module

public import Binary
public import Http.Http2.Wire

public section

namespace Http.Http2.Parser

open Binary

def paddedFlag : UInt8 := 0x08
def priorityFlag : UInt8 := 0x20
def ackFlag : UInt8 := 0x01

@[inline]
def getUInt24BE : Get Nat := do
  let b1 ← getThe UInt8
  let b2 ← getThe UInt8
  let b3 ← getThe UInt8
  return (b1.toNat <<< 16) + (b2.toNat <<< 8) + b3.toNat

@[inline]
def getUInt16BE : Get UInt16 := do
  let b1 ← getThe UInt8
  let b2 ← getThe UInt8
  let n := (b1.toNat <<< 8) + b2.toNat
  return UInt16.ofNat n

@[inline]
def getUInt32BE : Get UInt32 := do
  let b1 ← getThe UInt8
  let b2 ← getThe UInt8
  let b3 ← getThe UInt8
  let b4 ← getThe UInt8
  let n :=
    (UInt32.ofNat b1.toNat <<< 24) |||
    (UInt32.ofNat b2.toNat <<< 16) |||
    (UInt32.ofNat b3.toNat <<< 8) |||
    UInt32.ofNat b4.toNat
  return n

@[inline]
def getStreamId : Get StreamId := do
  let word ← getUInt32BE
  let masked := word &&& (0x7fffffff : UInt32)
  return masked.toNat

@[inline]
def getPriorityInfo : Get PriorityInfo := do
  let word ← getUInt32BE
  let exclusive := (word &&& (0x80000000 : UInt32)) != 0
  let dependency := (word &&& (0x7fffffff : UInt32)).toNat
  let weight ← getThe UInt8
  return { exclusive, streamDependency := dependency, weight := weight.toNat + 1 }

@[inline]
def expectLen (n : Nat) : Get Unit := do
  let rem ← remaining
  if rem == n then
    pure ()
  else
    throw (.userError s!"invalid payload length {rem}, expected {n}")

@[inline]
def expectNoExtra : Get Unit := do
  let rem ← remaining
  if rem == 0 then
    pure ()
  else
    throw (.userError s!"unexpected extra payload bytes: {rem}")

@[inline]
def takePaddedData : Option UInt8 → Get ByteArray := fun padLen? => do
  let rem ← remaining
  match padLen? with
  | none => get_bytes rem
  | some p =>
      let pad := p.toNat
      if pad > rem then
        throw (.userError s!"padding {pad} exceeds remaining {rem}")
      let dataLen := rem - pad
      let data ← get_bytes dataLen
      _ ← get_bytes pad
      return data

def decodeDataFrame (flags : UInt8) : Get FramePayload := do
  let padLen? ← if (flags &&& paddedFlag) != 0 then some <$> getThe UInt8 else pure none
  let data ← takePaddedData padLen?
  expectNoExtra
  return .data { padLength? := padLen?, data }

def decodeHeadersFrame (flags : UInt8) : Get FramePayload := do
  let padLen? ← if (flags &&& paddedFlag) != 0 then some <$> getThe UInt8 else pure none
  let priority? ← if (flags &&& priorityFlag) != 0 then some <$> getPriorityInfo else pure none
  let headerBlock ← takePaddedData padLen?
  expectNoExtra
  return .headers { padLength? := padLen?, priority?, headerBlock }

def decodePriorityFrame : Get FramePayload := do
  expectLen 5
  let info ← getPriorityInfo
  expectNoExtra
  return .priority { priority := info }

def decodeRstStreamFrame : Get FramePayload := do
  expectLen 4
  let err ← getUInt32BE
  expectNoExtra
  return .rstStream { errorCode := err }

def decodeSettingsFrame (flags : UInt8) : Get FramePayload := do
  let ack := (flags &&& ackFlag) != 0
  if ack then
    expectLen 0
    return .settings { ack := true, settings := #[] }
  else
    let rem ← remaining
    if rem % 6 != 0 then
      throw (.userError s!"invalid settings length {rem}")
    let mut settings : Array Setting := #[]
    repeat
      let more ← remaining
      if more == 0 then
        break
      let id ← getUInt16BE
      let value ← getUInt32BE
      settings := settings.push { identifier := id, value }
    expectNoExtra
    return .settings { ack := false, settings }

def decodePushPromiseFrame (flags : UInt8) : Get FramePayload := do
  let padLen? ← if (flags &&& paddedFlag) != 0 then some <$> getThe UInt8 else pure none
  let promised ← getStreamId
  let headerBlock ← takePaddedData padLen?
  expectNoExtra
  return .pushPromise { padLength? := padLen?, promisedStreamId := promised, headerBlock }

def decodePingFrame (flags : UInt8) : Get FramePayload := do
  expectLen 8
  let opaque_ ← get_bytes 8
  expectNoExtra
  return .ping { ack := (flags &&& ackFlag) != 0, opaque_ }

def decodeGoAwayFrame : Get FramePayload := do
  let rem ← remaining
  if rem < 8 then
    throw (.userError s!"goaway length too short {rem}")
  let lastId ← getStreamId
  let err ← getUInt32BE
  let debug ← get_bytes (rem - 8)
  expectNoExtra
  return .goaway { lastStreamId := lastId, errorCode := err, debugData := debug }

def decodeWindowUpdateFrame : Get FramePayload := do
  expectLen 4
  let word ← getUInt32BE
  let size := (word &&& (0x7fffffff : UInt32)).toNat
  expectNoExtra
  return .windowUpdate { windowSizeIncrement := size }

def decodeContinuationFrame : Get FramePayload := do
  let block ← get_bytes (← remaining)
  expectNoExtra
  return .continuation { headerBlock := block }

def decodePayload (header : FrameHeader) (payload : ByteArray) : Except DecodeError FramePayload :=
  match header.typ with
  | .unknown t => .ok (.unknown t payload)
  | .data => DecodeResult.toExcept <| (decodeDataFrame header.flags).run payload
  | .headers => DecodeResult.toExcept <| (decodeHeadersFrame header.flags).run payload
  | .priority => DecodeResult.toExcept <| decodePriorityFrame.run payload
  | .rstStream => DecodeResult.toExcept <| decodeRstStreamFrame.run payload
  | .settings => DecodeResult.toExcept <| (decodeSettingsFrame header.flags).run payload
  | .pushPromise => DecodeResult.toExcept <| (decodePushPromiseFrame header.flags).run payload
  | .ping => DecodeResult.toExcept <| (decodePingFrame header.flags).run payload
  | .goaway => DecodeResult.toExcept <| decodeGoAwayFrame.run payload
  | .windowUpdate => DecodeResult.toExcept <| decodeWindowUpdateFrame.run payload
  | .continuation => DecodeResult.toExcept <| decodeContinuationFrame.run payload

def frame_header : Get FrameHeader := do
  let length ← getUInt24BE
  let typByte ← getThe UInt8
  let flags ← getThe UInt8
  let streamId ← getStreamId
  return { length, typ := FrameType.ofByte typByte, flags, streamId }

def frame : Get Frame := do
  let header ← frame_header
  let payload ← get_bytes header.length
  match decodePayload header payload with
  | .ok parsed => return { header, payload := parsed }
  | .error err => throw err

def frame_bytes (bytes : ByteArray) : Except DecodeError Frame :=
  DecodeResult.toExcept <| frame.run bytes

end Http.Http2.Parser

end
