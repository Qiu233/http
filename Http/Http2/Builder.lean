module

public import Std
public import Binary
public import Http.Http2.Wire

public section

namespace Http.Http2.Builder

open Binary

def paddedFlag : UInt8 := 0x08
def priorityFlag : UInt8 := 0x20
def ackFlag : UInt8 := 0x01

@[inline]
def setFlag (flags : UInt8) (mask : UInt8) (on : Bool) : UInt8 :=
  if on then flags ||| mask else flags &&& (~~~mask)

@[inline]
def putUInt24BE (n : Nat) : Put := do
  let n32 := UInt32.ofNat n
  put (UInt8.ofNat ((n32 >>> 16).toNat))
  put (UInt8.ofNat ((n32 >>> 8).toNat))
  put (UInt8.ofNat n32.toNat)

@[inline]
def putUInt16BE (n : UInt16) : Put := do
  put (UInt8.ofNat ((n >>> 8).toNat))
  put (UInt8.ofNat n.toNat)

@[inline]
def putUInt32BE (n : UInt32) : Put := do
  put (UInt8.ofNat ((n >>> 24).toNat))
  put (UInt8.ofNat ((n >>> 16).toNat))
  put (UInt8.ofNat ((n >>> 8).toNat))
  put (UInt8.ofNat n.toNat)

@[inline]
def putStreamId (streamId : StreamId) : Put := do
  let masked := (UInt32.ofNat streamId) &&& (0x7fffffff : UInt32)
  putUInt32BE masked

@[inline]
def putPriorityInfo (info : PriorityInfo) : Put := do
  let dep := (UInt32.ofNat info.streamDependency) &&& (0x7fffffff : UInt32)
  let word := if info.exclusive then dep ||| (0x80000000 : UInt32) else dep
  putUInt32BE word
  let weight := if info.weight == 0 then 0 else info.weight - 1
  put (UInt8.ofNat weight)

@[inline]
def putZeros (n : Nat) : Put := do
  for _ in [0:n] do
    put (0 : UInt8)

def payloadPut : FramePayload → Put
  | .data f => do
      match f.padLength? with
      | none => put_bytes f.data
      | some p =>
          put p
          put_bytes f.data
          putZeros p.toNat
  | .headers f => do
      match f.padLength? with
      | none =>
          match f.priority? with
          | none => put_bytes f.headerBlock
          | some info =>
              putPriorityInfo info
              put_bytes f.headerBlock
      | some p =>
          put p
          match f.priority? with
          | none => pure ()
          | some info => putPriorityInfo info
          put_bytes f.headerBlock
          putZeros p.toNat
  | .priority f =>
      putPriorityInfo f.priority
  | .rstStream f =>
      putUInt32BE f.errorCode
  | .settings f => do
      if f.ack then
        pure ()
      else
        for s in f.settings do
          putUInt16BE s.identifier
          putUInt32BE s.value
  | .pushPromise f => do
      match f.padLength? with
      | none =>
          putStreamId f.promisedStreamId
          put_bytes f.headerBlock
      | some p =>
          put p
          putStreamId f.promisedStreamId
          put_bytes f.headerBlock
          putZeros p.toNat
  | .ping f =>
      put_bytes f.opaque_
  | .goaway f => do
      putStreamId f.lastStreamId
      putUInt32BE f.errorCode
      put_bytes f.debugData
  | .windowUpdate f => do
      let word := (UInt32.ofNat f.windowSizeIncrement) &&& (0x7fffffff : UInt32)
      putUInt32BE word
  | .continuation f =>
      put_bytes f.headerBlock
  | .unknown _ payload =>
      put_bytes payload

@[inline]
def payloadBytes (payload : FramePayload) : ByteArray :=
  Put.run (payloadPut payload)

@[inline]
def payloadType : FramePayload → FrameType
  | .data _ => .data
  | .headers _ => .headers
  | .priority _ => .priority
  | .rstStream _ => .rstStream
  | .settings _ => .settings
  | .pushPromise _ => .pushPromise
  | .ping _ => .ping
  | .goaway _ => .goaway
  | .windowUpdate _ => .windowUpdate
  | .continuation _ => .continuation
  | .unknown t _ => .unknown t

@[inline]
def payloadFlags (flags : UInt8) : FramePayload → UInt8
  | .data f =>
      setFlag flags paddedFlag f.padLength?.isSome
  | .headers f =>
      setFlag (setFlag flags paddedFlag f.padLength?.isSome) priorityFlag f.priority?.isSome
  | .settings f =>
      setFlag flags ackFlag f.ack
  | .ping f =>
      setFlag flags ackFlag f.ack
  | .pushPromise f =>
      setFlag flags paddedFlag f.padLength?.isSome
  | _ => flags

@[inline]
def headerPut (length : Nat) (typ : FrameType) (flags : UInt8) (streamId : StreamId) : Put := do
  putUInt24BE length
  put (FrameType.toByte typ)
  put flags
  putStreamId streamId

def framePut (frame : Frame) : Put := do
  let payload := payloadBytes frame.payload
  let flags := payloadFlags frame.header.flags frame.payload
  let typ := payloadType frame.payload
  headerPut payload.size typ flags frame.header.streamId
  put_bytes payload

@[inline]
def frameBytes (frame : Frame) : ByteArray :=
  Put.run (framePut frame)

end Http.Http2.Builder

end
