import Http.Client
import Http.Http2.Builder
import Http.Http2.Parser
import Http.HPack.Decode
import Http.HPack.Encode

open Http

namespace Http.Http2.Test

structure MockState where
  sentChunks : Array ByteArray := #[]
  recvChunks : Array ByteArray := #[]
  recvIx : Nat := 0
  shutdowns : Nat := 0

private def mkMockTransport (recvChunks : Array ByteArray) : IO (Transport × IO.Ref MockState) := do
  let state ← IO.mkRef { recvChunks := recvChunks }
  let transport : Transport :=
    { connect := fun _ => do
        let readBuffer ← IO.mkRef ByteArray.empty
        let conn : Transport.Connection :=
          { send := fun bytes => do
              state.modify fun s => { s with sentChunks := s.sentChunks.push bytes }
            recv? := fun _ => do
              let s ← state.get
              match s.recvChunks[s.recvIx]? with
              | some chunk =>
                  state.set { s with recvIx := s.recvIx + 1 }
                  pure (some chunk)
              | none =>
                  pure none
            shutdown := do
              state.modify fun s => { s with shutdowns := s.shutdowns + 1 }
            readBuffer := readBuffer }
        pure conn }
  pure (transport, state)

private def chunkBytes (bytes : ByteArray) (chunkSize : Nat) : Array ByteArray :=
  if chunkSize == 0 then
    #[bytes]
  else
    Id.run do
      let mut out : Array ByteArray := #[]
      let mut i := 0
      while i < bytes.size do
        let j := Nat.min bytes.size (i + chunkSize)
        out := out.push (bytes.extract i j)
        i := j
      out

private def frameBytes (frame : Http.Http2.Frame) : ByteArray :=
  Http.Http2.Builder.frameBytes frame

private def parseFrame? (bytes : ByteArray) : Option Http.Http2.Frame :=
  match Http.Http2.Parser.frame_bytes bytes with
  | .ok frame => some frame
  | .error _ => none

private def findHeaderValue? (headers : List Http.HPack.HeaderField) (name : String) : Option String :=
  let target := name.toUTF8
  let rec go (xs : List Http.HPack.HeaderField) : Option String :=
    match xs with
    | [] => none
    | x :: rest =>
        if x.name == target then
          String.fromUTF8? x.value
        else
          go rest
  go headers

private def statusHeadersBlock : ByteArray :=
  Http.HPack.encodeHeaderBlockBytes [{ name := ":status".toUTF8, value := "200".toUTF8 }]

private def mkServerSettingsFrame : Http.Http2.Frame :=
  { header := { length := 6, typ := .settings, flags := 0, streamId := 0 }
    payload := .settings { ack := false, settings := #[{ identifier := 0x0004, value := 65535 }] } }

private def mkHeadersFrame (headerBlock : ByteArray) (streamId : Nat := 1)
    (flags : UInt8 := 0x04) : Http.Http2.Frame :=
  { header := { length := headerBlock.size, typ := .headers, flags, streamId }
    payload := .headers { padLength? := none, priority? := none, headerBlock } }

private def mkContinuationFrame (headerBlock : ByteArray) (streamId : Nat := 1)
    (flags : UInt8 := 0x04) : Http.Http2.Frame :=
  { header := { length := headerBlock.size, typ := .continuation, flags, streamId }
    payload := .continuation { headerBlock } }

private def mkDataFrame (data : ByteArray) (streamId : Nat := 1)
    (flags : UInt8 := 0x01) : Http.Http2.Frame :=
  { header := { length := data.size, typ := .data, flags, streamId }
    payload := .data { padLength? := none, data } }

private def runHttp2GetWith (client : HttpClient) (path : String := "/") : IO (Except String Response) := do
  client.get path

private def decodeRequestHeaders? (bytes : ByteArray) : Option (List Http.HPack.HeaderField) := do
  let frame ← parseFrame? bytes
  match frame.payload with
  | .headers f =>
      match Http.HPack.decodeHeaderBlockBytes f.headerBlock with
      | .ok (headers, _) => some headers
      | .error _ => none
  | _ => none

def testHttp2ClientRoundtripAndFrames : IO Bool := do
  let serverBytes :=
    frameBytes mkServerSettingsFrame ++
    frameBytes (mkHeadersFrame statusHeadersBlock 1 0x04) ++
    frameBytes (mkDataFrame "ok".toUTF8 1 0x01)
  let (transport, state) ← mkMockTransport #[serverBytes]
  let client : HttpClient :=
    { host := "localhost", port := 8443, scheme := "http", protocol := .http2, transport := transport }
  let res ← runHttp2GetWith client "/"
  let s ← state.get
  let responseOk :=
    match res with
    | .ok r => r.status == 200 && r.body? == some "ok".toUTF8
    | .error _ => false
  let prefaceOk := s.sentChunks[0]? == some Http.Http2.connectionPreface
  let settingsOk :=
    match s.sentChunks[1]? >>= parseFrame? with
    | some f =>
        f.header.typ == .settings &&
        match f.payload with
        | .settings sf => !sf.ack
        | _ => false
    | none => false
  let headersOk :=
    match s.sentChunks[2]? >>= decodeRequestHeaders? with
    | some hs =>
        findHeaderValue? hs ":method" == some "GET" &&
        findHeaderValue? hs ":path" == some "/" &&
        findHeaderValue? hs ":scheme" == some "http" &&
        findHeaderValue? hs ":authority" == some "localhost:8443"
    | none => false
  let settingsAckOk :=
    match s.sentChunks[3]? >>= parseFrame? with
    | some f =>
        f.header.typ == .settings &&
        match f.payload with
        | .settings sf => sf.ack
        | _ => false
    | none => false
  let connWinOk :=
    match s.sentChunks[4]? >>= parseFrame? with
    | some f =>
        f.header.typ == .windowUpdate && f.header.streamId == 0 &&
        match f.payload with
        | .windowUpdate wu => wu.windowSizeIncrement == 2
        | _ => false
    | none => false
  let streamWinOk :=
    match s.sentChunks[5]? >>= parseFrame? with
    | some f =>
        f.header.typ == .windowUpdate && f.header.streamId == 1 &&
        match f.payload with
        | .windowUpdate wu => wu.windowSizeIncrement == 2
        | _ => false
    | none => false
  pure <| responseOk && prefaceOk && settingsOk && headersOk && settingsAckOk && connWinOk && streamWinOk && s.shutdowns == 1

def testHttp2FragmentedReadsWithContinuation : IO Bool := do
  let hb := statusHeadersBlock
  let split := hb.size / 2
  let hb1 := hb.extract 0 split
  let hb2 := hb.extract split hb.size
  let serverBytes :=
    frameBytes mkServerSettingsFrame ++
    frameBytes (mkHeadersFrame hb1 1 0x00) ++
    frameBytes (mkContinuationFrame hb2 1 0x04) ++
    frameBytes (mkDataFrame "hello".toUTF8 1 0x01)
  let chunks := chunkBytes serverBytes 1
  let (transport, state) ← mkMockTransport chunks
  let client : HttpClient :=
    { host := "localhost", port := 8443, scheme := "https", protocol := .http2, transport := transport }
  let res ← runHttp2GetWith client "/x"
  let s ← state.get
  let responseOk :=
    match res with
    | .ok r => r.status == 200 && r.body? == some "hello".toUTF8
    | .error _ => false
  let headersOk :=
    match s.sentChunks[2]? >>= decodeRequestHeaders? with
    | some hs => findHeaderValue? hs ":scheme" == some "https"
    | none => false
  pure <| responseOk && headersOk && s.shutdowns == 1

def testHttp2Http1ReplyErrorHint : IO Bool := do
  let badReply := "HTTP/1.1 400".toUTF8
  let (transport, state) ← mkMockTransport #[badReply]
  let client : HttpClient :=
    { host := "localhost", port := 8443, scheme := "https", protocol := .http2, transport := transport }
  let res ← runHttp2GetWith client "/"
  let s ← state.get
  let msgOk :=
    match res with
    | .ok _ => false
    | .error msg => msg.contains "ALPN"
  pure (msgOk && s.shutdowns == 1)

#eval testHttp2ClientRoundtripAndFrames
#eval testHttp2FragmentedReadsWithContinuation
#eval testHttp2Http1ReplyErrorHint

end Http.Http2.Test
