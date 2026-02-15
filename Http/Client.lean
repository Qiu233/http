module

public import Http.Surface
public import Http.Connection
public import Binary -- TODO: why? Without this will causes downstream importers `invalid environment extension, 'Binary.Deriving.binEnumAttr' has already been used`
import Http.Http1_1.Builder
import Http.Http1_1.Parser
import Http.Http1_1.Semantic
import Http.Http2.Builder
import Http.Http2.Parser
import Http.HPack.Decode

namespace Http

open Std.Internal
open IO.Async
open TCP
open Std.Net

public structure Transport.Connection where
  send : ByteArray → Async Unit
  /-- Contract: return `Option.none` exactly when the peer closed connection. -/
  recv? : UInt64 → Async (Option ByteArray)
  shutdown : Async Unit
  -- TODO: we need a ring buffer
  readBuffer : IO.Ref ByteArray

private def throwEOF [MonadExceptOf IO.Error m] : m α := throw IO.Error.unexpectedEof

@[noinline]
protected def Transport.Connection.readToBuffer (conn : Transport.Connection) (n : UInt64) : Async Unit := do
  let t ← unsafe conn.readBuffer.take
  let some data ← conn.recv? n | throwEOF
  conn.readBuffer.set (t ++ data)

public structure Transport where
  connect : SocketAddress → Async (Transport.Connection)

public def Transport.tcp : Transport :=
  { connect := fun addr => do
      let sock ← Socket.Client.mk
      sock.connect addr
      let conn : Transport.Connection :=
        { send := fun bytes => sock.send bytes
          recv? := sock.recv?
          shutdown := sock.shutdown
          readBuffer := ← IO.mkRef {} }
      return conn
  }

instance : Inhabited Transport where
  default := Transport.tcp

instance : Repr Transport where
  reprPrec _ _ := "<transport>"

public structure HttpClient where
  public mk' ::
  host : String
  port : UInt16 := 80
  protocol : Http.Connection.Protocol := .http1_1
  defaultHeaders : Headers := #[]
  transport : Transport := Transport.tcp
deriving Repr

@[always_inline]
public def HttpClient.mkTCP (host : String) (port : UInt16 := 80)
    (protocol : Http.Connection.Protocol := .http1_1) : HttpClient :=
  { host, port, protocol, transport := Transport.tcp }

@[always_inline]
def header (name value : String) : Header :=
  { name, value }

@[inline]
def ensureHeader (headers : Headers) (name value : String) : Headers :=
  if (findHeader? headers name).isSome then
    headers
  else
    headers.push (header name value)

@[inline]
def applyDefaultHeaders (headers defaults : Headers) : Headers :=
  defaults.foldl (init := headers) fun acc h =>
    if (findHeader? acc h.name).isSome then acc else acc.push h

@[inline]
def hostHeaderValue (host : String) (port : UInt16) : String :=
  if port == 80 then host else s!"{host}:{port}"

@[inline]
def contentLengthHeader? (body? : Option ByteArray) : Option Header :=
  match body? with
  | none => none
  | some body => some (header "Content-Length" (toString body.size))

def prepareRequest (client : HttpClient) (req : Request) : Request :=
  let headers := applyDefaultHeaders req.headers client.defaultHeaders
  let headers := ensureHeader headers "Host" (hostHeaderValue client.host client.port)
  let headers := ensureHeader headers "Connection" "close"
  let headers :=
    match contentLengthHeader? req.body? with
    | none => headers
    | some h => ensureHeader headers h.name h.value
  { req with headers }

def responseFromHttp1 [Monad m] [MonadExceptOf String m] (msg : Http.Http1_1.HttpMessage) : m Response :=
  match msg.header.start_line with
  | .status line =>
    let headers :=
      msg.header.fields.map fun f =>
        { name := f.name, value := Http.Http1_1.Builder.fieldValueString f.value }
    let body? := msg.body?.map fun xs =>
      match xs with
      | .bytes bs => bs
      | .chunked cb => cb.chunks.foldl (init := ({} : ByteArray)) (fun acc x => acc ++ x.data)
    return { status := line.status_code, reason? := line.reason?, headers, body? }
  | .request _ =>
    throw "expected HTTP response, got request"

def resolveAddress (host : String) (port : UInt16) : Async SocketAddress := do
  match IPv4Addr.ofString host with
  | some ip4 =>
    return (SocketAddress.v4 (SocketAddressV4.mk ip4 port))
  | none =>
    match IPv6Addr.ofString host with
    | some ip6 =>
      return (SocketAddress.v6 (SocketAddressV6.mk ip6 port))
    | none =>
      let addrs ← Std.Internal.IO.Async.DNS.getAddrInfo host (toString port)
      match addrs[0]? with
      | some (IPAddr.v4 ip) => return (SocketAddress.v4 (SocketAddressV4.mk ip port))
      | some (IPAddr.v6 ip) => return (SocketAddress.v6 (SocketAddressV6.mk ip port))
      | none => throw (IO.userError s!"no DNS addresses for {host}")

open Binary in
private def bufferedGet (conn : Transport.Connection) (x : Get α) (errMsg : String) : ExceptT String Async α := do
  let mut decoder := (pending x).run (← unsafe conn.readBuffer.take)
  while (decoder matches .pending ..) do
    let some data ← conn.recv? 4096 | throwEOF
    decoder := decoder.feed data
  if let DecodeResult.error err _ := decoder then
    throw s!"{decl_name%}: {errMsg}: {err}"
  let DecodeResult.success r kont := decoder | unreachable!
  let kontBytes := kont.data.extract kont.offset (kont.data.size)
  conn.readBuffer.set kontBytes
  return r

open Binary in
private def readToEnd (conn : Transport.Connection) (errMsg : String) : ExceptT String Async ByteArray := do
  let mut decoder := (pending exhaust).run (← unsafe conn.readBuffer.take)
  while (decoder matches .pending ..) do
    let some data ← conn.recv? 4096 | break
    decoder := decoder.feed data
  decoder := decoder.terminate -- terminate the pending state
  if let DecodeResult.error err _ := decoder then
    throw s!"{decl_name%}: {errMsg}: {err}"
  let DecodeResult.success r kont := decoder | unreachable!
  let kontBytes := kont.data.extract kont.offset (kont.data.size)
  assert! kontBytes.isEmpty
  conn.readBuffer.set kontBytes
  return r

open Binary in
/--
Return `Option.none` in two cases:
* `Content-Length` is `0`
* `Content-Length` is absent and `Transfer-Encoding` has no `chunked`
-/
def recvHttp1Body? (conn : Transport.Connection) (header : Http1_1.HttpMessageHeader)
    : ExceptT String Async (Option Http1_1.HttpMessageBody) := do
  let content_length? ← match header.content_length? with
    | .error e => throw s!"failed to decode content-length: {e}"
    | .ok r => pure r
  match content_length? with
  | some len =>
    if len == 0 then
      pure none
    else
      (some ∘ Http1_1.HttpMessageBody.bytes) <$> bufferedGet conn (get_bytes len) "failed to parse HTTP/1.1 body"
  | none =>
    let is_chunked ← match header.is_chunked with
      | .error e => throw s!"failed to decode transfer-encoding: {e}"
      | .ok r => pure r
    if is_chunked then
      let cbody ← bufferedGet conn Http1_1.Parser.chunked_body "failed to parse HTTP/1.1 body"
      pure (some (Http1_1.HttpMessageBody.chunked cbody))
    else
      -- important note: it must holds that `pending exhaust ≡ exhaust` in behavior
      let rem ← readToEnd conn "failed to fetch HTTP/1.1 body"
      if rem.size == 0 then
        pure none
      else
        pure (some (Http1_1.HttpMessageBody.bytes rem))


/-!
## Client side receiving
* If `Content-Length` is present, read as much as it specifies.
* Else if status/method implies no body (HEAD, 1xx, 204, 304) → body = empty, stop at end of headers.
* Else if Transfer-Encoding: chunked → chunk decode until terminator, then optional trailers.
* Else if Transfer-Encoding exists but not properly chunk-framed → read until connection close.
* Else (no TE, no CL) → read until connection close.
-/

open Binary in
def recvHttp1 (conn : Transport.Connection) (req_head : Bool) : ExceptT String Async Response := do
  let header ← bufferedGet conn Http1_1.Parser.http_message_header "failed to parse HTTP/1.1 header"
  if req_head then
    return ← responseFromHttp1 { header, body? := none }
  let Http1_1.StartLine.status statusLine := header.start_line
    | throw "internal error: start line of HTTP/1.1 response is not a status line"
  let status := ToString.toString statusLine.status_code
  if let ['1', _, _] := status.toList then -- 1xx (informational) should have no body
    return ← responseFromHttp1 { header, body? := none }
  if status matches "204" | "304" then -- `204 No Content`, `304 Not Modified`
    return ← responseFromHttp1 { header, body? := none }
  let body? ← recvHttp1Body? conn header
  if status == "205" then -- `205 Reset Content`
    if let some (.chunked chunked) := body? then
      if chunked.chunks.size > 0 then
        throw "HTTP/1.1 response 205 unexpectedly contains body bytes"
  responseFromHttp1 { header, body? }

def sendHttp1 (client : HttpClient) (req : Request) : ExceptT String Async Response := do
  let addr ← resolveAddress client.host client.port
  let conn ← client.transport.connect addr
  try
    let req := prepareRequest client req
    conn.send (requestToHttp1Bytes req)
    recvHttp1 conn (req.method == "HEAD")
  finally
    conn.shutdown

def prepareRequestH2 (client : HttpClient) (req : Request) : Request :=
  let headers := applyDefaultHeaders req.headers client.defaultHeaders
  let headers := ensureHeader headers "Host" (hostHeaderValue client.host client.port)
  let headers :=
    match contentLengthHeader? req.body? with
    | none => headers
    | some h => ensureHeader headers h.name h.value
  { req with headers }

def decodeHeaderBlockFrom [Monad m] [MonadExceptOf String m] (t : Http.HPack.DynamicTable) (bytes : ByteArray) :
    m (List Http.HPack.HeaderField × Http.HPack.DynamicTable) :=
  match Binary.DecodeResult.toExcept <| (Http.HPack.decodeHeaderBlockAux t).run bytes with
  | .ok res => return res
  | .error err => throw s!"{err}"

def frameLength (header : ByteArray) : Option Nat := do
  let b0 ← header[0]?
  let b1 ← header[1]?
  let b2 ← header[2]?
  return (b0.toNat <<< 16) + (b1.toNat <<< 8) + b2.toNat

def recvExact (conn : Transport.Connection) (n : UInt64) : ExceptT String Async ByteArray := do
  let size ← ByteArray.size <$> conn.readBuffer.get
  if size < n.toNat then
    conn.readToBuffer n
  let t ← unsafe conn.readBuffer.take
  let head := t.extract 0 n.toNat
  let tail := t.extract n.toNat (t.size)
  conn.readBuffer.set tail
  return head

def recvFrame (conn : Transport.Connection) : ExceptT String Async Http.Http2.Frame := do
  let header ← recvExact conn 9
  let some len := frameLength header | throw "failed to decode frame length"
  assert! (len < (2 ^ 64 - 1 : Nat))
  let payload ← recvExact conn (UInt64.ofNat len)
  let bytes := header.append payload
  match Http.Http2.Parser.frame_bytes bytes with
  | .ok frame => return frame
  | .error err => throw s!"{err}"

def h2EndStreamFlag : UInt8 := 0x01
def h2EndHeadersFlag : UInt8 := 0x04

def statusFromHeaders [Monad m] [MonadExceptOf String m] (headers : List Http.HPack.HeaderField) : m Nat := do
  let h ← headers.find? (fun h => h.name == ":status".toUTF8) |>.getDM (throw "missing :status pseudo-header")
  let some s := String.fromUTF8? h.value | throw "invalid :status value"
  s.toNat?.getDM (throw s!"invalid :status {s}")

def headersFromHpack [Monad m] [MonadExceptOf String m] (headers : List Http.HPack.HeaderField) : m Headers :=
  headers.foldlM (init := #[]) fun acc h => do
    let some name := String.fromUTF8? h.name | throw "invalid header name"
    if name.startsWith ":" then
      pure acc
    else
      let some value := String.fromUTF8? h.value | throw "invalid header value"
      pure <| acc.push { name, value }

def readHttp2Response (conn : Transport.Connection) (streamId : Http.Http2.StreamId) :
    ExceptT String Async Response := do
  let mut headerBlock := ByteArray.empty
  let mut headers? : Option Headers := none
  let mut status? : Option Nat := none
  let mut table := Http.HPack.DynamicTable.empty
  let mut body := ByteArray.empty
  let mut done := false
  while !done do
    let frame ← recvFrame conn
    match frame.payload with
    | .settings f =>
      if !f.ack then
        let ackFrame : Http.Http2.Frame :=
          { header := { length := 0, typ := .settings, flags := 0, streamId := 0 }
            payload := .settings { ack := true, settings := #[] } }
        conn.send (Http.Http2.Builder.frameBytes ackFrame)
    | _ => pure ()
    if frame.header.streamId != streamId then
      continue
    match frame.payload with
    | .headers f =>
      headerBlock := headerBlock.append f.headerBlock
      if (frame.header.flags &&& h2EndHeadersFlag) != 0 then
        let (hs, t') ← decodeHeaderBlockFrom table headerBlock
        table := t'
        status? ← some <$> statusFromHeaders hs
        headers? ← some <$> headersFromHpack hs
        headerBlock := ByteArray.empty
      if (frame.header.flags &&& h2EndStreamFlag) != 0 then
        done := true
    | .continuation f =>
      headerBlock := headerBlock.append f.headerBlock
      if (frame.header.flags &&& h2EndHeadersFlag) != 0 then
        let (hs, t') ← decodeHeaderBlockFrom table headerBlock
        table := t'
        status? ← some <$> statusFromHeaders hs
        headers? ← some <$> headersFromHpack hs
        headerBlock := ByteArray.empty
    | .data f =>
      body := body.append f.data
      if (frame.header.flags &&& h2EndStreamFlag) != 0 then
        done := true
    | _ => pure ()
  match status?, headers? with
  | some status, some headers =>
    return { status, headers, body? := some body }
  | _, _ =>
    throw "missing response headers"

def sendHttp2 (client : HttpClient) (req : Request) : ExceptT String Async Response := do
  let addr ← resolveAddress client.host client.port
  let conn ← client.transport.connect addr
  try
    conn.send Http.Http2.connectionPreface
    let settingsFrame : Http.Http2.Frame :=
      { header := { length := 0, typ := .settings, flags := 0, streamId := 0 }
        payload := .settings { ack := false, settings := #[] } }
    conn.send (Http.Http2.Builder.frameBytes settingsFrame)
    let req := prepareRequestH2 client req
    let ctx : RequestH2Context :=
      { streamId := 1
        scheme? := some "http"
        authority? := some (hostHeaderValue client.host client.port) }
    for frame in requestToHttp2Frames req ctx do
      conn.send (Http.Http2.Builder.frameBytes frame)
    readHttp2Response conn 1
  finally
    conn.shutdown

public def HttpClient.sendAsync (client : HttpClient) (req : Request) :
    Async (Except String Response) :=
  match client.protocol with
  | .http1_1 => sendHttp1 client req
  | .http2 => sendHttp2 client req
  | .unknown => return .error "unknown protocol"

public def HttpClient.send (client : HttpClient) (req : Request) :
    IO (Except String Response) :=
  (client.sendAsync req).wait

public def HttpClient.postAsync (client : HttpClient) (request_target : String) (body : ByteArray)
    (headers : Headers := #[]) : Async (Except String Response) := show ExceptT String Async Response from do
  let target ← RequestTarget.parse? request_target
    |>.mapError fun e => s!"invalid request-target: {e}\n{request_target}"
  let req : Request := { method := "POST", target, headers, body? := some body }
  client.sendAsync req

public def HttpClient.post (client : HttpClient) (request_target : String) (body : ByteArray)
    (headers : Headers := #[]) : IO (Except String Response) :=
  (client.postAsync request_target body headers).wait

public def HttpClient.getAsync (client : HttpClient) (request_target : String) (headers : Headers := #[]) :
    Async (Except String Response) := show ExceptT String Async Response from do
  let target ← RequestTarget.parse? request_target
    |>.mapError fun e => s!"invalid request-target: {e}\n{request_target}"
  let req : Request := { method := "GET", target, headers }
  client.sendAsync req

public def HttpClient.get (client : HttpClient) (request_target : String) (headers : Headers := #[]) :
    IO (Except String Response) :=
  (client.getAsync request_target headers).wait

end Http
