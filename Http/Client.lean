module

public import Http.Surface
public import Http.Connection
import Http.Http1_1.Builder
import Http.Http1_1.Parser
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
  recv? : UInt64 → Async (Option ByteArray)
  shutdown : Async Unit

public structure Transport where
  connect : SocketAddress → Async (Except String Transport.Connection)

public def Transport.tcp : Transport :=
  { connect := fun addr => do
      let sock ← Socket.Client.mk
      try
        sock.connect addr
        let conn : Transport.Connection :=
          { send := fun bytes => sock.send bytes
            recv? := fun n => sock.recv? n
            shutdown := sock.shutdown }
        return .ok conn
      catch e =>
        return .error e.toString }

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

def responseFromHttp1 (msg : Http.Http1_1.HttpMessage) : Except String Response :=
  match msg.start_line with
  | .status line =>
      let headers :=
        msg.fields.map fun f =>
          { name := f.name, value := Http.Http1_1.Builder.fieldValueString f.value }
      let body? := msg.body?.map String.toUTF8
      .ok { status := line.status_code, reason? := line.reason?, headers, body? }
  | .request _ =>
      .error "expected HTTP response, got request"

def resolveAddress (host : String) (port : UInt16) : Async (Except String SocketAddress) := do
  match IPv4Addr.ofString host with
  | some ip4 =>
      return .ok (SocketAddress.v4 (SocketAddressV4.mk ip4 port))
  | none =>
      match IPv6Addr.ofString host with
      | some ip6 =>
          return .ok (SocketAddress.v6 (SocketAddressV6.mk ip6 port))
      | none =>
          let addrs ← Std.Internal.IO.Async.DNS.getAddrInfo host (toString port)
          match addrs[0]? with
          | some (IPAddr.v4 ip) => return .ok (SocketAddress.v4 (SocketAddressV4.mk ip port))
          | some (IPAddr.v6 ip) => return .ok (SocketAddress.v6 (SocketAddressV6.mk ip port))
          | none => return .error s!"no DNS addresses for {host}"

open PolyParsec.Std in
def sendHttp1 (client : HttpClient) (req : Request) : Async (Except String Response) := do
  let addrResult ← resolveAddress client.host client.port
  let addr ←
    match addrResult with
    | .ok addr => pure addr
    | .error err => return .error err
  let connResult ← client.transport.connect addr
  match connResult with
  | .error err => return .error err
  | .ok conn =>
      try
        let req := prepareRequest client req
        conn.send (requestToHttp1String req).toUTF8
        let mut resp := ByteArray.empty
        repeat
          let some data ← conn.recv? 4096 | break
          resp := resp.append data
        let some respStr := String.fromUTF8? resp | return .error "invalid HTTP/1.1 response bytes"
        let parsed := (Http.Http1_1.Parser.http_message (m := Std.Internal.Parsec.String.Parser)).run respStr
        match parsed with
        | .ok msg => return responseFromHttp1 msg
        | .error err => return .error s!"failed to parse HTTP/1.1 response: {err}\n{respStr}"
      catch e =>
        return .error e.toString
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

def decodeHeaderBlockFrom (t : Http.HPack.DynamicTable) (bytes : ByteArray) :
    Except String (List Http.HPack.HeaderField × Http.HPack.DynamicTable) :=
  match Binary.DecodeResult.toExcept <| (Http.HPack.decodeHeaderBlockAux t).run bytes with
  | .ok res => .ok res
  | .error err => .error s!"{err}"

def frameLength (header : ByteArray) : Option Nat := do
  let b0 ← header[0]?
  let b1 ← header[1]?
  let b2 ← header[2]?
  return (b0.toNat <<< 16) + (b1.toNat <<< 8) + b2.toNat

def recvExact (conn : Transport.Connection) (n : Nat) : Async (Except String ByteArray) := do
  let mut out := ByteArray.empty
  let mut remaining := n
  while remaining > 0 do
    let chunk? ← conn.recv? remaining.toUInt64
    match chunk? with
    | none => return .error "unexpected EOF"
    | some chunk =>
        out := out.append chunk
        remaining := n - out.size
  return .ok out

def recvFrame (conn : Transport.Connection) : Async (Except String Http.Http2.Frame) := do
  let headerRes ← recvExact conn 9
  match headerRes with
  | .error err => return .error err
  | .ok header =>
      let some len := frameLength header | return .error "failed to decode frame length"
      let payloadRes ← recvExact conn len
      match payloadRes with
      | .error err => return .error err
      | .ok payload =>
          let bytes := header.append payload
          match Http.Http2.Parser.frame_bytes bytes with
          | .ok frame => return .ok frame
          | .error err => return .error s!"{err}"

def h2EndStreamFlag : UInt8 := 0x01
def h2EndHeadersFlag : UInt8 := 0x04

def statusFromHeaders (headers : List Http.HPack.HeaderField) : Except String Nat := do
  match headers.find? (fun h => h.name == ":status".toUTF8) with
  | none => .error "missing :status pseudo-header"
  | some h =>
      let some s := String.fromUTF8? h.value | throw "invalid :status value"
      match s.toNat? with
      | some n => .ok n
      | none => .error s!"invalid :status {s}"

def headersFromHpack (headers : List Http.HPack.HeaderField) : Except String Headers :=
  headers.foldlM (init := #[]) fun acc h => do
    let some name := String.fromUTF8? h.name | throw "invalid header name"
    if name.startsWith ":" then
      pure acc
    else
      let some value := String.fromUTF8? h.value | throw "invalid header value"
      pure <| acc.push { name, value }

def readHttp2Response (conn : Transport.Connection) (streamId : Http.Http2.StreamId) :
    Async (Except String Response) := do
  let mut headerBlock := ByteArray.empty
  let mut headers? : Option Headers := none
  let mut status? : Option Nat := none
  let mut table := Http.HPack.DynamicTable.empty
  let mut body := ByteArray.empty
  let mut done := false
  while !done do
    let frameRes ← recvFrame conn
    let frame ←
      match frameRes with
      | .ok f => pure f
      | .error err => return .error err
    match frame.payload with
    | .settings f =>
        if !f.ack then
          let ackFrame : Http.Http2.Frame :=
            { header := { length := 0, typ := .settings, flags := 0, streamId := 0 }
              payload := .settings { ack := true, settings := #[] } }
          conn.send (Http.Http2.Builder.frameBytes ackFrame)
        pure ()
    | _ => pure ()
    if frame.header.streamId != streamId then
      continue
    match frame.payload with
    | .headers f =>
        headerBlock := headerBlock.append f.headerBlock
        if (frame.header.flags &&& h2EndHeadersFlag) != 0 then
          match decodeHeaderBlockFrom table headerBlock with
          | .error err => return .error err
          | .ok (hs, t') =>
              table := t'
              match statusFromHeaders hs with
              | .ok n => status? := some n
              | .error err => return .error err
              headers? ← match headersFromHpack hs with
                | .error e => return .error e
                | .ok r => pure (some r)
          headerBlock := ByteArray.empty
        if (frame.header.flags &&& h2EndStreamFlag) != 0 then
          done := true
    | .continuation f =>
        headerBlock := headerBlock.append f.headerBlock
        if (frame.header.flags &&& h2EndHeadersFlag) != 0 then
          match decodeHeaderBlockFrom table headerBlock with
          | .error err => return .error err
          | .ok (hs, t') =>
              table := t'
              match statusFromHeaders hs with
              | .ok n => status? := some n
              | .error err => return .error err
              headers? ← match headersFromHpack hs with
                | .error e => return .error e
                | .ok r => pure (some r)
          headerBlock := ByteArray.empty
    | .data f =>
        body := body.append f.data
        if (frame.header.flags &&& h2EndStreamFlag) != 0 then
          done := true
    | _ => pure ()
  match status?, headers? with
  | some status, some headers =>
      return .ok { status, headers, body? := some body }
  | _, _ =>
      return .error "missing response headers"

def sendHttp2 (client : HttpClient) (req : Request) : Async (Except String Response) := do
  let addrResult ← resolveAddress client.host client.port
  let addr ←
    match addrResult with
    | .ok addr => pure addr
    | .error err => return .error err
  let connResult ← client.transport.connect addr
  match connResult with
  | .error err => return .error err
  | .ok conn =>
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
      catch e =>
        return .error e.toString
      finally
        conn.shutdown

public def HttpClient.sendAsync (client : HttpClient) (req : Request) :
    Async (Except String Response) :=
  match client.protocol with
  | .http1_1 => sendHttp1 client req
  | .http2 => sendHttp2 client req
  | .unknown => pure (.error "unknown protocol")

public def HttpClient.send (client : HttpClient) (req : Request) :
    IO (Except String Response) :=
  (client.sendAsync req).wait

public def HttpClient.postAsync (client : HttpClient) (request_target : String) (body : ByteArray)
    (headers : Headers := #[]) : Async (Except String Response) := do
  let target ← match RequestTarget.parse? request_target with
    | .error e => return .error s!"invalid request-target: {e}\n{request_target}"
    | .ok r => pure r
  let req : Request := { method := "POST", target, headers, body? := some body }
  client.sendAsync req

public def HttpClient.post (client : HttpClient) (request_target : String) (body : ByteArray)
    (headers : Headers := #[]) : IO (Except String Response) :=
  (client.postAsync request_target body headers).wait

public def HttpClient.getAsync (client : HttpClient) (request_target : String) (headers : Headers := #[]) :
    Async (Except String Response) := do
  let target ← match RequestTarget.parse? request_target with
    | .error e => return .error s!"invalid request-target: {e}\n{request_target}"
    | .ok r => pure r
  let req : Request := { method := "GET", target, headers }
  client.sendAsync req

public def HttpClient.get (client : HttpClient) (request_target : String) (headers : Headers := #[]) :
    IO (Except String Response) :=
  (client.getAsync request_target headers).wait

end Http
