module

public import Std
public import Http.Http1_1.Builder
public import Http.Http2.Wire
public import Http.HPack.Encode

public section

namespace Http

structure Header where
  name : String
  value : String
deriving Inhabited, Repr

abbrev Headers := Array Header

inductive RequestTarget where
  | origin (path : String) (query? : Option String)
  | absolute (absUri : Uri)
  | authority (auth : Uri.Authority)
  | asterisk
deriving Inhabited

structure Request where
  method : String
  target : RequestTarget
  headers : Headers
  body? : Option ByteArray := none
deriving Inhabited

structure Response where
  status : Nat
  reason? : Option String := none
  headers : Headers
  body? : Option ByteArray := none
deriving Inhabited

@[inline]
def requestTargetToHttp1 : RequestTarget → Http.Http1_1.RequestTarget
  | .origin path query? => .origin path query?
  | .absolute uri => .absolute uri
  | .authority auth => .authority auth
  | .asterisk => .asterisk

@[inline]
def headerToFieldLine (h : Header) : Http.Http1_1.FieldLine :=
  { name := h.name, value := #[h.value] }

@[inline]
def bodyToString? (body? : Option ByteArray) : Option String :=
  -- HTTP/1.1 builders are String-based, so we assume UTF-8 for now.
  body?.map String.fromUTF8!

@[inline]
def requestToHttp1 (req : Request) : Http.Http1_1.HttpMessage :=
  { start_line := .request
      { method := req.method
        request_target := requestTargetToHttp1 req.target
        version := { major := 1, minor := 1 } }
    fields := req.headers.map headerToFieldLine
    body? := bodyToString? req.body? }

@[inline]
def responseToHttp1 (resp : Response) : Http.Http1_1.HttpMessage :=
  { start_line := .status
      { version := { major := 1, minor := 1 }
        status_code := resp.status
        reason? := resp.reason? }
    fields := resp.headers.map headerToFieldLine
    body? := bodyToString? resp.body? }

@[inline]
def requestToHttp1String (req : Request) : String :=
  Http.Http1_1.Builder.httpMessageString (requestToHttp1 req)

@[inline]
def responseToHttp1String (resp : Response) : String :=
  Http.Http1_1.Builder.httpMessageString (responseToHttp1 resp)

@[inline]
def requestTargetPath (target : RequestTarget) : String :=
  match target with
  | .origin path query? =>
      match query? with
      | none => path
      | some q => path ++ "?" ++ q
  | .absolute uri =>
      match uri.query? with
      | none => uri.path
      | some q => uri.path ++ "?" ++ q
  | .authority auth => toString auth
  | .asterisk => "*"

@[inline]
def statusCodeString (code : Nat) : String :=
  if code < 10 then s!"00{code}"
  else if code < 100 then s!"0{code}"
  else toString code

@[inline]
def headerField (name value : String) : Http.HPack.HeaderField :=
  { name := name.toUTF8, value := value.toUTF8 }

@[inline]
def hpackHeaders (headers : Headers) : List Http.HPack.HeaderField :=
  headers.toList.map (fun h => headerField h.name.toLower h.value)

@[inline]
def findHeader? (headers : Headers) (name : String) : Option String :=
  let target := name.toLower
  Id.run do
    let mut out : Option String := none
    for h in headers do
      if out.isNone && h.name.toLower == target then
        out := some h.value
    return out

@[inline]
def requestScheme? (req : Request) : Option String :=
  match req.target with
  | .absolute uri => uri.scheme?
  | _ => none

@[inline]
def requestAuthority? (req : Request) : Option String :=
  match req.target with
  | .absolute uri =>
      match uri.authority? with
      | some a => some (toString a)
      | none => none
  | .authority auth => some (toString auth)
  | _ => findHeader? req.headers "host"

structure RequestH2Context where
  streamId : Http.Http2.StreamId := 1
  scheme? : Option String := none
  authority? : Option String := none
deriving Inhabited, Repr

structure ResponseH2Context where
  streamId : Http.Http2.StreamId := 1
deriving Inhabited, Repr

def requestPseudoHeaders (req : Request) (ctx : RequestH2Context) :
    List Http.HPack.HeaderField :=
  Id.run do
    let mut out : List Http.HPack.HeaderField := [headerField ":method" req.method]
    match ctx.scheme? with
    | some s => out := out ++ [headerField ":scheme" s]
    | none =>
        match requestScheme? req with
        | some s => out := out ++ [headerField ":scheme" s]
        | none => pure ()
    match ctx.authority? with
    | some a => out := out ++ [headerField ":authority" a]
    | none =>
        match requestAuthority? req with
        | some a => out := out ++ [headerField ":authority" a]
        | none => pure ()
    out := out ++ [headerField ":path" (requestTargetPath req.target)]
    return out

def responsePseudoHeaders (resp : Response) : List Http.HPack.HeaderField :=
  [headerField ":status" (statusCodeString resp.status)]

def endStreamFlag : UInt8 := 0x01
def endHeadersFlag : UInt8 := 0x04

@[inline]
def hasBodyData (body? : Option ByteArray) : Bool :=
  match body? with
  | none => false
  | some b => b.size > 0

def makeHeadersFrame (streamId : Http.Http2.StreamId) (headerBlock : ByteArray)
    (endStream : Bool) : Http.Http2.Frame :=
  let baseFlags := if endStream then endStreamFlag else 0
  let flags := baseFlags ||| endHeadersFlag
  { header := { length := headerBlock.size, typ := .headers, flags, streamId }
    payload := .headers { padLength? := none, priority? := none, headerBlock } }

def makeDataFrame (streamId : Http.Http2.StreamId) (data : ByteArray) : Http.Http2.Frame :=
  { header := { length := data.size, typ := .data, flags := endStreamFlag, streamId }
    payload := .data { padLength? := none, data } }

def requestToHttp2Frames (req : Request) (ctx : RequestH2Context := {}) :
    Array Http.Http2.Frame :=
  let headerBlock :=
    Http.HPack.encodeHeaderBlockBytes
      (requestPseudoHeaders req ctx ++ hpackHeaders req.headers)
  let hasBody := hasBodyData req.body?
  let headersFrame := makeHeadersFrame ctx.streamId headerBlock (!hasBody)
  match req.body? with
  | none => #[headersFrame]
  | some body =>
      if body.size == 0 then
        #[headersFrame]
      else
        #[headersFrame, makeDataFrame ctx.streamId body]

def responseToHttp2Frames (resp : Response) (ctx : ResponseH2Context := {}) :
    Array Http.Http2.Frame :=
  let headerBlock :=
    Http.HPack.encodeHeaderBlockBytes (responsePseudoHeaders resp ++ hpackHeaders resp.headers)
  let hasBody := hasBodyData resp.body?
  let headersFrame := makeHeadersFrame ctx.streamId headerBlock (!hasBody)
  match resp.body? with
  | none => #[headersFrame]
  | some body =>
      if body.size == 0 then
        #[headersFrame]
      else
        #[headersFrame, makeDataFrame ctx.streamId body]

end Http

end
