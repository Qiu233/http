module

public import Std
public import Http.Http1_1.Wire

public section

namespace Http.Http1_1.Builder

def crlf : String := "\r\n"

@[inline]
def versionString (v : Version) : String :=
  s!"HTTP/{v.major}.{v.minor}"

@[inline]
def requestTargetString : RequestTarget → String
  | .origin path query? =>
      match query? with
      | none => path
      | some q => path ++ "?" ++ q
  | .absolute uri => toString uri
  | .authority auth => toString auth
  | .asterisk => "*"

@[inline]
def requestLineString (line : RequestLine) : String :=
  line.method ++ " " ++ requestTargetString line.request_target ++ " " ++ versionString line.version

@[inline]
def statusCodeString (code : Nat) : String :=
  if code < 10 then s!"00{code}"
  else if code < 100 then s!"0{code}"
  else toString code

@[inline]
def statusLineString (line : StatusLine) : String :=
  match line.reason? with
  | none => versionString line.version ++ " " ++ statusCodeString line.status_code
  | some reason =>
      versionString line.version ++ " " ++ statusCodeString line.status_code ++ " " ++ reason

@[inline]
def fieldValueString (value : Array String) : String :=
  String.intercalate "" value.toList

@[inline]
def fieldLineString (line : FieldLine) : String :=
  let value := fieldValueString line.value
  let sep := if value.isEmpty then "" else " "
  line.name ++ ":" ++ sep ++ value

@[inline]
def startLineString : StartLine → String
  | .request line => requestLineString line
  | .status line => statusLineString line

@[inline]
def fieldLinesString (fields : Array FieldLine) : String :=
  String.intercalate crlf <| fields.toList.map fieldLineString

def httpMessageString (msg : HttpMessage) : String :=
  let fields := fieldLinesString msg.fields
  let fieldsBlock := if fields.isEmpty then "" else fields ++ crlf
  let body := msg.body?.getD ""
  startLineString msg.start_line ++ crlf ++ fieldsBlock ++ crlf ++ body

@[inline]
def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('a'.toNat + (n - 10))

partial def natToHex (n : Nat) : String :=
  if n == 0 then
    "0"
  else
    let rec loop (n : Nat) (acc : List Char) : List Char :=
      if n == 0 then
        acc
      else
        let digit := n % 16
        loop (n / 16) (hexDigit digit :: acc)
    String.ofList (loop n [])

@[inline]
def chunkExtString (exts : Array ChunkExt) : String :=
  exts.foldl (init := "") fun acc ext =>
    let value :=
      match ext.value? with
      | none => ""
      | some v => "=" ++ v
    acc ++ ";" ++ ext.name ++ value

@[inline]
def chunkString (chunk : Chunk) : String :=
  natToHex chunk.size ++ chunkExtString chunk.ext ++ crlf ++ chunk.data ++ crlf

def chunkedBodyString (body : ChunkedBody) : String :=
  let chunks := String.intercalate "" <| body.chunks.toList.map chunkString
  let trailers := fieldLinesString body.trailer
  let trailersBlock := if trailers.isEmpty then "" else trailers ++ crlf
  chunks ++ "0" ++ crlf ++ trailersBlock ++ crlf

end Http.Http1_1.Builder

end
