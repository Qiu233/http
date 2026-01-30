module

public import Uri.Basic

public section

namespace Http.Http1_1

abbrev Parameter := String × String
abbrev Parameters := Array (Option Parameter)
abbrev MediaType := String × String × Parameters
abbrev MediaRange := String × String × Parameters

structure Version where
  major : Nat
  minor : Nat
deriving Inhabited, Repr

inductive RequestTarget where
  | origin (path : String) (query? : Option String)
  | absolute (absUri : Uri)
  | authority (auth : Uri.Authority)
  | asterisk
deriving Inhabited

structure RequestLine where
  method : String
  request_target : RequestTarget
  version : Http.Http1_1.Version
deriving Inhabited

structure StatusLine where
  version : Http.Http1_1.Version
  status_code : Nat
  reason? : Option String
deriving Inhabited, Repr

structure FieldLine where
  name : String
  value : Array String
deriving Inhabited, Repr

inductive StartLine where
  | request (line : RequestLine)
  | status (line : StatusLine)
deriving Inhabited

structure HttpMessageHeader where
  start_line : StartLine
  fields : Array FieldLine
deriving Inhabited

structure ChunkExt where
  name : String
  value? : Option String
deriving Inhabited, Repr

structure Chunk where
  size : Nat
  ext : Array ChunkExt
  data : ByteArray
deriving Inhabited

structure ChunkedBody where
  chunks : Array Chunk
  lastChunk : Chunk
  trailer : Array FieldLine
deriving Inhabited

inductive HttpMessageBody where
  | bytes (data : ByteArray)
  | chunked (body : ChunkedBody)
deriving Inhabited

structure HttpMessage where
  header : HttpMessageHeader
  body? : Option HttpMessageBody
deriving Inhabited
