module

public import Uri

public section

namespace Http

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
  version : Http.Version
deriving Inhabited

structure StatusLine where
  version : Http.Version
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

structure HttpMessage where
  start_line : StartLine
  fields : Array FieldLine
  body? : Option String
deriving Inhabited

structure ChunkExt where
  name : String
  value? : Option String
deriving Inhabited, Repr

structure Chunk where
  size : Nat
  ext : Array ChunkExt
  data : String
deriving Inhabited, Repr

structure ChunkedBody where
  chunks : Array Chunk
  trailer : Array FieldLine
deriving Inhabited, Repr
