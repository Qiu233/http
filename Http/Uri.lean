module
public import Uri
public import Uri.Basic
public import Binary
public import Http.Parser.Util

/-!
See RFC9110 §4.Identifiers in HTTP
-/

public section

namespace Uri.Parser

open Binary UTF8
open Http.Parser

@[inline]
def partial_uri : Get Uri := do
  let (auth?, path) ← relative_part
  let query? ← optional do
    skipChar '?'
    query
  return { scheme? := none, authority? := auth?, path, query? }

@[inline]
private def uri_helper (scheme : String) : Get Uri := do
  skipString scheme
  skipString "://"
  let auth ← authority
  let path ← path_abempty
  let query? ← optional do
    skipChar '?'
    query
  return { scheme? := some scheme, authority? := some auth, path, query? }

@[always_inline]
def http_uri : Get Uri := uri_helper "http"

@[always_inline]
def https_uri : Get Uri := uri_helper "https"

end Uri.Parser

@[inline]
def Uri.http (host : Uri.Host) (port : UInt16) (path : String) (query? : Option String := Option.none) : Uri :=
  { scheme? := some "http", authority? := some { userInfo? := none, host, port? := some port }, path, query? }

-- @[inline]
-- def Uri.https (host : Uri.Host) (port : UInt16) (path : String) (query? : Option String := Option.none) : Uri :=
--   { scheme? := some "https", authority? := some { userInfo? := none, host, port? := some port }, path, query? }

end
