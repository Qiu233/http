module
public import Uri

/-!
See RFC9110 §4.Identifiers in HTTP
-/

public section

namespace Uri.Parser


variable {m} [instMonad : Monad m] [instOrElse : ∀ α, OrElse (m α)] [instParser : Uri.Parser.MonadParser m]

open Uri.Parser.MonadParser

@[always_inline, specialize]
def uri_host : m Host := host

@[always_inline, specialize]
def absolute_path : m (String) := do
  let ss ← many1 (skipChar '/' *> segment)
  return String.intercalate "" <| ss.toList.map (fun x => s!"/{x}")

@[specialize]
def partial_uri : m Uri := do
  let (auth?, path) ← relative_part
  let query? ← optional do
    skipChar '?'
    query
  return { scheme? := none, authority? := auth?, path, query? }

@[specialize]
private def uri_helper (scheme : String) : m Uri := do
  skipString scheme
  skipString "://"
  let auth ← authority
  let path ← path_abempty
  let query? ← optional do
    skipChar '?'
    query
  return { scheme? := some scheme, authority? := some auth, path, query? }

@[always_inline, specialize]
def http_uri : m Uri := uri_helper "http"

@[always_inline, specialize]
def https_uri : m Uri := uri_helper "https"

end Uri.Parser

@[inline]
def Uri.http (host : Uri.Host) (port : UInt16) (path : String) (query? : Option String := Option.none) : Uri :=
  { scheme? := some "http", authority? := some { userInfo? := none, host, port? := some port }, path, query? }

-- @[inline]
-- def Uri.https (host : Uri.Host) (port : UInt16) (path : String) (query? : Option String := Option.none) : Uri :=
--   { scheme? := some "https", authority? := some { userInfo? := none, host, port? := some port }, path, query? }

end
