module

public import Binary
public import Http.Http1_1.Parser

public section

namespace Http.Http1_1

@[inline]
def fieldValueString (value : Array String) : String :=
  String.intercalate "" value.toList

@[inline]
def trimOWS (s : String) : String :=
  let isOWS := fun c => c == ' ' || c == '\t'
  let chars := s.toList.dropWhile isOWS
  let chars := chars.reverse.dropWhile isOWS |>.reverse
  String.ofList chars

@[inline]
def parseDecNat? (s : String) : Option Nat := do
  if s.isEmpty then
    none
  let mut acc := 0
  for c in s.toList do
    if c.isDigit then
      acc := acc * 10 + (c.toNat - '0'.toNat)
    else
      none
  some acc

/-- return an array of fields with specified name -/
def HttpMessageHeader.getFields (header : HttpMessageHeader) (name : String) : Array String :=
  header.fields.filterMap fun x =>
    if x.name.toLower == name then
      some (trimOWS <| fieldValueString x.value)
    else none

def HttpMessageHeader.getField (header : HttpMessageHeader) (name : String) : Option String :=
  (header.getFields name)[0]?

def HttpMessageHeader.content_length? (header : HttpMessageHeader) : Except String (Option Nat) := do
  let vs := header.getFields "content-length"
  if vs.isEmpty then
    return none
  let #[v] := vs | throw s!"more than one Content-Length found in message header"
  parseDecNat? v |>.getDM (throw s!"invalid Content-Length value: {v}")

def HttpMessageHeader.is_chunked (header : HttpMessageHeader) : Except String Bool := do
  let vs := header.getFields "transfer-encoding"
  if vs.isEmpty then
    return false
  let es ← vs.mapM fun x => Parser.transfer_encoding.run x.toUTF8 |>.toExceptString
  let es := es.flatten
  return es.any fun (name, _) => name == "chunked"

-- namespace Parser

-- open Binary

-- @[inline]
-- def http_message : Get HttpMessage := do
--   let header ← http_message_header
--   let content_length? ← match header.content_length? with
--     | .error e => throw (.userError s!"failed to decode content-length: {e}")
--     | .ok r => pure r
--   let body? ← do
--     match content_length? with
--     | some len =>
--       if len == 0 then
--         pure none
--       else
--         (some ∘ HttpMessageBody.bytes) <$> get_bytes len
--     | none =>
--       let is_chunked ← match header.is_chunked with
--         | .error e => throw (.userError s!"failed to decode transfer-encoding: {e}")
--         | .ok r => pure r
--       if is_chunked then
--         let cbody ← chunked_body
--         pure <| some <| HttpMessageBody.chunked cbody
--       else
--         let rem ← exhaust
--         if rem.size == 0 then
--           pure none
--         else
--           pure <| some <| HttpMessageBody.bytes rem
--   return { header := header, body? }

-- end Parser
