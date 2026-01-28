module

public import Uri
public import Http.Parser.Util

public section

namespace Http.Parser

variable {m} [instMonad : Monad m] [instOrElse : ∀ α, OrElse (m α)] [instParser : PolyParsec.MonadPolyParsec String m]

open PolyParsec

@[inline, specialize]
def mbx_WSP : m Char := SP <|> HTAB

@[inline, specialize]
def mbx_FWS : m String := do
  let _ ← optional (manyChars mbx_WSP *> CRLF)
  many1Chars mbx_WSP

@[inline, specialize]
def mbx_ctext : m Char := satisfy fun c =>
  ('\x21' ≤ c && c ≤ '\x27') ||
  ('\x2A' ≤ c && c ≤ '\x5B') ||
  ('\x5D' ≤ c && c ≤ '\x7E')

@[inline, specialize]
def mbx_quoted_pair : m String := do
  skipChar '\\'
  let c ← vchar <|> mbx_WSP
  return "\\" ++ c.toString

partial def mbx_comment : m String := do
  skipChar '('
  let parts ← many <| attempt (mbx_FWS *> (do
    let inner ← attempt mbx_comment <|> mbx_quoted_pair <|> (char_to_string <$> mbx_ctext)
    return inner)) <|> attempt mbx_comment <|> mbx_quoted_pair <|> (char_to_string <$> mbx_ctext)
  _ ← optional mbx_FWS
  skipChar ')'
  return "(" ++ String.intercalate "" parts.toList ++ ")"

@[inline, specialize]
def mbx_CFWS : m String := do
  (attempt do
    let parts ← many1 (attempt (optional mbx_FWS *> mbx_comment))
    let tail ← optional mbx_FWS
    let mut out := String.intercalate "" (parts.toList)
    if let some t := tail then out := out ++ t
    return out)
  <|> mbx_FWS

@[inline, specialize]
def mbx_atext : m Char := satisfy fun c =>
  c.isAlpha || c.isDigit ||
    c matches '!' | '#' | '$' | '%' | '&' | '\'' | '*' | '+' | '-' |
      '/' | '=' | '?' | '^' | '_' | '`' | '{' | '|' | '}' | '~'

@[inline, specialize]
def mbx_atom : m String := do
  _ ← optional mbx_CFWS
  let core ← many1Chars mbx_atext
  _ ← optional mbx_CFWS
  return core

@[inline, specialize]
def mbx_dot_atom_text : m String := do
  let first ← many1Chars mbx_atext
  let rest ← many (attempt (skipChar '.' *> many1Chars mbx_atext))
  let mut out := first
  for part in rest.toList do
    out := out ++ "." ++ part
  return out

@[inline, specialize]
def mbx_dot_atom : m String := do
  _ ← optional mbx_CFWS
  let core ← mbx_dot_atom_text
  _ ← optional mbx_CFWS
  return core

@[inline, specialize]
def mbx_qtext : m Char := satisfy fun c =>
  c == '\x21' || ('\x23' ≤ c && c ≤ '\x5B') || ('\x5D' ≤ c && c ≤ '\x7E')

@[inline, specialize]
def mbx_quoted_string : m String := do
  _ ← optional mbx_CFWS
  _ ← DQUOTE
  let parts ← many (attempt (optional mbx_FWS *> (do
    let qcontent ← (char_to_string <$> mbx_qtext) <|> mbx_quoted_pair
    return qcontent)))
  _ ← optional mbx_FWS
  _ ← DQUOTE
  _ ← optional mbx_CFWS
  return String.intercalate "" parts.toList

@[inline, specialize]
def mbx_word : m String := mbx_atom <|> mbx_quoted_string

@[inline, specialize]
def mbx_phrase : m String := do
  let first ← mbx_word
  let rest ← many (attempt (mbx_FWS *> mbx_word))
  let mut out := first
  for part in rest.toList do
    out := out ++ " " ++ part
  return out

@[inline, specialize]
def mbx_local_part : m String := mbx_dot_atom <|> mbx_quoted_string

@[inline, specialize]
def mbx_dtext : m Char := satisfy fun c =>
  ('\x21' ≤ c && c ≤ '\x5A') || ('\x5E' ≤ c && c ≤ '\x7E')

@[inline, specialize]
def mbx_domain_literal : m String := do
  _ ← optional mbx_CFWS
  skipChar '['
  let parts ← many (attempt (optional mbx_FWS *> (char_to_string <$> mbx_dtext)))
  _ ← optional mbx_FWS
  skipChar ']'
  _ ← optional mbx_CFWS
  return "[" ++ String.intercalate "" parts.toList ++ "]"

@[inline, specialize]
def mbx_domain : m String := mbx_dot_atom <|> mbx_domain_literal

@[inline, specialize]
def mbx_addr_spec : m String := do
  let local_ ← mbx_local_part
  skipChar '@'
  let dom ← mbx_domain
  return local_ ++ "@" ++ dom

@[inline, specialize]
def mbx_angle_addr : m String := do
  _ ← optional mbx_CFWS
  skipChar '<'
  let addr ← mbx_addr_spec
  skipChar '>'
  _ ← optional mbx_CFWS
  return "<" ++ addr ++ ">"

@[inline, specialize]
def mbx_name_addr : m String := do
  let display? ← optional mbx_phrase
  let addr ← mbx_angle_addr
  return match display? with
    | none => addr
    | some d => d ++ " " ++ addr

@[inline, specialize]
def mailbox : m String := (attempt mbx_name_addr) <|> mbx_addr_spec

end Http.Parser
