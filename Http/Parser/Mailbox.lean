module

public import Binary
public import Http.Parser.Util

public section

namespace Http.Parser

open Binary UTF8

@[inline]
def mbx_WSP : Get Char := SP <|> HTAB

@[inline]
def mbx_FWS : Get String := do
  let _ ← optional (manyChars mbx_WSP *> CRLF)
  many1Chars mbx_WSP

@[inline]
def mbx_ctext : Get Char := satisfy fun c =>
  ('\x21' ≤ c && c ≤ '\x27') ||
  ('\x2A' ≤ c && c ≤ '\x5B') ||
  ('\x5D' ≤ c && c ≤ '\x7E')

@[inline]
def mbx_quoted_pair : Get String := do
  skipChar '\\'
  let c ← vchar <|> mbx_WSP
  return "\\" ++ c.toString

partial def mbx_comment : Get String := do
  skipChar '('
  let parts ← many <| (mbx_FWS *> (do
    let inner ← mbx_comment <|> mbx_quoted_pair <|> (char_to_string <$> mbx_ctext)
    return inner)) <|> mbx_comment <|> mbx_quoted_pair <|> (char_to_string <$> mbx_ctext)
  _ ← optional mbx_FWS
  skipChar ')'
  return "(" ++ String.intercalate "" parts.toList ++ ")"

@[inline]
def mbx_CFWS : Get String := do
  (do
    let parts ← many1 (optional mbx_FWS *> mbx_comment)
    let tail ← optional mbx_FWS
    let mut out := String.intercalate "" (parts.toList)
    if let some t := tail then out := out ++ t
    return out)
  <|> mbx_FWS

@[inline]
def mbx_atext : Get Char := satisfy fun c =>
  c.isAlpha || c.isDigit ||
    c matches '!' | '#' | '$' | '%' | '&' | '\'' | '*' | '+' | '-' |
      '/' | '=' | '?' | '^' | '_' | '`' | '{' | '|' | '}' | '~'

@[inline]
def mbx_atom : Get String := do
  _ ← optional mbx_CFWS
  let core ← many1Chars mbx_atext
  _ ← optional mbx_CFWS
  return core

@[inline]
def mbx_dot_atom_text : Get String := do
  let first ← many1Chars mbx_atext
  let rest ← many (skipChar '.' *> many1Chars mbx_atext)
  let mut out := first
  for part in rest.toList do
    out := out ++ "." ++ part
  return out

@[inline]
def mbx_dot_atom : Get String := do
  _ ← optional mbx_CFWS
  let core ← mbx_dot_atom_text
  _ ← optional mbx_CFWS
  return core

@[inline]
def mbx_qtext : Get Char := satisfy fun c =>
  c == '\x21' || ('\x23' ≤ c && c ≤ '\x5B') || ('\x5D' ≤ c && c ≤ '\x7E')

@[inline]
def mbx_quoted_string : Get String := do
  _ ← optional mbx_CFWS
  _ ← DQUOTE
  let parts ← many (optional mbx_FWS *> (do
    let qcontent ← (char_to_string <$> mbx_qtext) <|> mbx_quoted_pair
    return qcontent))
  _ ← optional mbx_FWS
  _ ← DQUOTE
  _ ← optional mbx_CFWS
  return String.intercalate "" parts.toList

@[inline]
def mbx_word : Get String := mbx_atom <|> mbx_quoted_string

@[inline]
def mbx_phrase : Get String := do
  let first ← mbx_word
  let rest ← many (mbx_FWS *> mbx_word)
  let mut out := first
  for part in rest.toList do
    out := out ++ " " ++ part
  return out

@[inline]
def mbx_local_part : Get String := mbx_dot_atom <|> mbx_quoted_string

@[inline]
def mbx_dtext : Get Char := satisfy fun c =>
  ('\x21' ≤ c && c ≤ '\x5A') || ('\x5E' ≤ c && c ≤ '\x7E')

@[inline]
def mbx_domain_literal : Get String := do
  _ ← optional mbx_CFWS
  skipChar '['
  let parts ← many (optional mbx_FWS *> (char_to_string <$> mbx_dtext))
  _ ← optional mbx_FWS
  skipChar ']'
  _ ← optional mbx_CFWS
  return "[" ++ String.intercalate "" parts.toList ++ "]"

@[inline]
def mbx_domain : Get String := mbx_dot_atom <|> mbx_domain_literal

@[inline]
def mbx_addr_spec : Get String := do
  let local_ ← mbx_local_part
  skipChar '@'
  let dom ← mbx_domain
  return local_ ++ "@" ++ dom

@[inline]
def mbx_angle_addr : Get String := do
  _ ← optional mbx_CFWS
  skipChar '<'
  let addr ← mbx_addr_spec
  skipChar '>'
  _ ← optional mbx_CFWS
  return "<" ++ addr ++ ">"

@[inline]
def mbx_name_addr : Get String := do
  let display? ← optional mbx_phrase
  let addr ← mbx_angle_addr
  return match display? with
    | none => addr
    | some d => d ++ " " ++ addr

@[inline]
def mailbox : Get String := (mbx_name_addr) <|> mbx_addr_spec

end Http.Parser
