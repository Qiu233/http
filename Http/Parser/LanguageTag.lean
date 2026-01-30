module

public import Binary
public import Http.Parser.Util
public import Http.Parser.LanguageRange

public section

namespace Http.Parser

open Binary UTF8

@[inline]
def language_tag_extlang : Get String := do
  let first ← alpha_subtag 3 3
  let rest ← many (skipChar '-' *> alpha_subtag 3 3)
  let rest := rest.toList
  if rest.length > 2 then
    fail "extlang too long"
  return String.intercalate "-" (first :: rest)

@[inline]
def language_tag_language : Get String :=
  (do
    let primary ← alpha_subtag 2 3
    let ext? ← optional (skipChar '-' *> language_tag_extlang)
    return match ext? with
      | none => primary
      | some ext => primary ++ "-" ++ ext)
  <|> (alpha_subtag 4 4)
  <|> (alpha_subtag 5 8)

@[inline]
def language_tag_script : Get String := alpha_subtag 4 4

@[inline]
def language_tag_region : Get String :=
  alpha_subtag 2 2 <|> subtag_len 3 3 DIGIT

@[inline]
def language_tag_variant_digit : Get String := do
  let first ← DIGIT
  let rest ← takeN 3 alphanum
  _ ← notFollowedBy alphanum
  return first.toString ++ String.ofList rest.toList

@[inline]
def language_tag_variant : Get String :=
  (language_tag_variant_digit) <|> alphanum_subtag 5 8

@[inline]
def language_tag_singleton : Get String := do
  let c ← satisfy fun c =>
    c.isDigit ||
      ('A' ≤ c && c ≤ 'W') || ('Y' ≤ c && c ≤ 'Z') ||
      ('a' ≤ c && c ≤ 'w') || ('y' ≤ c && c ≤ 'z')
  return c.toString

@[inline]
def language_tag_extension : Get String := do
  let singleton ← language_tag_singleton
  let subtags ← many1 (skipChar '-' *> alphanum_subtag 2 8)
  return String.intercalate "-" (singleton :: subtags.toList)

@[inline]
def language_tag_variants : Get (Array String) :=
  many (skipChar '-' *> language_tag_variant)

@[inline]
def language_tag_extensions : Get (Array String) :=
  many (skipChar '-' *> language_tag_extension)

@[inline]
def language_tag_privateuse : Get String := do
  let x ← satisfy fun c => c == 'x' || c == 'X'
  let subtags ← many1 (skipChar '-' *> alphanum_subtag 1 8)
  return String.intercalate "-" (x.toString :: subtags.toList)

@[inline]
def language_tag_langtag : Get String := do
  let language ← language_tag_language
  let script? : Get _ := optional (skipChar '-' *> language_tag_script)
  let region? : Get _ := optional (skipChar '-' *> language_tag_region)
  let variants ← language_tag_variants
  let extensions ← language_tag_extensions
  let privateuse? : Get _ := optional (skipChar '-' *> language_tag_privateuse)
  let mut out := language
  if let some s ← script? then out := out ++ "-" ++ s
  if let some r ← region? then out := out ++ "-" ++ r
  for v in variants.toList do
    out := out ++ "-" ++ v
  for e in extensions.toList do
    out := out ++ "-" ++ e
  if let some p ← privateuse? then out := out ++ "-" ++ p
  return out

def language_tag_grandfathered_irregular : Array String :=
  #[
    "en-GB-oed", "i-ami", "i-bnn", "i-default", "i-enochian", "i-hak",
    "i-klingon", "i-lux", "i-mingo", "i-navajo", "i-pwn", "i-tao",
    "i-tay", "i-tsu", "sgn-BE-FR", "sgn-BE-NL", "sgn-CH-DE"
  ]

def language_tag_grandfathered_regular : Array String :=
  #[
    "art-lojban", "cel-gaulish", "no-bok", "no-nyn", "zh-guoyu",
    "zh-hakka", "zh-min", "zh-min-nan", "zh-xiang"
  ]

@[inline]
def pstring_ci (s : String) : Get String := do
  for c in s.toList do
    let _ ← satisfy fun x => x.toLower == c.toLower
  return s

@[inline]
def language_tag_parse_list (xs : Array String) : Get String := do
  let mut acc : Option String := none
  for tag in xs do
    match acc with
    | some _ => pure ()
    | none =>
      if let some res ← optional (pstring_ci tag) then
        acc := some res
  match acc with
  | some res => pure res
  | none => fail "invalid grandfathered tag"

@[inline]
def language_tag_grandfathered : Get String :=
  (language_tag_parse_list language_tag_grandfathered_irregular)
  <|> (language_tag_parse_list language_tag_grandfathered_regular)

@[always_inline]
def language_tag : Get String :=
  (language_tag_langtag) <|> (language_tag_privateuse) <|> language_tag_grandfathered

end Http.Parser
