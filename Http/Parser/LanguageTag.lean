module

public import Uri
public import Http.Parser.Util
public import Http.Parser.LanguageRange

public section

namespace Http.Parser

variable {m} [instMonad : Monad m] [instOrElse : ∀ α, OrElse (m α)] [instParser : Uri.Parser.MonadParser m]

open Uri.Parser.MonadParser

@[inline, specialize]
def language_tag_extlang : m String := do
  let first ← alpha_subtag 3 3
  let rest ← many (attempt (skipChar '-' *> alpha_subtag 3 3))
  let rest := rest.toList
  if rest.length > 2 then
    fail "extlang too long"
  return String.intercalate "-" (first :: rest)

@[inline, specialize]
def language_tag_language : m String :=
  (attempt do
    let primary ← alpha_subtag 2 3
    let ext? ← optional (attempt (skipChar '-' *> language_tag_extlang))
    return match ext? with
      | none => primary
      | some ext => primary ++ "-" ++ ext)
  <|> (attempt (alpha_subtag 4 4))
  <|> (alpha_subtag 5 8)

@[inline, specialize]
def language_tag_script : m String := alpha_subtag 4 4

@[inline, specialize]
def language_tag_region : m String :=
  alpha_subtag 2 2 <|> subtag_len 3 3 DIGIT

@[inline, specialize]
def language_tag_variant_digit : m String := do
  let first ← DIGIT
  let rest ← takeN 3 alphanum
  _ ← notFollowedBy alphanum
  return first.toString ++ chars_to_string rest

@[inline, specialize]
def language_tag_variant : m String :=
  (attempt language_tag_variant_digit) <|> alphanum_subtag 5 8

@[inline, specialize]
def language_tag_singleton : m String := do
  let c ← satisfy fun c =>
    c.isDigit ||
      ('A' ≤ c && c ≤ 'W') || ('Y' ≤ c && c ≤ 'Z') ||
      ('a' ≤ c && c ≤ 'w') || ('y' ≤ c && c ≤ 'z')
  return c.toString

@[inline, specialize]
def language_tag_extension : m String := do
  let singleton ← language_tag_singleton
  let subtags ← many1 (attempt (skipChar '-' *> alphanum_subtag 2 8))
  return String.intercalate "-" (singleton :: subtags.toList)

@[inline, specialize]
def language_tag_variants : m (Array String) :=
  many (attempt (skipChar '-' *> language_tag_variant))

@[inline, specialize]
def language_tag_extensions : m (Array String) :=
  many (attempt (skipChar '-' *> language_tag_extension))

@[inline, specialize]
def language_tag_privateuse : m String := do
  let x ← satisfy fun c => c == 'x' || c == 'X'
  let subtags ← many1 (attempt (skipChar '-' *> alphanum_subtag 1 8))
  return String.intercalate "-" (x.toString :: subtags.toList)

@[inline, specialize]
def language_tag_langtag : m String := do
  let language ← language_tag_language
  let script? : m _ := optional (attempt (skipChar '-' *> language_tag_script))
  let region? : m _ := optional (attempt (skipChar '-' *> language_tag_region))
  let variants ← language_tag_variants
  let extensions ← language_tag_extensions
  let privateuse? : m _ := optional (attempt (skipChar '-' *> language_tag_privateuse))
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

@[inline, specialize]
def pstring_ci (s : String) : m String := do
  for c in s.toList do
    let _ ← satisfy fun x => x.toLower == c.toLower
  return s

@[inline, specialize]
def language_tag_parse_list (xs : Array String) : m String := do
  let mut acc : Option String := none
  for tag in xs do
    match acc with
    | some _ => pure ()
    | none =>
      if let some res ← optional (attempt (pstring_ci tag)) then
        acc := some res
  match acc with
  | some res => pure res
  | none => fail "invalid grandfathered tag"

@[inline, specialize]
def language_tag_grandfathered : m String :=
  (attempt (language_tag_parse_list language_tag_grandfathered_irregular))
  <|> (language_tag_parse_list language_tag_grandfathered_regular)

@[always_inline, specialize]
def language_tag : m String :=
  (attempt language_tag_langtag) <|> (attempt language_tag_privateuse) <|> language_tag_grandfathered

end Http.Parser
