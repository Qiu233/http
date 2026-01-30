module

public import Binary
public import Http.Parser.Util

public section

namespace Http.Parser

open Binary UTF8

@[inline]
def alphanum : Get Char := satisfy fun c => c.isAlpha || c.isDigit

@[inline]
def subtag_len (min max : Nat) (p : Get Char) : Get String := do
  let head ← takeN min p
  let tail ← takeUpTo (max - min) p
  let xs := head ++ tail
  if tail.size == max - min then
    _ ← notFollowedBy p
  return String.ofList xs.toList

@[inline]
def alpha_subtag (min max : Nat) : Get String :=
  subtag_len min max ALPHA

@[inline]
def alphanum_subtag (min max : Nat) : Get String :=
  subtag_len min max alphanum

@[inline]
def language_range : Get String := do
  (pchar '*' *> pure "*") <|> (do
    let first ← alpha_subtag 1 8
    let rest ← many (skipChar '-' *> alphanum_subtag 1 8)
    return String.intercalate "-" (first :: rest.toList))

end Http.Parser
