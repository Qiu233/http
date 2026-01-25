module

public import Uri
public import Http.Parser.Util

public section

namespace Http.Parser

variable {m} [instMonad : Monad m] [instOrElse : ∀ α, OrElse (m α)] [instParser : Uri.Parser.MonadParser m]

open Uri.Parser.MonadParser

@[inline, specialize]
def alphanum : m Char := satisfy fun c => c.isAlpha || c.isDigit

@[inline, specialize]
def subtag_len (min max : Nat) (p : m Char) : m String := do
  let head ← takeN min p
  let tail ← takeUpTo (max - min) p
  let xs := head ++ tail
  if tail.size == max - min then
    _ ← notFollowedBy p
  return chars_to_string xs

@[inline, specialize]
def alpha_subtag (min max : Nat) : m String :=
  subtag_len min max ALPHA

@[inline, specialize]
def alphanum_subtag (min max : Nat) : m String :=
  subtag_len min max alphanum

@[inline, specialize]
def language_range : m String := do
  (attempt (pchar '*' *> pure "*")) <|> (do
    let first ← alpha_subtag 1 8
    let rest ← many (attempt (skipChar '-' *> alphanum_subtag 1 8))
    return String.intercalate "-" (first :: rest.toList))

end Http.Parser
