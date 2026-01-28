module

public import Uri
public import PolyParsec

public section

namespace Http.Parser

variable {m} [instMonad : Monad m] [instOrElse : ∀ α, OrElse (m α)] [instParser : PolyParsec.MonadPolyParsec String m]

open PolyParsec

@[always_inline, specialize]
def CR : m Char := pchar '\r'

@[always_inline, specialize]
def LF : m Char := pchar '\n'

-- RFC9112.§2.2.Message Parsing:
-- Although the line terminator for the start-line and fields is the sequence CRLF,
--   a recipient MAY recognize a single LF as a line terminator and ignore any preceding CR.

@[always_inline, specialize]
def CRLF : m Unit :=
  skipString "\r\n" <|> skipString "\n"

@[always_inline, specialize]
def DQUOTE : m Char := pchar '"'

@[always_inline, specialize]
def SP : m Char := pchar ' '

@[always_inline, specialize]
def HTAB : m Char := pchar '\t'

@[always_inline, specialize]
def ALPHA : m Char := satisfy Char.isAlpha

@[always_inline, specialize]
def DIGIT : m Char := satisfy Char.isDigit

@[always_inline, specialize]
def HEXDIG : m Char := satisfy fun c =>
  c.isDigit || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

@[always_inline, specialize]
def OCTET : m Char := satisfy fun c => '\x00' ≤ c && c ≤ '\xFF'

@[always_inline, specialize]
def vchar : m Char := satisfy fun c => '\x21' ≤ c && c ≤ '\x7e'

@[always_inline, specialize]
def obs_text : m Char := satisfy fun c => '\x80' ≤ c && c ≤ '\xFF'

@[inline]
def char_to_string (c : Char) : String := String.ofList [c]

@[inline]
def chars_to_string (xs : Array Char) : String := String.ofList xs.toList

@[inline, specialize]
def takeUpTo (n : Nat) (p : m α) : m (Array α) :=
  rest n #[]
where
  rest : Nat → Array α → m (Array α)
    | 0, xs => return xs
    | n+1, xs => do
      match ← optional (attempt p) with
      | some x => rest n <| xs.push x
      | none => return xs

@[inline, specialize]
def takeN (n : Nat) (p : m α) : m (Array α) :=
  rest n #[]
where
  rest : Nat → Array α → m (Array α)
    | 0, xs => return xs
    | n+1, xs => do rest n <| xs.push (← p)

end Http.Parser
