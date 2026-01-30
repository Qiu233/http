module

public import Binary

public section

namespace Http.Parser

open Binary UTF8

@[inline]
def byteToChar (b : UInt8) : Char :=
  Char.ofNat b.toNat

@[inline]
def char_to_string (c : Char) : String := String.ofList [c]

@[always_inline]
def CR : Get Char := pchar '\r'

@[always_inline]
def LF : Get Char := pchar '\n'

-- RFC9112.§2.2.Message Parsing:
-- Although the line terminator for the start-line and fields is the sequence CRLF,
--   a recipient MAY recognize a single LF as a line terminator and ignore any preceding CR.
@[always_inline]
def CRLF : Get Unit :=
  skipString "\r\n" <|> skipString "\n"

@[always_inline]
def DQUOTE : Get Char := pchar '"'

@[always_inline]
def SP : Get Char := pchar ' '

@[always_inline]
def HTAB : Get Char := pchar '\t'

@[always_inline]
def ALPHA : Get Char := satisfy Char.isAlpha

@[always_inline]
def DIGIT : Get Char := satisfy Char.isDigit

@[always_inline]
def HEXDIG : Get Char := satisfy fun c =>
  c.isDigit || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

@[always_inline]
def OCTET : Get Char := satisfy fun c => '\x00' ≤ c && c ≤ '\xFF'

@[always_inline]
def vchar : Get Char := satisfy fun c => '\x21' ≤ c && c ≤ '\x7e'

@[always_inline]
def obs_text : Get Char := satisfy fun c => '\x80' ≤ c && c ≤ '\xFF'

end Http.Parser
