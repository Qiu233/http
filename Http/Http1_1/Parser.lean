module

public import Uri
public import Http.Http1_1.Wire
public import Http.Uri
public import Http.Parser.Util
public import Http.Parser.LanguageRange
public import Http.Parser.LanguageTag
public import Http.Parser.Mailbox

public section

namespace Http.Http1_1.Parser

open Http.Parser

variable {m} [instMonad : Monad m] [instOrElse : ∀ α, OrElse (m α)] [instParser : PolyParsec.MonadPolyParsec String m]

open PolyParsec
open Uri.Parser

@[always_inline, specialize]
def http_name : m String := pstring "HTTP"

private def decode_dec! : Char → Nat := fun c =>
  if c.isDigit then c.toNat - '0'.toNat
  else panic! "invalid decimal character"

@[always_inline, specialize]
def http_version : m Version := do
  _ ← http_name
  skipChar '/'
  let x ← decode_dec! <$> satisfy Char.isDigit
  skipChar '.'
  let y ← decode_dec! <$> satisfy Char.isDigit
  return { major := x, minor := y }

@[inline, specialize]
def tchar : m Char := do
  satisfy fun c => c.isDigit || c.isAlpha ||
    c matches '!' | '#' | '$' | '%' | '&' | '\'' | '*' |
      '+' | '-' | '.' | '^' | '_' | '`' | '|' | '~'

@[always_inline, specialize]
def token : m String := many1Chars tchar

@[always_inline, specialize]
def method : m String := token

@[always_inline, specialize]
def origin_form : m (String × Option String) := do
  let path ← Uri.Parser.absolute_path
  let query? ← optional do
    skipChar '?'
    query
  return (path, query?)

@[always_inline, specialize]
def absolute_form : m Uri := absolute_uri

@[always_inline, specialize]
def authority_form : m Uri.Authority := do
  let host ← host
  skipChar ':'
  let port ← Uri.Parser.port
  return { userInfo? := none, host, port? := some port }

@[always_inline, specialize]
def asterisk_form : m Char := pchar '*'

@[always_inline, specialize]
def SP' : m Unit := skipChar ' '

@[always_inline, specialize]
def HTAB' : m Unit := skipChar '\t'

@[inline, specialize]
def request_target : m RequestTarget :=
  attempt (origin_form >>= fun (path, query?) => return RequestTarget.origin path query?)
  <|> attempt (absolute_form <&> RequestTarget.absolute)
  <|> attempt (authority_form <&> RequestTarget.authority)
  <|> (asterisk_form *> pure RequestTarget.asterisk)

@[inline, specialize]
def request_line : m RequestLine := do
  let method ← method
  SP'
  let request_target ← request_target
  SP'
  let version ← http_version
  return { method, request_target, version }

@[inline, specialize]
def status_code : m Nat := do
  let a ← decode_dec! <$> satisfy Char.isDigit
  let b ← decode_dec! <$> satisfy Char.isDigit
  let c ← decode_dec! <$> satisfy Char.isDigit
  return a * 100 + b * 10 + c

@[always_inline, specialize]
def reason_phrase : m String :=
  many1Chars <| HTAB <|> SP <|> vchar <|> obs_text

@[inline, specialize]
def status_line : m StatusLine := do
  let version ← http_version
  SP'
  let status_code ← status_code
  SP'
  let reason? ← optional reason_phrase
  return { version, status_code, reason? }

@[always_inline, specialize]
def OWS : m String := manyChars <| SP <|> HTAB

@[always_inline, specialize]
def RWS : m String := many1Chars <| SP <|> HTAB

@[always_inline, specialize]
def BWS : m String := OWS

@[always_inline, specialize]
def field_name : m String := token

@[always_inline, specialize]
def field_vchar : m Char := vchar <|> obs_text

@[inline, specialize]
partial def field_content : m String := do
  let first ← field_vchar
  let tail ← optional do
    let xs ← many1Chars <| SP <|> HTAB <|> field_vchar
    let last := String.back xs
    if last matches ' ' | '\t' then
      fail "field-content must end with field-vchar"
    return xs
  return tail.map (fun t => first.toString ++ t) |>.getD first.toString

@[always_inline, specialize]
def field_value : m (Array String) := many field_content

@[inline, specialize]
def field_line : m FieldLine := do
  let name ← field_name
  skipChar ':'
  _ ← OWS
  let value ← field_value
  _ ← OWS
  return { name, value }

@[inline, specialize]
private def decimal_nat : m Nat := do
  let s ← many1Chars DIGIT
  let xs := s.toList.map fun c => c.toNat - '0'.toNat
  let x :: xs := xs | unreachable!
  return xs.foldl (init := x) fun acc t => acc * 10 + t

private def decode_hex! : Char → Nat := fun c =>
  if c.isDigit then c.toNat - '0'.toNat
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else panic! "invalid hex character"

@[inline, specialize]
private def hex_nat : m Nat := do
  let s ← many1Chars HEXDIG
  let xs := s.toList.map decode_hex!
  let x :: xs := xs | unreachable!
  return xs.foldl (init := x) fun acc t => acc * 16 + t

@[inline, specialize]
private def comma_list (p : m α) : m (Array α) := do
  let first? ← optional (attempt p)
  match first? with
  | none => return #[]
  | some first =>
    let mut xs := #[first]
    repeat
      if let some x ← optional (attempt (OWS *> skipChar ',' *> OWS *> p)) then
        xs := xs.push x
      else break
    return xs

@[inline, specialize]
private def sp_list (p : m α) : m (Array α) := do
  let first? ← optional (attempt p)
  match first? with
  | none => return #[]
  | some first =>
    let mut xs := #[first]
    repeat
      if let some x ← optional (attempt (RWS *> p)) then
        xs := xs.push x
      else break
    return xs

@[always_inline, specialize]
def obs_fold : m String := do
  let pre ← OWS
  CRLF
  let post ← RWS
  return pre ++ "\r\n" ++ post

@[always_inline, specialize]
def token68 : m String := do
  let head ← many1Chars <| satisfy fun c =>
    c.isAlpha || c.isDigit || c matches '-' | '.' | '_' | '~' | '+' | '/'
  let pad ← manyChars (pchar '=')
  return head ++ pad

@[always_inline, specialize]
def qdtext : m Char := satisfy fun c =>
  c == '\t' || c == '!' || c == ' ' ||
    ('\x23' ≤ c && c ≤ '\x5B') ||
    ('\x5D' ≤ c && c ≤ '\x7E') ||
    ('\x80' ≤ c && c ≤ '\xFF')

@[always_inline, specialize]
def quoted_pair : m String := do
  skipChar '\\'
  let c ← HTAB <|> SP <|> vchar <|> obs_text
  return "\\" ++ c.toString

@[always_inline, specialize]
def quoted_string : m String := do
  _ ← DQUOTE
  let parts ← many <| (char_to_string <$> qdtext) <|> quoted_pair
  _ ← DQUOTE
  return String.intercalate "" parts.toList

@[always_inline, specialize]
def ctext : m Char := satisfy fun c =>
  c == '\t' || c == ' ' ||
    ('\x21' ≤ c && c ≤ '\x27') ||
    ('\x2A' ≤ c && c ≤ '\x5B') ||
    ('\x5D' ≤ c && c ≤ '\x7E') ||
    ('\x80' ≤ c && c ≤ '\xFF')

partial def comment : m String := do
  skipChar '('
  let parts ← many <| attempt comment <|> quoted_pair <|> (char_to_string <$> ctext)
  skipChar ')'
  return "(" ++ String.intercalate "" parts.toList ++ ")"

@[always_inline, specialize]
def parameter_name : m String := token

@[always_inline, specialize]
def parameter_value : m String := token <|> quoted_string

@[always_inline, specialize]
def parameter : m Parameter := do
  let name ← parameter_name
  skipChar '='
  let value ← parameter_value
  return (name, value)

@[inline, specialize]
def parameters : m Parameters := do
  let mut xs := #[]
  repeat
    if let some v ← optional (attempt (OWS *> skipChar ';' *> OWS *> optional parameter)) then
      xs := xs.push v
    else break
  return xs

@[always_inline, specialize]
def type : m String := token

@[always_inline, specialize]
def subtype : m String := token

@[inline, specialize]
def media_type : m MediaType := do
  let t ← type
  skipChar '/'
  let s ← subtype
  let params ← parameters
  return (t, s, params)

@[inline, specialize]
def media_range : m MediaRange := do
  (attempt do
      skipString "*/*"
      let params ← parameters
      return ("*", "*", params))
    <|> (attempt do
      let t ← type
      skipString "/*"
      let params ← parameters
      return (t, "*", params))
    <|> (do
      let t ← type
      skipChar '/'
      let s ← subtype
      let params ← parameters
      return (t, s, params))

@[always_inline, specialize]
def qvalue : m String := do
  (attempt do
      skipChar '0'
      let frac ← optional do
        skipChar '.'
        let ds ← takeUpTo 3 DIGIT
        return "." ++ chars_to_string ds
      return "0" ++ frac.getD "")
    <|> (do
      skipChar '1'
      let frac ← optional do
        skipChar '.'
        let ds ← takeUpTo 3 (pchar '0')
        return "." ++ chars_to_string ds
      return "1" ++ frac.getD "")

@[always_inline, specialize]
def weight : m String := do
  _ ← OWS
  skipChar ';'
  _ ← OWS
  skipString "q="
  qvalue

@[always_inline, specialize]
def method_list : m (Array String) := comma_list method

@[inline, specialize]
def accept : m (Array (MediaRange × Option String)) := do
  let item : m (MediaRange × Option String) := do
    let mr ← media_range
    let wt? ← optional weight
    return (mr, wt?)
  comma_list item

@[inline, specialize]
def accept_charset : m (Array (String × Option String)) := do
  let item : m (String × Option String) := do
    let cs ← token <|> pstring "*"
    let wt? ← optional weight
    return (cs, wt?)
  comma_list item

@[always_inline, specialize]
def content_coding : m String := token

@[inline, specialize]
def codings : m String := content_coding <|> pstring "identity" <|> pstring "*"

@[inline, specialize]
def accept_encoding : m (Array (String × Option String)) := do
  let item : m (String × Option String) := do
    let c ← codings
    let wt? ← optional weight
    return (c, wt?)
  comma_list item

@[inline, specialize]
def accept_language : m (Array (String × Option String)) := do
  let item : m (String × Option String) := do
    let lr ← language_range
    let wt? ← optional weight
    return (lr, wt?)
  comma_list item

@[always_inline, specialize]
def range_unit : m String := token

@[inline, specialize]
def acceptable_ranges : m (Array String) := comma_list range_unit

@[always_inline, specialize]
def allow : m (Array String) := comma_list method

@[always_inline, specialize]
def auth_scheme : m String := token

@[always_inline, specialize]
def auth_param : m Parameter := do
  let name ← token
  _ ← BWS
  skipChar '='
  _ ← BWS
  let value ← token <|> quoted_string
  return (name, value)

@[inline, specialize]
def auth_param_list : m (Array Parameter) := comma_list auth_param

@[inline, specialize]
def challenge : m (String × Option (Sum String (Array Parameter))) := do
  let scheme ← auth_scheme
  let data? ← optional do
    _ ← many1Chars SP
    (attempt (Sum.inl <$> token68)) <|> (Sum.inr <$> auth_param_list)
  return (scheme, data?)

@[inline, specialize]
def credentials : m (String × Option (Sum String (Array Parameter))) := do
  let scheme ← auth_scheme
  let data? ← optional do
    _ ← many1Chars SP
    (attempt (Sum.inl <$> token68)) <|> (Sum.inr <$> auth_param_list)
  return (scheme, data?)

@[inline, specialize]
def authentication_info : m (Array Parameter) := auth_param_list

@[always_inline, specialize]
def authorization : m (String × Option (Sum String (Array Parameter))) := credentials

@[always_inline, specialize]
def connection_option : m String := token

@[always_inline, specialize]
def connection : m (Array String) := comma_list connection_option

@[always_inline, specialize]
def content_encoding : m (Array String) := comma_list content_coding

@[always_inline, specialize]
def content_language : m (Array String) := comma_list language_tag

@[always_inline, specialize]
def content_length : m Nat := decimal_nat

@[always_inline, specialize]
def absolute_URI : m Uri := absolute_uri

@[always_inline, specialize]
def partial_URI : m Uri := Uri.Parser.partial_uri

@[always_inline, specialize]
def content_location : m Uri := absolute_URI <|> partial_URI

@[always_inline, specialize]
def complete_length : m String := many1Chars DIGIT

@[inline, specialize]
def incl_range : m String := do
  let first ← many1Chars DIGIT
  skipChar '-'
  let last ← many1Chars DIGIT
  return first ++ "-" ++ last

@[inline, specialize]
def range_resp : m String := do
  let range ← incl_range
  skipChar '/'
  let tail ← (attempt (pchar '*' *> pure "*")) <|> complete_length
  return range ++ "/" ++ tail

@[inline, specialize]
def unsatisfied_range : m String := do
  skipString "*/"
  let len ← complete_length
  return "*/" ++ len

@[inline, specialize]
def content_range : m String := do
  let unit ← range_unit
  SP'
  let spec ← range_resp <|> unsatisfied_range
  return unit ++ " " ++ spec

@[always_inline, specialize]
def content_type : m MediaType := media_type

@[always_inline, specialize]
def GMT : m String := pstring "GMT"

@[inline, specialize]
def day_name : m String :=
  pstring "Mon" <|> pstring "Tue" <|> pstring "Wed" <|> pstring "Thu" <|> pstring "Fri" <|> pstring "Sat" <|> pstring "Sun"

@[inline, specialize]
def day_name_l : m String :=
  pstring "Monday" <|> pstring "Tuesday" <|> pstring "Wednesday" <|> pstring "Thursday" <|> pstring "Friday" <|> pstring "Saturday" <|> pstring "Sunday"

@[inline, specialize]
def month : m String :=
  pstring "Jan" <|> pstring "Feb" <|> pstring "Mar" <|> pstring "Apr" <|> pstring "May" <|> pstring "Jun" <|> pstring "Jul" <|> pstring "Aug" <|> pstring "Sep" <|> pstring "Oct" <|> pstring "Nov" <|> pstring "Dec"

@[always_inline, specialize]
def day : m String := chars_to_string <$> takeN 2 DIGIT

@[always_inline, specialize]
def year : m String := chars_to_string <$> takeN 4 DIGIT

@[always_inline, specialize]
def hour : m String := chars_to_string <$> takeN 2 DIGIT

@[always_inline, specialize]
def minute : m String := chars_to_string <$> takeN 2 DIGIT

@[always_inline, specialize]
def second : m String := chars_to_string <$> takeN 2 DIGIT

@[inline, specialize]
def time_of_day : m String := do
  let h ← hour
  skipChar ':'
  let m ← minute
  skipChar ':'
  let s ← second
  return s!"{h}:{m}:{s}"

@[inline, specialize]
def date1 : m String := do
  let d ← day
  SP'
  let m ← month
  SP'
  let y ← year
  return s!"{d} {m} {y}"

@[inline, specialize]
def date2 : m String := do
  let d ← day
  skipChar '-'
  let m ← month
  skipChar '-'
  let y ← chars_to_string <$> takeN 2 DIGIT
  return s!"{d}-{m}-{y}"

@[inline, specialize]
def date3 : m String := do
  let m ← month
  SP'
  let d ← (attempt (chars_to_string <$> takeN 2 DIGIT)) <|> (do skipChar ' '; char_to_string <$> DIGIT)
  return s!"{m} {d}"

@[inline, specialize]
def IMF_fixdate : m String := do
  let dn ← day_name
  skipChar ','
  SP'
  let d1 ← date1
  SP'
  let tod ← time_of_day
  SP'
  let gmt ← GMT
  return s!"{dn}, {d1} {tod} {gmt}"

@[inline, specialize]
def rfc850_date : m String := do
  let dn ← day_name_l
  skipChar ','
  SP'
  let d2 ← date2
  SP'
  let tod ← time_of_day
  SP'
  let gmt ← GMT
  return s!"{dn}, {d2} {tod} {gmt}"

@[inline, specialize]
def asctime_date : m String := do
  let dn ← day_name
  SP'
  let d3 ← date3
  SP'
  let tod ← time_of_day
  SP'
  let y ← year
  return s!"{dn} {d3} {tod} {y}"

@[inline, specialize]
def obs_date : m String := rfc850_date <|> asctime_date

@[always_inline, specialize]
def HTTP_date : m String := IMF_fixdate <|> obs_date

@[always_inline, specialize]
def date : m String := HTTP_date

@[always_inline, specialize]
def etagc : m Char := satisfy fun c =>
  c == '!' || ('\x23' ≤ c && c ≤ '\x7E') || ('\x80' ≤ c && c ≤ '\xFF')

@[inline, specialize]
def opaque_tag : m String := do
  _ ← DQUOTE
  let cs ← manyChars etagc
  _ ← DQUOTE
  return s!"\"{cs}\""

@[always_inline, specialize]
def weak : m String := pstring "W/"

@[inline, specialize]
def entity_tag : m String := do
  let w? ← optional weak
  let tag ← opaque_tag
  return w?.getD "" ++ tag

@[always_inline, specialize]
def etag : m String := entity_tag

@[inline, specialize]
def expectation : m (String × Option (String × Parameters)) := do
  let name ← token
  let tail? ← optional do
    skipChar '='
    let value ← token <|> quoted_string
    let params ← parameters
    return (value, params)
  return (name, tail?)

@[inline, specialize]
def expect : m (Array (String × Option (String × Parameters))) := comma_list expectation

@[always_inline, specialize]
def from_ : m String := mailbox

@[inline, specialize]
def uri_host : m Uri.Host := Uri.Parser.uri_host

@[inline, specialize]
def host : m (Uri.Host × Option UInt16) := do
  let h ← uri_host
  let p? ← optional (attempt (skipChar ':' *> Uri.Parser.port))
  return (h, p?)

@[always_inline, specialize]
def http_uri : m Uri := Uri.Parser.http_uri

@[always_inline, specialize]
def https_uri : m Uri := Uri.Parser.https_uri

@[inline, specialize]
def if_match : m (Option (Array String)) := do
  (attempt (pchar '*' *> pure none)) <|> (some <$> comma_list entity_tag)

@[always_inline, specialize]
def if_modified_since : m String := HTTP_date

@[inline, specialize]
def if_none_match : m (Option (Array String)) := do
  (attempt (pchar '*' *> pure none)) <|> (some <$> comma_list entity_tag)

@[inline, specialize]
def if_range : m String := entity_tag <|> HTTP_date

@[always_inline, specialize]
def if_unmodified_since : m String := HTTP_date

@[always_inline, specialize]
def last_modified : m String := HTTP_date

@[always_inline, specialize]
def location : m Uri := Uri.Parser.uri_reference

@[always_inline, specialize]
def max_forwards : m Nat := decimal_nat

@[inline, specialize]
def proxy_authenticate : m (Array (String × Option (Sum String (Array Parameter)))) := comma_list challenge

@[always_inline, specialize]
def proxy_authentication_info : m (Array Parameter) := auth_param_list

@[always_inline, specialize]
def proxy_authorization : m (String × Option (Sum String (Array Parameter))) := credentials

@[inline, specialize]
def first_pos : m String := many1Chars DIGIT

@[inline, specialize]
def last_pos : m String := many1Chars DIGIT

@[inline, specialize]
def int_range : m String := do
  let first ← first_pos
  skipChar '-'
  let last? ← optional last_pos
  return match last? with
    | none => first ++ "-"
    | some last => first ++ "-" ++ last

@[inline, specialize]
def suffix_length : m String := many1Chars DIGIT

@[inline, specialize]
def suffix_range : m String := do
  skipChar '-'
  let len ← suffix_length
  return "-" ++ len

@[inline, specialize]
def other_range : m String := do
  let cs ← many1Chars <| satisfy fun c =>
    ('\x21' ≤ c && c ≤ '\x2B') || ('\x2D' ≤ c && c ≤ '\x7E')
  return cs

@[inline, specialize]
def range_spec : m String := int_range <|> suffix_range <|> other_range

@[inline, specialize]
def range_set : m (Array String) := comma_list range_spec

@[inline, specialize]
def ranges_specifier : m (String × Array String) := do
  let unit ← range_unit
  skipChar '='
  let rs ← range_set
  return (unit, rs)

@[always_inline, specialize]
def range : m (String × Array String) := ranges_specifier

@[always_inline, specialize]
def absolute_path : m String := Uri.Parser.absolute_path

@[always_inline, specialize]
def partial_uri : m Uri := Uri.Parser.partial_uri

@[always_inline, specialize]
def referer : m Uri := absolute_URI <|> partial_uri

@[always_inline, specialize]
def delay_seconds : m Nat := decimal_nat

@[always_inline, specialize]
def retry_after : m String := HTTP_date <|> (toString <$> delay_seconds)

@[inline, specialize]
def product : m (String × Option String) := do
  let name ← token
  let ver? ← optional do
    skipChar '/'
    token
  return (name, ver?)

@[always_inline, specialize]
def product_version : m String := token

@[always_inline, specialize]
def protocol_name : m String := token

@[always_inline, specialize]
def protocol_version : m String := token

@[inline, specialize]
def protocol : m (String × Option String) := do
  let name ← protocol_name
  let ver? ← optional do
    skipChar '/'
    protocol_version
  return (name, ver?)

@[always_inline, specialize]
def received_by : m (String × Option UInt16) := do
  let name ← token
  let port? ← optional (attempt (skipChar ':' *> Uri.Parser.port))
  return (name, port?)

@[inline, specialize]
def received_protocol : m (Option String × String) := do
  let prefix? ← optional (attempt (protocol_name <* skipChar '/'))
  let ver ← protocol_version
  return (prefix?, ver)

@[always_inline, specialize]
def pseudonym : m String := token

@[inline, specialize]
def server : m (String × Array String) := do
  let first ← product
  let firstStr := match first with
    | (n, none) => n
    | (n, some v) => s!"{n}/{v}"
  let rest ← many (RWS *> (attempt (do
    let p ← product
    return match p with
      | (n, none) => n
      | (n, some v) => s!"{n}/{v}") <|> comment))
  return (firstStr, rest)

@[inline, specialize]
def user_agent : m (String × Array String) := do
  let first ← product
  let firstStr := match first with
    | (n, none) => n
    | (n, some v) => s!"{n}/{v}"
  let rest ← many (RWS *> (attempt (do
    let p ← product
    return match p with
      | (n, none) => n
      | (n, some v) => s!"{n}/{v}") <|> comment))
  return (firstStr, rest)

@[inline, specialize]
def transfer_parameter : m Parameter := do
  let name ← token
  _ ← BWS
  skipChar '='
  _ ← BWS
  let value ← token <|> quoted_string
  return (name, value)

@[inline, specialize]
def transfer_coding : m (String × Array Parameter) := do
  let name ← token
  let params ← many (OWS *> skipChar ';' *> OWS *> transfer_parameter)
  return (name, params)

@[inline, specialize]
def t_codings : m (String × Array Parameter × Option String) := do
  (attempt (pstring "trailers" *> pure ("trailers", #[], none)))
    <|> (do
      let (name, params) ← transfer_coding
      let wt? ← optional weight
      return (name, params, wt?))

@[inline, specialize]
def TE : m (Array (String × Array Parameter × Option String)) := comma_list t_codings

@[always_inline, specialize]
def trailer : m (Array String) := comma_list field_name

@[inline, specialize]
def transfer_encoding : m (Array (String × Array Parameter)) := comma_list transfer_coding

@[inline, specialize]
def upgrade : m (Array (String × Option String)) := comma_list protocol

@[inline, specialize]
def vary : m (Array String) := do
  let item := (pstring "*" <|> field_name)
  comma_list item

@[inline, specialize]
def via : m (Array (Option String × String × (String × Option UInt16) × Option String)) := do
  let item : m (Option String × String × (String × Option UInt16) × Option String) := do
    let (pn?, pv) ← received_protocol
    _ ← RWS
    let rb ← received_by
    let comment? ← optional (RWS *> comment)
    return (pn?, pv, rb, comment?)
  comma_list item

@[inline, specialize]
def www_authenticate : m (Array (String × Option (Sum String (Array Parameter)))) := comma_list challenge

@[always_inline, specialize]
def uri_reference : m Uri := Uri.Parser.uri_reference

@[inline, specialize]
def start_line : m StartLine :=
  attempt (request_line <&> StartLine.request)
  <|> (status_line <&> StartLine.status)

@[always_inline, specialize]
def message_body : m String := manyChars OCTET

@[inline, specialize]
def http_message : m HttpMessage := do
  let start ← start_line
  CRLF
  let fields ← many (field_line <* CRLF)
  CRLF
  let body ← message_body
  let body? := if body.isEmpty then none else some body
  return { start_line := start, fields, body? }

@[inline, specialize]
def chunk_size : m Nat := hex_nat

@[inline, specialize]
def chunk_ext_name : m String := token

@[inline, specialize]
def chunk_ext_val : m String := token <|> quoted_string

@[inline, specialize]
def chunk_ext : m (Array ChunkExt) := do
  let mut xs := #[]
  repeat
    if let some name ← optional (attempt (BWS *> skipChar ';' *> BWS *> chunk_ext_name)) then
      let value? ← optional (attempt (BWS *> skipChar '=' *> BWS *> chunk_ext_val))
      xs := xs.push { name, value? }
    else break
  return xs

@[inline, specialize]
def chunk_data : m String := many1Chars OCTET

@[inline, specialize]
def chunk : m Chunk := do
  let size ← chunk_size
  let ext ← chunk_ext
  CRLF
  let data ← chunk_data
  CRLF
  return { size, ext, data }

@[inline, specialize]
def last_chunk : m (Array ChunkExt) := do
  _ ← many1Chars (pchar '0')
  let ext ← chunk_ext
  CRLF
  return ext

@[inline, specialize]
def trailer_section : m (Array FieldLine) := many (field_line <* CRLF)

@[inline, specialize]
def chunked_body : m ChunkedBody := do
  let chunks ← many chunk
  _ ← last_chunk
  let trailer ← trailer_section
  CRLF
  return { chunks, trailer }

end Http.Http1_1.Parser
