module

public import Binary
public import Http.Http1_1.Wire
public import Http.Uri
public import Http.Parser.Util
public import Http.Parser.LanguageRange
public import Http.Parser.LanguageTag
public import Http.Parser.Mailbox

public section

namespace Http.Http1_1.Parser

open Binary UTF8
open Http.Parser
open Uri.Parser

@[always_inline]
def http_name : Get String := pstring "HTTP"

private def decode_dec! : Char → Nat := fun c =>
  if c.isDigit then c.toNat - '0'.toNat
  else panic! "invalid decimal character"

@[always_inline]
def http_version : Get Version := do
  _ ← http_name
  skipChar '/'
  let x ← decode_dec! <$> satisfy Char.isDigit
  skipChar '.'
  let y ← decode_dec! <$> satisfy Char.isDigit
  return { major := x, minor := y }

@[inline]
def tchar : Get Char := do
  satisfy fun c => c.isDigit || c.isAlpha ||
    c matches '!' | '#' | '$' | '%' | '&' | '\'' | '*' |
      '+' | '-' | '.' | '^' | '_' | '`' | '|' | '~'

@[always_inline]
def token : Get String := many1Chars tchar

@[always_inline]
def method : Get String := token

@[always_inline]
def origin_form : Get (String × Option String) := do
  let path ← Uri.Parser.absolute_path
  let query? ← optional do
    skipChar '?'
    query
  return (path, query?)

@[always_inline]
def absolute_form : Get Uri := absolute_uri

@[always_inline]
def authority_form : Get Uri.Authority := do
  let host ← host
  skipChar ':'
  let port ← Uri.Parser.port
  return { userInfo? := none, host, port? := some port }

@[always_inline]
def asterisk_form : Get Char := pchar '*'

@[always_inline]
def SP' : Get Unit := skipChar ' '

@[always_inline]
def HTAB' : Get Unit := skipChar '\t'

@[inline]
def request_target : Get RequestTarget :=
  (origin_form >>= fun (path, query?) => return RequestTarget.origin path query?)
  <|> (absolute_form <&> RequestTarget.absolute)
  <|> (authority_form <&> RequestTarget.authority)
  <|> (asterisk_form *> pure RequestTarget.asterisk)

@[inline]
def request_line : Get RequestLine := do
  let method ← method
  SP'
  let request_target ← request_target
  SP'
  let version ← http_version
  return { method, request_target, version }

@[inline]
def status_code : Get Nat := do
  let a ← decode_dec! <$> satisfy Char.isDigit
  let b ← decode_dec! <$> satisfy Char.isDigit
  let c ← decode_dec! <$> satisfy Char.isDigit
  return a * 100 + b * 10 + c

@[always_inline]
def reason_phrase : Get String :=
  many1Chars <| HTAB <|> SP <|> vchar <|> obs_text

@[inline]
def status_line : Get StatusLine := do
  let version ← http_version
  SP'
  let status_code ← status_code
  SP'
  let reason? ← optional reason_phrase
  return { version, status_code, reason? }

@[always_inline]
def OWS : Get String := manyChars <| SP <|> HTAB

@[always_inline]
def RWS : Get String := many1Chars <| SP <|> HTAB

@[always_inline]
def BWS : Get String := OWS

@[always_inline]
def field_name : Get String := token

@[always_inline]
def field_vchar : Get Char := vchar <|> obs_text

@[inline]
partial def field_content : Get String := do
  let first ← field_vchar
  let tail ← optional do
    let xs ← many1Chars <| SP <|> HTAB <|> field_vchar -- TODO: field-content is not LL, find a solution.
    let last := String.back xs
    if last matches ' ' | '\t' then
      fail "field-content must end with field-vchar"
    return xs
  return tail.map (fun t => first.toString ++ t) |>.getD first.toString

@[always_inline]
def field_value : Get (Array String) := many field_content

@[inline]
def field_line : Get FieldLine := do
  let name ← field_name
  skipChar ':'
  _ ← OWS
  let value ← field_value
  _ ← OWS
  return { name, value }

@[inline]
private def decimal_nat : Get Nat := do
  let s ← many1Chars DIGIT
  let xs := s.toList.map fun c => c.toNat - '0'.toNat
  let x :: xs := xs | unreachable!
  return xs.foldl (init := x) fun acc t => acc * 10 + t

private def decode_hex! : Char → Nat := fun c =>
  if c.isDigit then c.toNat - '0'.toNat
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else panic! "invalid hex character"

@[inline]
private def hex_nat : Get Nat := do
  let s ← many1Chars HEXDIG
  let xs := s.toList.map decode_hex!
  let x :: xs := xs | unreachable!
  return xs.foldl (init := x) fun acc t => acc * 16 + t

@[inline, specialize]
private def comma_list (p : Get α) : Get (Array α) := do
  let first? ← optional (p)
  match first? with
  | none => return #[]
  | some first =>
    let mut xs := #[first]
    repeat
      if let some x ← optional ((OWS *> skipChar ',' *> OWS *> p)) then
        xs := xs.push x
      else break
    return xs

@[inline, specialize]
private def sp_list (p : Get α) : Get (Array α) := do
  let first? ← optional (p)
  match first? with
  | none => return #[]
  | some first =>
    let mut xs := #[first]
    repeat
      if let some x ← optional ((RWS *> p)) then
        xs := xs.push x
      else break
    return xs

@[always_inline]
def obs_fold : Get String := do
  let pre ← OWS
  CRLF
  let post ← RWS
  return pre ++ "\r\n" ++ post

@[always_inline]
def token68 : Get String := do
  let head ← many1Chars <| satisfy fun c =>
    c.isAlpha || c.isDigit || c matches '-' | '.' | '_' | '~' | '+' | '/'
  let pad ← manyChars (pchar '=')
  return head ++ pad

@[always_inline]
def qdtext : Get Char := satisfy fun c =>
  c == '\t' || c == '!' || c == ' ' ||
    ('\x23' ≤ c && c ≤ '\x5B') ||
    ('\x5D' ≤ c && c ≤ '\x7E') ||
    ('\x80' ≤ c && c ≤ '\xFF')

@[always_inline]
def quoted_pair : Get String := do
  skipChar '\\'
  let c ← HTAB <|> SP <|> vchar <|> obs_text
  return "\\" ++ c.toString

@[always_inline]
def quoted_string : Get String := do
  _ ← DQUOTE
  let parts ← many <| (char_to_string <$> qdtext) <|> quoted_pair
  _ ← DQUOTE
  return String.intercalate "" parts.toList

@[always_inline]
def ctext : Get Char := satisfy fun c =>
  c == '\t' || c == ' ' ||
    ('\x21' ≤ c && c ≤ '\x27') ||
    ('\x2A' ≤ c && c ≤ '\x5B') ||
    ('\x5D' ≤ c && c ≤ '\x7E') ||
    ('\x80' ≤ c && c ≤ '\xFF')

partial def comment : Get String := do
  skipChar '('
  let parts ← many <| comment <|> quoted_pair <|> (char_to_string <$> ctext)
  skipChar ')'
  return "(" ++ String.intercalate "" parts.toList ++ ")"

@[always_inline]
def parameter_name : Get String := token

@[always_inline]
def parameter_value : Get String := token <|> quoted_string

@[always_inline]
def parameter : Get Parameter := do
  let name ← parameter_name
  skipChar '='
  let value ← parameter_value
  return (name, value)

@[inline]
def parameters : Get Parameters := do
  let mut xs := #[]
  repeat
    if let some v ← optional ((OWS *> skipChar ';' *> OWS *> optional parameter)) then
      xs := xs.push v
    else break
  return xs

@[always_inline]
def type : Get String := token

@[always_inline]
def subtype : Get String := token

@[inline]
def media_type : Get MediaType := do
  let t ← type
  skipChar '/'
  let s ← subtype
  let params ← parameters
  return (t, s, params)

@[inline]
def media_range : Get MediaRange := do
  (do
      skipString "*/*"
      let params ← parameters
      return ("*", "*", params))
    <|> (do
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

@[always_inline]
private def chars_to_string : Array Char → String := fun x => String.ofList x.toList

@[inline]
def qvalue : Get String := do
  (do
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

@[always_inline]
def weight : Get String := do
  _ ← OWS
  skipChar ';'
  _ ← OWS
  skipString "q="
  qvalue

@[always_inline]
def method_list : Get (Array String) := comma_list method

@[inline]
def accept : Get (Array (MediaRange × Option String)) := do
  let item : Get (MediaRange × Option String) := do
    let mr ← media_range
    let wt? ← optional weight
    return (mr, wt?)
  comma_list item

@[inline]
def accept_charset : Get (Array (String × Option String)) := do
  let item : Get (String × Option String) := do
    let cs ← token <|> pstring "*"
    let wt? ← optional weight
    return (cs, wt?)
  comma_list item

@[always_inline]
def content_coding : Get String := token

@[inline]
def codings : Get String := content_coding <|> pstring "identity" <|> pstring "*"

@[inline]
def accept_encoding : Get (Array (String × Option String)) := do
  let item : Get (String × Option String) := do
    let c ← codings
    let wt? ← optional weight
    return (c, wt?)
  comma_list item

@[inline]
def accept_language : Get (Array (String × Option String)) := do
  let item : Get (String × Option String) := do
    let lr ← language_range
    let wt? ← optional weight
    return (lr, wt?)
  comma_list item

@[always_inline]
def range_unit : Get String := token

@[inline]
def acceptable_ranges : Get (Array String) := comma_list range_unit

@[always_inline]
def allow : Get (Array String) := comma_list method

@[always_inline]
def auth_scheme : Get String := token

@[always_inline]
def auth_param : Get Parameter := do
  let name ← token
  _ ← BWS
  skipChar '='
  _ ← BWS
  let value ← token <|> quoted_string
  return (name, value)

@[inline]
def auth_param_list : Get (Array Parameter) := comma_list auth_param

@[inline]
def challenge : Get (String × Option (Sum String (Array Parameter))) := do
  let scheme ← auth_scheme
  let data? ← optional do
    _ ← many1Chars SP
    ((Sum.inl <$> token68)) <|> (Sum.inr <$> auth_param_list)
  return (scheme, data?)

@[inline]
def credentials : Get (String × Option (Sum String (Array Parameter))) := do
  let scheme ← auth_scheme
  let data? ← optional do
    _ ← many1Chars SP
    ((Sum.inl <$> token68)) <|> (Sum.inr <$> auth_param_list)
  return (scheme, data?)

@[inline]
def authentication_info : Get (Array Parameter) := auth_param_list

@[always_inline]
def authorization : Get (String × Option (Sum String (Array Parameter))) := credentials

@[always_inline]
def connection_option : Get String := token

@[always_inline]
def connection : Get (Array String) := comma_list connection_option

@[always_inline]
def content_encoding : Get (Array String) := comma_list content_coding

@[always_inline]
def content_language : Get (Array String) := comma_list language_tag

@[always_inline]
def content_length : Get Nat := decimal_nat

@[always_inline]
def absolute_URI : Get Uri := absolute_uri

@[always_inline]
def partial_URI : Get Uri := Uri.Parser.partial_uri

@[always_inline]
def content_location : Get Uri := absolute_URI <|> partial_URI

@[always_inline]
def complete_length : Get String := many1Chars DIGIT

@[inline]
def incl_range : Get String := do
  let first ← many1Chars DIGIT
  skipChar '-'
  let last ← many1Chars DIGIT
  return first ++ "-" ++ last

@[inline]
def range_resp : Get String := do
  let range ← incl_range
  skipChar '/'
  let tail ← ((pchar '*' *> pure "*")) <|> complete_length
  return range ++ "/" ++ tail

@[inline]
def unsatisfied_range : Get String := do
  skipString "*/"
  let len ← complete_length
  return "*/" ++ len

@[inline]
def content_range : Get String := do
  let unit ← range_unit
  SP'
  let spec ← range_resp <|> unsatisfied_range
  return unit ++ " " ++ spec

@[always_inline]
def content_type : Get MediaType := media_type

@[always_inline]
def GMT : Get String := pstring "GMT"

@[inline]
def day_name : Get String :=
  pstring "Mon" <|> pstring "Tue" <|> pstring "Wed" <|> pstring "Thu" <|> pstring "Fri" <|> pstring "Sat" <|> pstring "Sun"

@[inline]
def day_name_l : Get String :=
  pstring "Monday" <|> pstring "Tuesday" <|> pstring "Wednesday" <|> pstring "Thursday" <|> pstring "Friday" <|> pstring "Saturday" <|> pstring "Sunday"

@[inline]
def month : Get String :=
  pstring "Jan" <|> pstring "Feb" <|> pstring "Mar" <|> pstring "Apr" <|> pstring "May" <|> pstring "Jun" <|> pstring "Jul" <|> pstring "Aug" <|> pstring "Sep" <|> pstring "Oct" <|> pstring "Nov" <|> pstring "Dec"

@[always_inline]
def day : Get String := chars_to_string <$> takeN 2 DIGIT

@[always_inline]
def year : Get String := chars_to_string <$> takeN 4 DIGIT

@[always_inline]
def hour : Get String := chars_to_string <$> takeN 2 DIGIT

@[always_inline]
def minute : Get String := chars_to_string <$> takeN 2 DIGIT

@[always_inline]
def second : Get String := chars_to_string <$> takeN 2 DIGIT

@[inline]
def time_of_day : Get String := do
  let h ← hour
  skipChar ':'
  let m ← minute
  skipChar ':'
  let s ← second
  return s!"{h}:{m}:{s}"

@[inline]
def date1 : Get String := do
  let d ← day
  SP'
  let m ← month
  SP'
  let y ← year
  return s!"{d} {m} {y}"

@[inline]
def date2 : Get String := do
  let d ← day
  skipChar '-'
  let m ← month
  skipChar '-'
  let y ← chars_to_string <$> takeN 2 DIGIT
  return s!"{d}-{m}-{y}"

@[inline]
def date3 : Get String := do
  let m ← month
  SP'
  let d ← ((chars_to_string <$> takeN 2 DIGIT)) <|> (do skipChar ' '; char_to_string <$> DIGIT)
  return s!"{m} {d}"

@[inline]
def IMF_fixdate : Get String := do
  let dn ← day_name
  skipChar ','
  SP'
  let d1 ← date1
  SP'
  let tod ← time_of_day
  SP'
  let gmt ← GMT
  return s!"{dn}, {d1} {tod} {gmt}"

@[inline]
def rfc850_date : Get String := do
  let dn ← day_name_l
  skipChar ','
  SP'
  let d2 ← date2
  SP'
  let tod ← time_of_day
  SP'
  let gmt ← GMT
  return s!"{dn}, {d2} {tod} {gmt}"

@[inline]
def asctime_date : Get String := do
  let dn ← day_name
  SP'
  let d3 ← date3
  SP'
  let tod ← time_of_day
  SP'
  let y ← year
  return s!"{dn} {d3} {tod} {y}"

@[inline]
def obs_date : Get String := rfc850_date <|> asctime_date

@[always_inline]
def HTTP_date : Get String := IMF_fixdate <|> obs_date

@[always_inline]
def date : Get String := HTTP_date

@[always_inline]
def etagc : Get Char := satisfy fun c =>
  c == '!' || ('\x23' ≤ c && c ≤ '\x7E') || ('\x80' ≤ c && c ≤ '\xFF')

@[inline]
def opaque_tag : Get String := do
  _ ← DQUOTE
  let cs ← manyChars etagc
  _ ← DQUOTE
  return s!"\"{cs}\""

@[always_inline]
def weak : Get String := pstring "W/"

@[inline]
def entity_tag : Get String := do
  let w? ← optional weak
  let tag ← opaque_tag
  return w?.getD "" ++ tag

@[always_inline]
def etag : Get String := entity_tag

@[inline]
def expectation : Get (String × Option (String × Parameters)) := do
  let name ← token
  let tail? ← optional do
    skipChar '='
    let value ← token <|> quoted_string
    let params ← parameters
    return (value, params)
  return (name, tail?)

@[inline]
def expect : Get (Array (String × Option (String × Parameters))) := comma_list expectation

@[always_inline]
def from_ : Get String := mailbox

@[inline]
def uri_host : Get Uri.Host := Uri.Parser.uri_host

@[inline]
def host : Get (Uri.Host × Option UInt16) := do
  let h ← uri_host
  let p? ← optional ((skipChar ':' *> Uri.Parser.port))
  return (h, p?)

@[always_inline]
def http_uri : Get Uri := Uri.Parser.http_uri

@[always_inline]
def https_uri : Get Uri := Uri.Parser.https_uri

@[inline]
def if_match : Get (Option (Array String)) := do
  ((pchar '*' *> pure none)) <|> (some <$> comma_list entity_tag)

@[always_inline]
def if_modified_since : Get String := HTTP_date

@[inline]
def if_none_match : Get (Option (Array String)) := do
  ((pchar '*' *> pure none)) <|> (some <$> comma_list entity_tag)

@[inline]
def if_range : Get String := entity_tag <|> HTTP_date

@[always_inline]
def if_unmodified_since : Get String := HTTP_date

@[always_inline]
def last_modified : Get String := HTTP_date

@[always_inline]
def location : Get Uri := Uri.Parser.uri_reference

@[always_inline]
def max_forwards : Get Nat := decimal_nat

@[inline]
def proxy_authenticate : Get (Array (String × Option (Sum String (Array Parameter)))) := comma_list challenge

@[always_inline]
def proxy_authentication_info : Get (Array Parameter) := auth_param_list

@[always_inline]
def proxy_authorization : Get (String × Option (Sum String (Array Parameter))) := credentials

@[inline]
def first_pos : Get String := many1Chars DIGIT

@[inline]
def last_pos : Get String := many1Chars DIGIT

@[inline]
def int_range : Get String := do
  let first ← first_pos
  skipChar '-'
  let last? ← optional last_pos
  return match last? with
    | none => first ++ "-"
    | some last => first ++ "-" ++ last

@[inline]
def suffix_length : Get String := many1Chars DIGIT

@[inline]
def suffix_range : Get String := do
  skipChar '-'
  let len ← suffix_length
  return "-" ++ len

@[inline]
def other_range : Get String := do
  let cs ← many1Chars <| satisfy fun c =>
    ('\x21' ≤ c && c ≤ '\x2B') || ('\x2D' ≤ c && c ≤ '\x7E')
  return cs

@[inline]
def range_spec : Get String := int_range <|> suffix_range <|> other_range

@[inline]
def range_set : Get (Array String) := comma_list range_spec

@[inline]
def ranges_specifier : Get (String × Array String) := do
  let unit ← range_unit
  skipChar '='
  let rs ← range_set
  return (unit, rs)

@[always_inline]
def range : Get (String × Array String) := ranges_specifier

@[always_inline]
def absolute_path : Get String := Uri.Parser.absolute_path

@[always_inline]
def partial_uri : Get Uri := Uri.Parser.partial_uri

@[always_inline]
def referer : Get Uri := absolute_URI <|> partial_uri

@[always_inline]
def delay_seconds : Get Nat := decimal_nat

@[always_inline]
def retry_after : Get String := HTTP_date <|> (toString <$> delay_seconds)

@[inline]
def product : Get (String × Option String) := do
  let name ← token
  let ver? ← optional do
    skipChar '/'
    token
  return (name, ver?)

@[always_inline]
def product_version : Get String := token

@[always_inline]
def protocol_name : Get String := token

@[always_inline]
def protocol_version : Get String := token

@[inline]
def protocol : Get (String × Option String) := do
  let name ← protocol_name
  let ver? ← optional do
    skipChar '/'
    protocol_version
  return (name, ver?)

@[always_inline]
def received_by : Get (String × Option UInt16) := do
  let name ← token
  let port? ← optional ((skipChar ':' *> Uri.Parser.port))
  return (name, port?)

@[inline]
def received_protocol : Get (Option String × String) := do
  let prefix? ← optional ((protocol_name <* skipChar '/'))
  let ver ← protocol_version
  return (prefix?, ver)

@[always_inline]
def pseudonym : Get String := token

@[inline]
def server : Get (String × Array String) := do
  let first ← product
  let firstStr := match first with
    | (n, none) => n
    | (n, some v) => s!"{n}/{v}"
  let rest ← many (RWS *> ((do
    let p ← product
    return match p with
      | (n, none) => n
      | (n, some v) => s!"{n}/{v}") <|> comment))
  return (firstStr, rest)

@[inline]
def user_agent : Get (String × Array String) := do
  let first ← product
  let firstStr := match first with
    | (n, none) => n
    | (n, some v) => s!"{n}/{v}"
  let rest ← many (RWS *> ((do
    let p ← product
    return match p with
      | (n, none) => n
      | (n, some v) => s!"{n}/{v}") <|> comment))
  return (firstStr, rest)

@[inline]
def transfer_parameter : Get Parameter := do
  let name ← token
  _ ← BWS
  skipChar '='
  _ ← BWS
  let value ← token <|> quoted_string
  return (name, value)

@[inline]
def transfer_coding : Get (String × Array Parameter) := do
  let name ← token
  let params ← many (OWS *> skipChar ';' *> OWS *> transfer_parameter)
  return (name, params)

@[inline]
def t_codings : Get (String × Array Parameter × Option String) := do
  ((pstring "trailers" *> pure ("trailers", #[], none)))
    <|> (do
      let (name, params) ← transfer_coding
      let wt? ← optional weight
      return (name, params, wt?))

@[inline]
def TE : Get (Array (String × Array Parameter × Option String)) := comma_list t_codings

@[always_inline]
def trailer : Get (Array String) := comma_list field_name

@[inline]
def transfer_encoding : Get (Array (String × Array Parameter)) := comma_list transfer_coding

@[inline]
def upgrade : Get (Array (String × Option String)) := comma_list protocol

@[inline]
def vary : Get (Array String) := do
  let item := (pstring "*" <|> field_name)
  comma_list item

@[inline]
def via : Get (Array (Option String × String × (String × Option UInt16) × Option String)) := do
  let item : Get (Option String × String × (String × Option UInt16) × Option String) := do
    let (pn?, pv) ← received_protocol
    _ ← RWS
    let rb ← received_by
    let comment? ← optional (RWS *> comment)
    return (pn?, pv, rb, comment?)
  comma_list item

@[inline]
def www_authenticate : Get (Array (String × Option (Sum String (Array Parameter)))) := comma_list challenge

@[always_inline]
def uri_reference : Get Uri := Uri.Parser.uri_reference

@[inline]
def start_line : Get StartLine :=
  (request_line <&> StartLine.request)
  <|> (status_line <&> StartLine.status)

@[always_inline]
def chunk_size : Get Nat := hex_nat

@[always_inline]
def chunk_ext_name : Get String := token

@[always_inline]
def chunk_ext_val : Get String := token <|> quoted_string

@[inline]
def chunk_ext : Get (Array ChunkExt) := many do
  _ ← BWS
  skipChar ';'
  _ ← BWS
  let name ← chunk_ext_name
  let value? ← optional do
    _ ← BWS
    skipChar '='
    _ ← BWS
    chunk_ext_val
  return { name, value? }

@[inline]
def chunk : Get Chunk := do
  let size ← chunk_size
  let ext ← chunk_ext
  CRLF
  let data ← get_bytes size
  CRLF
  return { size, ext, data }

@[inline]
def last_chunk : Get Chunk := do
  _ ← many1 (satisfy fun x => x == '0')
  let ext ← chunk_ext
  CRLF
  return { size := 0, ext, data := {} }

@[always_inline]
def trailer_section : Get (Array FieldLine) := many (field_line <* CRLF)

@[inline]
def chunked_body : Get ChunkedBody := do
  let chunks ← many <| pending do
    chunk <* shrink -- shrink to drop parsed chunks from inner buffer
  pending do
  let lastChunk ← last_chunk
  pending do
  let trailer ← trailer_section
  CRLF
  return { chunks, lastChunk, trailer }

@[inline]
def http_message_header : Get HttpMessageHeader := do
  let start ← start_line
  pending do -- checkpoint
  CRLF
  let fields ← many <| pending (field_line <* CRLF) -- checkpoints
  CRLF
  return { start_line := start, fields }

end Http.Http1_1.Parser
