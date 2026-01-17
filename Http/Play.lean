import Std
import Http.Parser


-- #check Std.Net
-- #check Std.Internal.IO.Async.TCP.Socket.Client
#check Std.Internal.IO.Async.TCP.Socket.Client



open Std.Internal
open IO.Async
open TCP
open Std.Net

def f : Async String := do
  let sock ← Socket.Client.mk
  try
    let ip := (IPv4Addr.ofString "127.0.0.1").get!
    sock.connect (SocketAddress.v4 (SocketAddressV4.mk ip 8000))
    let req := "GET / HTTP/1.1
Host: 127.0.0.1:8000
Connection: keep-alive
User-Agent: Mozilla/5.0 ...
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
Accept-Encoding: gzip, deflate, br
Accept-Language: en-US,en;q=0.9
Upgrade-Insecure-Requests: 1

"
    sock.send req.toUTF8
    -- sock.keepAlive true 100
    let mut resp := ByteArray.empty
    repeat
      let some data ← sock.recv? 1024 | break
      resp := resp.append data
    return String.fromUTF8! resp
  catch _ => pure ()
  finally
    sock.shutdown
  return ""

-- #eval f.wait
-- #check Async.

open Std.Internal.Parsec Std.Internal.Parsec.String in

section

namespace Http

@[always_inline]
local instance : Uri.Parser.MonadParser Parser where
  satisfy := satisfy
  pchar := pchar
  pstring := pstring
  skipChar := skipChar
  skipString := skipString
  attempt := attempt
  optional := optional
  many := many
  many1 := many1
  manyChars := manyChars
  many1Chars := many1Chars
  fail := fail
  notFollowedBy := notFollowedBy
  peek? := peek?

deriving instance Repr for Std.Net.IPv4Addr
deriving instance Repr for Std.Net.IPv6Addr
deriving instance Repr for Uri.Host
deriving instance Repr for Uri.Authority
deriving instance Repr for Uri
deriving instance Repr for RequestTarget
deriving instance Repr for RequestLine
deriving instance Repr for StartLine
deriving instance Repr for HttpMessage

def s : String := "GET / HTTP/1.1
Host: 127.0.0.1:8000
Connection: keep-alive
User-Agent: Mozilla/5.0 ...
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
Accept-Encoding: gzip, deflate, br
Accept-Language: en-US,en;q=0.9
Upgrade-Insecure-Requests: 1

"

def t := do
  let resp ← f.wait
  let resp := Http.Parser.Http1_1.http_message (m := Parser) |>.run resp
  println! "{repr resp}"

-- #eval Http.Parser.Http1_1.http_message (m := Parser) |>.run s

-- #eval t
