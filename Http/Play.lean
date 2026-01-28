module

import Std
public import Http.Http1_1.Parser
public import Http.Surface
import all Http.Client

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

open Std.Internal.Parsec Std.Internal.Parsec.String in

section

namespace Http.Http1_1

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


def t : IO Unit := do
  let resp ← f.wait
  println! "{resp}"
--   let resp := Http.Http1_1.Parser.http_message (m := Parser) |>.run resp
--   println! "{repr resp}"
-- #eval t

instance : Repr (ByteArray) where
  reprPrec x _ := s!"{repr x.data}"

deriving instance Repr for Response

def r : IO Unit := do
  let client := HttpClient.mkTCP "127.0.0.1" 8000 .http1_1
  let resp ← client.get "/"
  match resp with
  | Except.error e => println! "error: {e}"
  | .ok r =>
    -- println! "{repr r}"
    let body := r.body?.map String.fromUTF8?
    let body := body.join
    println! "{body}"

#eval r
