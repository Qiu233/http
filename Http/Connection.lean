module

public import Std
public import Http.Http2.Wire

public section

namespace Http.Connection

inductive Protocol where
  | http1
  | http2
  | unknown
deriving Inhabited, Repr, BEq

inductive Probe where
  | needMore
  | protocol (p : Protocol)
deriving Inhabited, Repr, BEq

@[inline]
def bytesPrefixEq (short long : ByteArray) : Bool :=
  if short.size > long.size then
    false
  else
    Id.run do
      let mut ok := true
      for i in [0:short.size] do
        if ok && short.get! i != long.get! i then
          ok := false
      return ok

@[inline]
def bytesStartsWith (bytes prefix_ : ByteArray) : Bool :=
  bytesPrefixEq prefix_ bytes

def findCrlf? (bytes : ByteArray) : Option Nat :=
  Id.run do
    let mut out : Option Nat := none
    let max := bytes.size
    let mut i := 0
    while i + 1 < max && out.isNone do
      if bytes.get! i == 13 && bytes.get! (i + 1) == 10 then
        out := some i
      i := i + 1
    return out

def hasSubarrayInRange (bytes sub : ByteArray) (stop : Nat) : Bool :=
  if sub.size == 0 then
    true
  else if stop < sub.size then
    false
  else
    Id.run do
      let mut found := false
      let limit := stop + 1 - sub.size
      for i in [0:limit] do
        if !found then
          let mut ok := true
          for j in [0:sub.size] do
            if ok && bytes.get! (i + j) != sub.get! j then
              ok := false
          if ok then
            found := true
      return found

def http1Marker : ByteArray := "HTTP/1.".toUTF8

def probe (bytes : ByteArray) : Probe :=
  let preface := Http.Http2.connectionPreface
  if bytes.size == 0 then
    .needMore
  else if bytes.size < preface.size then
    if bytesPrefixEq bytes preface then
      .needMore
    else
      .protocol .unknown
  else if bytesStartsWith bytes preface then
    .protocol .http2
  else
    match findCrlf? bytes with
    | none => .needMore
    | some idx =>
        if hasSubarrayInRange bytes http1Marker idx then
          .protocol .http1
        else
          .protocol .unknown

end Http.Connection

end
