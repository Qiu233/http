module

public import Binary
public import Std

public section

namespace Http.HPack

open Binary

structure HeaderField where
  name : ByteArray
  value : ByteArray
deriving BEq

@[inline]
def HeaderField.size (h : HeaderField) : Nat :=
  h.name.size + h.value.size + 32

structure DynamicTable where
  entries : List HeaderField
  size : Nat
  maxSize : Nat
  allowedMax : Nat

@[inline]
def DynamicTable.empty (maxSize : Nat := 4096) : DynamicTable :=
  { entries := [], size := 0, maxSize, allowedMax := maxSize }

def List.popLast : List α → Option (List α × α)
  | [] => none
  | [x] => some ([], x)
  | x :: xs =>
      match List.popLast xs with
      | none => none
      | some (init, last) => some (x :: init, last)

partial def DynamicTable.evict (t : DynamicTable) : DynamicTable :=
  if t.size <= t.maxSize then
    t
  else
    match List.popLast t.entries with
    | none => { t with entries := [], size := 0 }
    | some (init, last) =>
        let t' := { t with entries := init, size := t.size - last.size }
        t'.evict

def DynamicTable.add (h : HeaderField) (t : DynamicTable) : DynamicTable :=
  let entrySize := h.size
  if entrySize > t.maxSize then
    { t with entries := [], size := 0 }
  else
    let t' := { t with entries := h :: t.entries, size := t.size + entrySize }
    t'.evict

@[inline]
def u8 (n : Nat) : UInt8 := UInt8.ofNat n

@[inline]
def u32 (n : Nat) : UInt32 := UInt32.ofNat n

@[inline]
def ba (s : String) : ByteArray := s.toUTF8

def staticTable : Array HeaderField := #[
  ⟨ba ":authority", ba ""⟩,
  ⟨ba ":method", ba "GET"⟩,
  ⟨ba ":method", ba "POST"⟩,
  ⟨ba ":path", ba "/"⟩,
  ⟨ba ":path", ba "/index.html"⟩,
  ⟨ba ":scheme", ba "http"⟩,
  ⟨ba ":scheme", ba "https"⟩,
  ⟨ba ":status", ba "200"⟩,
  ⟨ba ":status", ba "204"⟩,
  ⟨ba ":status", ba "206"⟩,
  ⟨ba ":status", ba "304"⟩,
  ⟨ba ":status", ba "400"⟩,
  ⟨ba ":status", ba "404"⟩,
  ⟨ba ":status", ba "500"⟩,
  ⟨ba "accept-charset", ba ""⟩,
  ⟨ba "accept-encoding", ba "gzip, deflate"⟩,
  ⟨ba "accept-language", ba ""⟩,
  ⟨ba "accept-ranges", ba ""⟩,
  ⟨ba "accept", ba ""⟩,
  ⟨ba "access-control-allow-origin", ba ""⟩,
  ⟨ba "age", ba ""⟩,
  ⟨ba "allow", ba ""⟩,
  ⟨ba "authorization", ba ""⟩,
  ⟨ba "cache-control", ba ""⟩,
  ⟨ba "content-disposition", ba ""⟩,
  ⟨ba "content-encoding", ba ""⟩,
  ⟨ba "content-language", ba ""⟩,
  ⟨ba "content-length", ba ""⟩,
  ⟨ba "content-location", ba ""⟩,
  ⟨ba "content-range", ba ""⟩,
  ⟨ba "content-type", ba ""⟩,
  ⟨ba "cookie", ba ""⟩,
  ⟨ba "date", ba ""⟩,
  ⟨ba "etag", ba ""⟩,
  ⟨ba "expect", ba ""⟩,
  ⟨ba "expires", ba ""⟩,
  ⟨ba "from", ba ""⟩,
  ⟨ba "host", ba ""⟩,
  ⟨ba "if-match", ba ""⟩,
  ⟨ba "if-modified-since", ba ""⟩,
  ⟨ba "if-none-match", ba ""⟩,
  ⟨ba "if-range", ba ""⟩,
  ⟨ba "if-unmodified-since", ba ""⟩,
  ⟨ba "last-modified", ba ""⟩,
  ⟨ba "link", ba ""⟩,
  ⟨ba "location", ba ""⟩,
  ⟨ba "max-forwards", ba ""⟩,
  ⟨ba "proxy-authenticate", ba ""⟩,
  ⟨ba "proxy-authorization", ba ""⟩,
  ⟨ba "range", ba ""⟩,
  ⟨ba "referer", ba ""⟩,
  ⟨ba "refresh", ba ""⟩,
  ⟨ba "retry-after", ba ""⟩,
  ⟨ba "server", ba ""⟩,
  ⟨ba "set-cookie", ba ""⟩,
  ⟨ba "strict-transport-security", ba ""⟩,
  ⟨ba "transfer-encoding", ba ""⟩,
  ⟨ba "user-agent", ba ""⟩,
  ⟨ba "vary", ba ""⟩,
  ⟨ba "via", ba ""⟩,
  ⟨ba "www-authenticate", ba ""⟩
]

def listGet1? : List α → Nat → Option α
  | [], _ => none
  | x :: _, 1 => some x
  | _ :: xs, n + 1 => listGet1? xs n
  | _, 0 => none

def lookupHeader (t : DynamicTable) (idx : Nat) : Option HeaderField :=
  let staticSize := staticTable.size
  if idx == 0 then
    none
  else if idx <= staticSize then
    staticTable[(idx - 1)]?
  else
    let dynIdx := idx - staticSize
    listGet1? t.entries dynIdx

structure HuffmanEntry where
  code : UInt32
  bits : Nat
  sym : Option UInt8

def huffmanTable : Array HuffmanEntry := #[
  ⟨u32 0x1ff8, 13, some (u8 0)⟩,
  ⟨u32 0x7fffd8, 23, some (u8 1)⟩,
  ⟨u32 0xfffffe2, 28, some (u8 2)⟩,
  ⟨u32 0xfffffe3, 28, some (u8 3)⟩,
  ⟨u32 0xfffffe4, 28, some (u8 4)⟩,
  ⟨u32 0xfffffe5, 28, some (u8 5)⟩,
  ⟨u32 0xfffffe6, 28, some (u8 6)⟩,
  ⟨u32 0xfffffe7, 28, some (u8 7)⟩,
  ⟨u32 0xfffffe8, 28, some (u8 8)⟩,
  ⟨u32 0xffffea, 24, some (u8 9)⟩,
  ⟨u32 0x3ffffffc, 30, some (u8 10)⟩,
  ⟨u32 0xfffffe9, 28, some (u8 11)⟩,
  ⟨u32 0xfffffea, 28, some (u8 12)⟩,
  ⟨u32 0x3ffffffd, 30, some (u8 13)⟩,
  ⟨u32 0xfffffeb, 28, some (u8 14)⟩,
  ⟨u32 0xfffffec, 28, some (u8 15)⟩,
  ⟨u32 0xfffffed, 28, some (u8 16)⟩,
  ⟨u32 0xfffffee, 28, some (u8 17)⟩,
  ⟨u32 0xfffffef, 28, some (u8 18)⟩,
  ⟨u32 0xffffff0, 28, some (u8 19)⟩,
  ⟨u32 0xffffff1, 28, some (u8 20)⟩,
  ⟨u32 0xffffff2, 28, some (u8 21)⟩,
  ⟨u32 0x3ffffffe, 30, some (u8 22)⟩,
  ⟨u32 0xffffff3, 28, some (u8 23)⟩,
  ⟨u32 0xffffff4, 28, some (u8 24)⟩,
  ⟨u32 0xffffff5, 28, some (u8 25)⟩,
  ⟨u32 0xffffff6, 28, some (u8 26)⟩,
  ⟨u32 0xffffff7, 28, some (u8 27)⟩,
  ⟨u32 0xffffff8, 28, some (u8 28)⟩,
  ⟨u32 0xffffff9, 28, some (u8 29)⟩,
  ⟨u32 0xffffffa, 28, some (u8 30)⟩,
  ⟨u32 0xffffffb, 28, some (u8 31)⟩,
  ⟨u32 0x14, 6, some (u8 32)⟩,
  ⟨u32 0x3f8, 10, some (u8 33)⟩,
  ⟨u32 0x3f9, 10, some (u8 34)⟩,
  ⟨u32 0xffa, 12, some (u8 35)⟩,
  ⟨u32 0x1ff9, 13, some (u8 36)⟩,
  ⟨u32 0x15, 6, some (u8 37)⟩,
  ⟨u32 0xf8, 8, some (u8 38)⟩,
  ⟨u32 0x7fa, 11, some (u8 39)⟩,
  ⟨u32 0x3fa, 10, some (u8 40)⟩,
  ⟨u32 0x3fb, 10, some (u8 41)⟩,
  ⟨u32 0xf9, 8, some (u8 42)⟩,
  ⟨u32 0x7fb, 11, some (u8 43)⟩,
  ⟨u32 0xfa, 8, some (u8 44)⟩,
  ⟨u32 0x16, 6, some (u8 45)⟩,
  ⟨u32 0x17, 6, some (u8 46)⟩,
  ⟨u32 0x18, 6, some (u8 47)⟩,
  ⟨u32 0x0, 5, some (u8 48)⟩,
  ⟨u32 0x1, 5, some (u8 49)⟩,
  ⟨u32 0x2, 5, some (u8 50)⟩,
  ⟨u32 0x19, 6, some (u8 51)⟩,
  ⟨u32 0x1a, 6, some (u8 52)⟩,
  ⟨u32 0x1b, 6, some (u8 53)⟩,
  ⟨u32 0x1c, 6, some (u8 54)⟩,
  ⟨u32 0x1d, 6, some (u8 55)⟩,
  ⟨u32 0x1e, 6, some (u8 56)⟩,
  ⟨u32 0x1f, 6, some (u8 57)⟩,
  ⟨u32 0x5c, 7, some (u8 58)⟩,
  ⟨u32 0xfb, 8, some (u8 59)⟩,
  ⟨u32 0x7ffc, 15, some (u8 60)⟩,
  ⟨u32 0x20, 6, some (u8 61)⟩,
  ⟨u32 0xffb, 12, some (u8 62)⟩,
  ⟨u32 0x3fc, 10, some (u8 63)⟩,
  ⟨u32 0x1ffa, 13, some (u8 64)⟩,
  ⟨u32 0x21, 6, some (u8 65)⟩,
  ⟨u32 0x5d, 7, some (u8 66)⟩,
  ⟨u32 0x5e, 7, some (u8 67)⟩,
  ⟨u32 0x5f, 7, some (u8 68)⟩,
  ⟨u32 0x60, 7, some (u8 69)⟩,
  ⟨u32 0x61, 7, some (u8 70)⟩,
  ⟨u32 0x62, 7, some (u8 71)⟩,
  ⟨u32 0x63, 7, some (u8 72)⟩,
  ⟨u32 0x64, 7, some (u8 73)⟩,
  ⟨u32 0x65, 7, some (u8 74)⟩,
  ⟨u32 0x66, 7, some (u8 75)⟩,
  ⟨u32 0x67, 7, some (u8 76)⟩,
  ⟨u32 0x68, 7, some (u8 77)⟩,
  ⟨u32 0x69, 7, some (u8 78)⟩,
  ⟨u32 0x6a, 7, some (u8 79)⟩,
  ⟨u32 0x6b, 7, some (u8 80)⟩,
  ⟨u32 0x6c, 7, some (u8 81)⟩,
  ⟨u32 0x6d, 7, some (u8 82)⟩,
  ⟨u32 0x6e, 7, some (u8 83)⟩,
  ⟨u32 0x6f, 7, some (u8 84)⟩,
  ⟨u32 0x70, 7, some (u8 85)⟩,
  ⟨u32 0x71, 7, some (u8 86)⟩,
  ⟨u32 0x72, 7, some (u8 87)⟩,
  ⟨u32 0xfc, 8, some (u8 88)⟩,
  ⟨u32 0x73, 7, some (u8 89)⟩,
  ⟨u32 0xfd, 8, some (u8 90)⟩,
  ⟨u32 0x1ffb, 13, some (u8 91)⟩,
  ⟨u32 0x7fff0, 19, some (u8 92)⟩,
  ⟨u32 0x1ffc, 13, some (u8 93)⟩,
  ⟨u32 0x3ffc, 14, some (u8 94)⟩,
  ⟨u32 0x22, 6, some (u8 95)⟩,
  ⟨u32 0x7ffd, 15, some (u8 96)⟩,
  ⟨u32 0x3, 5, some (u8 97)⟩,
  ⟨u32 0x23, 6, some (u8 98)⟩,
  ⟨u32 0x4, 5, some (u8 99)⟩,
  ⟨u32 0x24, 6, some (u8 100)⟩,
  ⟨u32 0x5, 5, some (u8 101)⟩,
  ⟨u32 0x25, 6, some (u8 102)⟩,
  ⟨u32 0x26, 6, some (u8 103)⟩,
  ⟨u32 0x27, 6, some (u8 104)⟩,
  ⟨u32 0x6, 5, some (u8 105)⟩,
  ⟨u32 0x74, 7, some (u8 106)⟩,
  ⟨u32 0x75, 7, some (u8 107)⟩,
  ⟨u32 0x28, 6, some (u8 108)⟩,
  ⟨u32 0x29, 6, some (u8 109)⟩,
  ⟨u32 0x2a, 6, some (u8 110)⟩,
  ⟨u32 0x7, 5, some (u8 111)⟩,
  ⟨u32 0x2b, 6, some (u8 112)⟩,
  ⟨u32 0x76, 7, some (u8 113)⟩,
  ⟨u32 0x2c, 6, some (u8 114)⟩,
  ⟨u32 0x8, 5, some (u8 115)⟩,
  ⟨u32 0x9, 5, some (u8 116)⟩,
  ⟨u32 0x2d, 6, some (u8 117)⟩,
  ⟨u32 0x77, 7, some (u8 118)⟩,
  ⟨u32 0x78, 7, some (u8 119)⟩,
  ⟨u32 0x79, 7, some (u8 120)⟩,
  ⟨u32 0x7a, 7, some (u8 121)⟩,
  ⟨u32 0x7b, 7, some (u8 122)⟩,
  ⟨u32 0x7ffe, 15, some (u8 123)⟩,
  ⟨u32 0x7fc, 11, some (u8 124)⟩,
  ⟨u32 0x3ffd, 14, some (u8 125)⟩,
  ⟨u32 0x1ffd, 13, some (u8 126)⟩,
  ⟨u32 0xffffffc, 28, some (u8 127)⟩,
  ⟨u32 0xfffe6, 20, some (u8 128)⟩,
  ⟨u32 0x3fffd2, 22, some (u8 129)⟩,
  ⟨u32 0xfffe7, 20, some (u8 130)⟩,
  ⟨u32 0xfffe8, 20, some (u8 131)⟩,
  ⟨u32 0x3fffd3, 22, some (u8 132)⟩,
  ⟨u32 0x3fffd4, 22, some (u8 133)⟩,
  ⟨u32 0x3fffd5, 22, some (u8 134)⟩,
  ⟨u32 0x7fffd9, 23, some (u8 135)⟩,
  ⟨u32 0x3fffd6, 22, some (u8 136)⟩,
  ⟨u32 0x7fffda, 23, some (u8 137)⟩,
  ⟨u32 0x7fffdb, 23, some (u8 138)⟩,
  ⟨u32 0x7fffdc, 23, some (u8 139)⟩,
  ⟨u32 0x7fffdd, 23, some (u8 140)⟩,
  ⟨u32 0x7fffde, 23, some (u8 141)⟩,
  ⟨u32 0xffffeb, 24, some (u8 142)⟩,
  ⟨u32 0x7fffdf, 23, some (u8 143)⟩,
  ⟨u32 0xffffec, 24, some (u8 144)⟩,
  ⟨u32 0xffffed, 24, some (u8 145)⟩,
  ⟨u32 0x3fffd7, 22, some (u8 146)⟩,
  ⟨u32 0x7fffe0, 23, some (u8 147)⟩,
  ⟨u32 0xffffee, 24, some (u8 148)⟩,
  ⟨u32 0x7fffe1, 23, some (u8 149)⟩,
  ⟨u32 0x7fffe2, 23, some (u8 150)⟩,
  ⟨u32 0x7fffe3, 23, some (u8 151)⟩,
  ⟨u32 0x7fffe4, 23, some (u8 152)⟩,
  ⟨u32 0x1fffdc, 21, some (u8 153)⟩,
  ⟨u32 0x3fffd8, 22, some (u8 154)⟩,
  ⟨u32 0x7fffe5, 23, some (u8 155)⟩,
  ⟨u32 0x3fffd9, 22, some (u8 156)⟩,
  ⟨u32 0x7fffe6, 23, some (u8 157)⟩,
  ⟨u32 0x7fffe7, 23, some (u8 158)⟩,
  ⟨u32 0xffffef, 24, some (u8 159)⟩,
  ⟨u32 0x3fffda, 22, some (u8 160)⟩,
  ⟨u32 0x1fffdd, 21, some (u8 161)⟩,
  ⟨u32 0xfffe9, 20, some (u8 162)⟩,
  ⟨u32 0x3fffdb, 22, some (u8 163)⟩,
  ⟨u32 0x3fffdc, 22, some (u8 164)⟩,
  ⟨u32 0x7fffe8, 23, some (u8 165)⟩,
  ⟨u32 0x7fffe9, 23, some (u8 166)⟩,
  ⟨u32 0x1fffde, 21, some (u8 167)⟩,
  ⟨u32 0x7fffea, 23, some (u8 168)⟩,
  ⟨u32 0x3fffdd, 22, some (u8 169)⟩,
  ⟨u32 0x3fffde, 22, some (u8 170)⟩,
  ⟨u32 0xfffff0, 24, some (u8 171)⟩,
  ⟨u32 0x1fffdf, 21, some (u8 172)⟩,
  ⟨u32 0x3fffdf, 22, some (u8 173)⟩,
  ⟨u32 0x7fffeb, 23, some (u8 174)⟩,
  ⟨u32 0x7fffec, 23, some (u8 175)⟩,
  ⟨u32 0x1fffe0, 21, some (u8 176)⟩,
  ⟨u32 0x1fffe1, 21, some (u8 177)⟩,
  ⟨u32 0x3fffe0, 22, some (u8 178)⟩,
  ⟨u32 0x1fffe2, 21, some (u8 179)⟩,
  ⟨u32 0x7fffed, 23, some (u8 180)⟩,
  ⟨u32 0x3fffe1, 22, some (u8 181)⟩,
  ⟨u32 0x7fffee, 23, some (u8 182)⟩,
  ⟨u32 0x7fffef, 23, some (u8 183)⟩,
  ⟨u32 0xfffea, 20, some (u8 184)⟩,
  ⟨u32 0x3fffe2, 22, some (u8 185)⟩,
  ⟨u32 0x3fffe3, 22, some (u8 186)⟩,
  ⟨u32 0x3fffe4, 22, some (u8 187)⟩,
  ⟨u32 0x7ffff0, 23, some (u8 188)⟩,
  ⟨u32 0x3fffe5, 22, some (u8 189)⟩,
  ⟨u32 0x3fffe6, 22, some (u8 190)⟩,
  ⟨u32 0x7ffff1, 23, some (u8 191)⟩,
  ⟨u32 0x3ffffe0, 26, some (u8 192)⟩,
  ⟨u32 0x3ffffe1, 26, some (u8 193)⟩,
  ⟨u32 0xfffeb, 20, some (u8 194)⟩,
  ⟨u32 0x7fff1, 19, some (u8 195)⟩,
  ⟨u32 0x3fffe7, 22, some (u8 196)⟩,
  ⟨u32 0x7ffff2, 23, some (u8 197)⟩,
  ⟨u32 0x3fffe8, 22, some (u8 198)⟩,
  ⟨u32 0x1ffffec, 25, some (u8 199)⟩,
  ⟨u32 0x3ffffe2, 26, some (u8 200)⟩,
  ⟨u32 0x3ffffe3, 26, some (u8 201)⟩,
  ⟨u32 0x3ffffe4, 26, some (u8 202)⟩,
  ⟨u32 0x7ffffde, 27, some (u8 203)⟩,
  ⟨u32 0x7ffffdf, 27, some (u8 204)⟩,
  ⟨u32 0x3ffffe5, 26, some (u8 205)⟩,
  ⟨u32 0xfffff1, 24, some (u8 206)⟩,
  ⟨u32 0x1ffffed, 25, some (u8 207)⟩,
  ⟨u32 0x7fff2, 19, some (u8 208)⟩,
  ⟨u32 0x1fffe3, 21, some (u8 209)⟩,
  ⟨u32 0x3ffffe6, 26, some (u8 210)⟩,
  ⟨u32 0x7ffffe0, 27, some (u8 211)⟩,
  ⟨u32 0x7ffffe1, 27, some (u8 212)⟩,
  ⟨u32 0x3ffffe7, 26, some (u8 213)⟩,
  ⟨u32 0x7ffffe2, 27, some (u8 214)⟩,
  ⟨u32 0xfffff2, 24, some (u8 215)⟩,
  ⟨u32 0x1fffe4, 21, some (u8 216)⟩,
  ⟨u32 0x1fffe5, 21, some (u8 217)⟩,
  ⟨u32 0x3ffffe8, 26, some (u8 218)⟩,
  ⟨u32 0x3ffffe9, 26, some (u8 219)⟩,
  ⟨u32 0xffffffd, 28, some (u8 220)⟩,
  ⟨u32 0x7ffffe3, 27, some (u8 221)⟩,
  ⟨u32 0x7ffffe4, 27, some (u8 222)⟩,
  ⟨u32 0x7ffffe5, 27, some (u8 223)⟩,
  ⟨u32 0xfffec, 20, some (u8 224)⟩,
  ⟨u32 0xfffff3, 24, some (u8 225)⟩,
  ⟨u32 0xfffed, 20, some (u8 226)⟩,
  ⟨u32 0x1fffe6, 21, some (u8 227)⟩,
  ⟨u32 0x3fffe9, 22, some (u8 228)⟩,
  ⟨u32 0x1fffe7, 21, some (u8 229)⟩,
  ⟨u32 0x1fffe8, 21, some (u8 230)⟩,
  ⟨u32 0x7ffff3, 23, some (u8 231)⟩,
  ⟨u32 0x3fffea, 22, some (u8 232)⟩,
  ⟨u32 0x3fffeb, 22, some (u8 233)⟩,
  ⟨u32 0x1ffffee, 25, some (u8 234)⟩,
  ⟨u32 0x1ffffef, 25, some (u8 235)⟩,
  ⟨u32 0xfffff4, 24, some (u8 236)⟩,
  ⟨u32 0xfffff5, 24, some (u8 237)⟩,
  ⟨u32 0x3ffffea, 26, some (u8 238)⟩,
  ⟨u32 0x7ffff4, 23, some (u8 239)⟩,
  ⟨u32 0x3ffffeb, 26, some (u8 240)⟩,
  ⟨u32 0x7ffffe6, 27, some (u8 241)⟩,
  ⟨u32 0x3ffffec, 26, some (u8 242)⟩,
  ⟨u32 0x3ffffed, 26, some (u8 243)⟩,
  ⟨u32 0x7ffffe7, 27, some (u8 244)⟩,
  ⟨u32 0x7ffffe8, 27, some (u8 245)⟩,
  ⟨u32 0x7ffffe9, 27, some (u8 246)⟩,
  ⟨u32 0x7ffffea, 27, some (u8 247)⟩,
  ⟨u32 0x7ffffeb, 27, some (u8 248)⟩,
  ⟨u32 0xffffffe, 28, some (u8 249)⟩,
  ⟨u32 0x7ffffec, 27, some (u8 250)⟩,
  ⟨u32 0x7ffffed, 27, some (u8 251)⟩,
  ⟨u32 0x7ffffee, 27, some (u8 252)⟩,
  ⟨u32 0x7ffffef, 27, some (u8 253)⟩,
  ⟨u32 0x7fffff0, 27, some (u8 254)⟩,
  ⟨u32 0x3ffffee, 26, some (u8 255)⟩,
  ⟨u32 0x3fffffff, 30, none⟩
]

def huffmanLookup (code : UInt32) (bits : Nat) : Option (Option UInt8) :=
  Id.run do
    let mut found : Option (Option UInt8) := none
    for entry in huffmanTable do
      if entry.bits == bits && entry.code == code then
        found := some entry.sym
    return found

def huffmanHasPrefix (code : UInt32) (bits : Nat) : Bool :=
  Id.run do
    let mut ok := false
    for entry in huffmanTable do
      if entry.bits >= bits then
        let shift := entry.bits - bits
        if (entry.code.toNat >>> shift) == code.toNat then
          ok := true
    return ok

def decodeHuffman (bytes : ByteArray) : Except String ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    let mut current : UInt32 := 0
    let mut bits : Nat := 0
    let mut err : Option String := none
    for i in [0:bytes.size] do
      if err.isNone then
        let byte := bytes.get! i
        for j in [0:8] do
          if err.isNone then
            let bit := (byte >>> (7 - UInt8.ofNat j)) &&& 0x01
            current := (current <<< 1) ||| (UInt32.ofNat bit.toNat)
            bits := bits + 1
            match huffmanLookup current bits with
            | some none => err := some "huffman: EOS in data"
            | some (some sym) =>
                out := out.push sym
                current := 0
                bits := 0
            | none =>
                if !huffmanHasPrefix current bits then
                  err := some "huffman: invalid code"
    match err with
    | some msg => return .error msg
    | none =>
        if bits == 0 then
          return .ok out
        else
          let padding := (UInt32.ofNat ((Nat.pow 2 bits) - 1))
          if bits <= 7 && current == padding then
            return .ok out
          else
            return .error "huffman: invalid padding"

partial def getPrefixedInteger (prefixBits : Nat) (first : UInt8) : Get Nat := do
  let maskNat := (Nat.pow 2 prefixBits) - 1
  let mask := UInt8.ofNat maskNat
  let value := (first &&& mask).toNat
  if value < maskNat then
    return value
  else
    let rec loop (acc : Nat) (m : Nat) : Get Nat := do
      let b ← getThe UInt8
      let acc := acc + (((b &&& 0x7f).toNat) <<< m)
      if (b &&& 0x80) == 0 then
        return acc
      else
        loop acc (m + 7)
    loop maskNat 0

def getHpackString : Get ByteArray := do
  let first ← get
  let huffman := (first &&& 0x80) != 0
  let len ← getPrefixedInteger 7 first
  let bytes ← get_bytes len
  if huffman then
    match decodeHuffman bytes with
    | .ok out => return out
    | .error err => throw (.userError err)
  else
    return bytes

def getIndexedName (t : DynamicTable) (idx : Nat) : Get ByteArray := do
  match lookupHeader t idx with
  | some h => return h.name
  | none => throw (.userError s!"invalid header index {idx}")

def decodeHeaderStep (t : DynamicTable) : Get (Option HeaderField × DynamicTable) := do
  let first ← get
  if (first &&& 0x80) != 0 then
    let idx ← getPrefixedInteger 7 first
    match lookupHeader t idx with
    | some h => return (some h, t)
    | none => throw (.userError s!"indexed header out of range {idx}")
  else if (first &&& 0x40) != 0 then
    let nameIndex ← getPrefixedInteger 6 first
    let name ← if nameIndex == 0 then getHpackString else getIndexedName t nameIndex
    let value ← getHpackString
    let h := { name, value }
    let t' := DynamicTable.add h t
    return (some h, t')
  else if (first &&& 0x20) != 0 then
    let newMax ← getPrefixedInteger 5 first
    if newMax > t.allowedMax then
      throw (.userError s!"dynamic table size update too large {newMax}")
    let t' := DynamicTable.evict { t with maxSize := newMax }
    return (none, t')
  else
    let nameIndex ← getPrefixedInteger 4 first
    let name ← if nameIndex == 0 then getHpackString else getIndexedName t nameIndex
    let value ← getHpackString
    let h := { name, value }
    return (some h, t)

partial def decodeHeaderBlockAux (t : DynamicTable) : Get (List HeaderField × DynamicTable) := do
  let rem ← remaining
  if rem == 0 then
    return ([], t)
  else
    let (entry?, t') ← decodeHeaderStep t
    let (rest, t'') ← decodeHeaderBlockAux t'
    match entry? with
    | some entry => return (entry :: rest, t'')
    | none => return (rest, t'')

def decodeHeaderBlock (maxSize : Nat := 4096) : Get (List HeaderField × DynamicTable) := do
  decodeHeaderBlockAux (DynamicTable.empty maxSize)

def decodeHeaderBlockBytes (bytes : ByteArray) (maxSize : Nat := 4096) :
    Except DecodeError (List HeaderField × DynamicTable) :=
  DecodeResult.toExcept <| (decodeHeaderBlock (maxSize := maxSize)).run bytes

end Http.HPack

end
