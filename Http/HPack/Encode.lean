module

public import Std
public import Http.HPack.Basic

public section

namespace Http.HPack

@[inline]
def u64 (n : Nat) : UInt64 := UInt64.ofNat n

@[inline]
def appendBytes (a b : ByteArray) : ByteArray :=
  Id.run do
    let mut out := a
    for i in [0:b.size] do
      out := out.push (b.get! i)
    return out

partial def encodeIntegerAux (value : Nat) (out : ByteArray) : ByteArray :=
  if value >= 128 then
    let byte := UInt8.ofNat ((value % 128) + 128)
    encodeIntegerAux (value / 128) (out.push byte)
  else
    out.push (UInt8.ofNat value)

/-- Encodes an HPACK integer with a given prefix and prefix bits. -/
def encodePrefixedInteger (prefixBits : Nat) (prefix_ : UInt8) (value : Nat) : ByteArray :=
  let maxPrefix := (Nat.pow 2 prefixBits) - 1
  if value < maxPrefix then
    ByteArray.empty.push (prefix_ ||| UInt8.ofNat value)
  else
    let out := ByteArray.empty.push (prefix_ ||| UInt8.ofNat maxPrefix)
    encodeIntegerAux (value - maxPrefix) out

@[inline]
def maskLowBits (bits : Nat) : UInt64 :=
  if bits == 0 then
    0
  else
    u64 ((Nat.pow 2 bits) - 1)

partial def flushBits (out : ByteArray) (buffer : UInt64) (bits : Nat) :
    ByteArray × UInt64 × Nat :=
  if bits < 8 then
    (out, buffer, bits)
  else
    let shift := bits - 8
    let byte := UInt8.ofNat ((buffer.toNat >>> shift) &&& 0xff)
    let buffer := buffer &&& maskLowBits shift
    flushBits (out.push byte) buffer shift

/-- Huffman table indexed by symbol. -/
def huffmanCodes : Array (UInt32 × Nat) :=
  Id.run do
    let mut out := Array.replicate 256 (0, 0)
    for entry in huffmanTable do
      match entry.sym with
      | some b => out := out.set! b.toNat (entry.code, entry.bits)
      | none => pure ()
    return out

/-- Encodes bytes using the HPACK static Huffman code. -/
def encodeHuffman (bytes : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    let mut buffer : UInt64 := 0
    let mut bits : Nat := 0
    for i in [0:bytes.size] do
      let b := bytes.get! i
      let (code, nbits) := huffmanCodes[b.toNat]!
      if bits + nbits > 56 then
        let (out', buffer', bits') := flushBits out buffer bits
        out := out'
        buffer := buffer'
        bits := bits'
      buffer := (buffer <<< UInt64.ofNat nbits) ||| (u64 code.toNat)
      bits := bits + nbits
    let padBits := (8 - (bits % 8)) % 8
    if padBits != 0 then
      buffer := (buffer <<< UInt64.ofNat padBits) ||| (u64 ((Nat.pow 2 padBits) - 1))
      bits := bits + padBits
    let (out', _, _) := flushBits out buffer bits
    return out'

/-- Encodes a string literal, using Huffman when it shortens the result. -/
def encodeHpackString (bytes : ByteArray) (useHuffman : Bool := true) : ByteArray :=
  let huff := encodeHuffman bytes
  let useH := useHuffman && huff.size < bytes.size
  let payload := if useH then huff else bytes
  let prefix_ := if useH then (0x80 : UInt8) else 0
  let lenBytes := encodePrefixedInteger 7 prefix_ payload.size
  appendBytes lenBytes payload

@[inline]
def encodeIndexed (idx : Nat) : ByteArray :=
  encodePrefixedInteger 7 0x80 idx

@[inline]
def listFindIndex1? (xs : List α) (p : α → Bool) : Option Nat :=
  let rec loop (xs : List α) (n : Nat) :=
    match xs with
    | [] => none
    | x :: rest =>
        if p x then
          some n
        else
          loop rest (n + 1)
  loop xs 1

@[inline]
def arrayFindIndex? [Inhabited α] (xs : Array α) (p : α → Bool) : Option Nat :=
  Id.run do
    let mut found : Option Nat := none
    for i in [0:xs.size] do
      if found.isNone && p (xs[i]!) then
        found := some i
    return found

/-- Finds a full header match in static or dynamic tables. -/
def findHeaderIndex (t : DynamicTable) (h : HeaderField) : Option Nat :=
  match arrayFindIndex? staticTable (fun s => s == h) with
  | some i => some (i + 1)
  | none =>
      match listFindIndex1? t.entries (fun s => s == h) with
      | some i => some (staticTable.size + i)
      | none => none

/-- Finds a header name match in static or dynamic tables. -/
def findNameIndex (t : DynamicTable) (name : ByteArray) : Option Nat :=
  match arrayFindIndex? staticTable (fun s => s.name == name) with
  | some i => some (i + 1)
  | none =>
      match listFindIndex1? t.entries (fun s => s.name == name) with
      | some i => some (staticTable.size + i)
      | none => none

/-- Encodes a header field and updates the dynamic table if needed. -/
def encodeHeaderField (t : DynamicTable) (h : HeaderField) (useHuffman : Bool := true) :
    ByteArray × DynamicTable :=
  match findHeaderIndex t h with
  | some idx => (encodeIndexed idx, t)
  | none => Id.run do
      let nameIndex :=
        match findNameIndex t h.name with
        | some idx => idx
        | none => 0
      let mut out := encodePrefixedInteger 6 0x40 nameIndex
      if nameIndex == 0 then
        out := appendBytes out (encodeHpackString h.name useHuffman)
      out := appendBytes out (encodeHpackString h.value useHuffman)
      let t' := DynamicTable.add h t
      (out, t')

/-- Encodes a full header block, using incremental indexing for new entries. -/
def encodeHeaderBlockFrom (t : DynamicTable) (headers : List HeaderField)
    (useHuffman : Bool := true) : ByteArray × DynamicTable :=
  let rec loop (hs : List HeaderField) (t : DynamicTable) (out : ByteArray) :=
    match hs with
    | [] => (out, t)
    | h :: rest =>
        let (bytes, t') := encodeHeaderField t h useHuffman
        loop rest t' (appendBytes out bytes)
  loop headers t ByteArray.empty

/-- Encodes a header block with a fresh dynamic table. -/
def encodeHeaderBlock (headers : List HeaderField) (maxSize : Nat := 4096)
    (useHuffman : Bool := true) : ByteArray × DynamicTable :=
  encodeHeaderBlockFrom (DynamicTable.empty maxSize) headers useHuffman

/-- Encodes a header block and returns only the bytes. -/
def encodeHeaderBlockBytes (headers : List HeaderField) (maxSize : Nat := 4096)
    (useHuffman : Bool := true) : ByteArray :=
  (encodeHeaderBlock headers maxSize useHuffman).1

end Http.HPack

end
