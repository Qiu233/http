module

public import Binary
public import Http.HPack.Basic

public section

namespace Http.HPack

open Binary

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
