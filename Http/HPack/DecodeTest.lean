import Http.HPack.Decode

open Http.HPack

def testBytes : ByteArray :=
  ByteArray.mk #[
    0x82,
    0x00, 0x06, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d,
    0x05, 0x76, 0x61, 0x6c, 0x75, 0x65
  ]

def expected : List HeaderField :=
  [
    { name := ba ":method", value := ba "GET" },
    { name := ba "custom", value := ba "value" }
  ]

def testDecode : Bool :=
  match decodeHeaderBlockBytes testBytes with
  | .ok (hs, _) => hs == expected
  | .error _ => false

#eval testDecode
