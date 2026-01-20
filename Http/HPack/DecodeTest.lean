import Http.HPack.Decode
import Http.HPack.Encode

open Http.HPack
open Binary

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

def testIntegerEncoding : Bool :=
  let ex1 := encodePrefixedInteger 5 0 10
  let ex2 := encodePrefixedInteger 5 0 1337
  let ex3 := encodePrefixedInteger 8 0 42
  ex1 == ByteArray.mk #[0x0a] &&
    ex2 == ByteArray.mk #[0x1f, 0x9a, 0x0a] &&
    ex3 == ByteArray.mk #[0x2a]

def bytesC21 : ByteArray :=
  ByteArray.mk #[
    0x40, 0x0a,
    0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x2d, 0x6b, 0x65, 0x79,
    0x0d,
    0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x2d, 0x68, 0x65, 0x61, 0x64, 0x65, 0x72
  ]

def headersC21 : List HeaderField :=
  [{ name := ba "custom-key", value := ba "custom-header" }]

def testDecodeC21 : Bool :=
  match decodeHeaderBlockBytes bytesC21 with
  | .ok (hs, t) => hs == headersC21 && t.entries == headersC21
  | .error _ => false

def bytesC22 : ByteArray :=
  ByteArray.mk #[
    0x04, 0x0c,
    0x2f, 0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2f, 0x70, 0x61, 0x74, 0x68
  ]

def headersC22 : List HeaderField :=
  [{ name := ba ":path", value := ba "/sample/path" }]

def testDecodeC22 : Bool :=
  match decodeHeaderBlockBytes bytesC22 with
  | .ok (hs, t) => hs == headersC22 && t.entries == []
  | .error _ => false

def bytesC23 : ByteArray :=
  ByteArray.mk #[
    0x10, 0x08,
    0x70, 0x61, 0x73, 0x73, 0x77, 0x6f, 0x72, 0x64,
    0x06,
    0x73, 0x65, 0x63, 0x72, 0x65, 0x74
  ]

def headersC23 : List HeaderField :=
  [{ name := ba "password", value := ba "secret" }]

def testDecodeC23 : Bool :=
  match decodeHeaderBlockBytes bytesC23 with
  | .ok (hs, t) => hs == headersC23 && t.entries == []
  | .error _ => false

def bytesC24 : ByteArray := ByteArray.mk #[0x82]

def headersC24 : List HeaderField :=
  [{ name := ba ":method", value := ba "GET" }]

def testDecodeC24 : Bool :=
  match decodeHeaderBlockBytes bytesC24 with
  | .ok (hs, t) => hs == headersC24 && t.entries == []
  | .error _ => false

def headersReq1 : List HeaderField :=
  [
    { name := ba ":method", value := ba "GET" },
    { name := ba ":scheme", value := ba "http" },
    { name := ba ":path", value := ba "/" },
    { name := ba ":authority", value := ba "www.example.com" }
  ]

def headersReq2 : List HeaderField :=
  headersReq1 ++ [{ name := ba "cache-control", value := ba "no-cache" }]

def headersReq3 : List HeaderField :=
  [
    { name := ba ":method", value := ba "GET" },
    { name := ba ":scheme", value := ba "https" },
    { name := ba ":path", value := ba "/index.html" },
    { name := ba ":authority", value := ba "www.example.com" },
    { name := ba "custom-key", value := ba "custom-value" }
  ]

def bytesReq1 : ByteArray :=
  ByteArray.mk #[
    0x82, 0x86, 0x84, 0x41, 0x0f,
    0x77, 0x77, 0x77, 0x2e, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d
  ]

def bytesReq2 : ByteArray :=
  ByteArray.mk #[
    0x82, 0x86, 0x84, 0xbe, 0x58, 0x08,
    0x6e, 0x6f, 0x2d, 0x63, 0x61, 0x63, 0x68, 0x65
  ]

def bytesReq3 : ByteArray :=
  ByteArray.mk #[
    0x82, 0x87, 0x85, 0xbf, 0x40, 0x0a,
    0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x2d, 0x6b, 0x65, 0x79, 0x0c,
    0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x2d, 0x76, 0x61, 0x6c, 0x75, 0x65
  ]

def testEncodeRequestsNoHuffman : Bool :=
  let (b1, t1) := encodeHeaderBlockFrom (DynamicTable.empty 4096) headersReq1 false
  let (b2, t2) := encodeHeaderBlockFrom t1 headersReq2 false
  let (b3, _) := encodeHeaderBlockFrom t2 headersReq3 false
  b1 == bytesReq1 && b2 == bytesReq2 && b3 == bytesReq3

def decodeWith (t : DynamicTable) (bytes : ByteArray) :
    Except DecodeError (List HeaderField × DynamicTable) :=
  DecodeResult.toExcept <| (decodeHeaderBlockAux t).run bytes

def testDecodeRequestsNoHuffman : Bool :=
  match decodeWith (DynamicTable.empty 4096) bytesReq1 with
  | .error _ => false
  | .ok (hs1, t1) =>
      let ok1 := hs1 == headersReq1 &&
        t1.entries == [{ name := ba ":authority", value := ba "www.example.com" }]
      match decodeWith t1 bytesReq2 with
      | .error _ => false
      | .ok (hs2, t2) =>
          let ok2 := hs2 == headersReq2 &&
            t2.entries ==
              [
                { name := ba "cache-control", value := ba "no-cache" },
                { name := ba ":authority", value := ba "www.example.com" }
              ]
          match decodeWith t2 bytesReq3 with
          | .error _ => false
          | .ok (hs3, t3) =>
              let ok3 := hs3 == headersReq3 &&
                t3.entries ==
                  [
                    { name := ba "custom-key", value := ba "custom-value" },
                    { name := ba "cache-control", value := ba "no-cache" },
                    { name := ba ":authority", value := ba "www.example.com" }
                  ]
              ok1 && ok2 && ok3

def bytesReq1Huffman : ByteArray :=
  ByteArray.mk #[
    0x82, 0x86, 0x84, 0x41, 0x8c,
    0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff
  ]

def testEncodeRequestHuffman : Bool :=
  let (b1, _) := encodeHeaderBlockFrom (DynamicTable.empty 4096) headersReq1 true
  b1 == bytesReq1Huffman

def testDecodeRequestHuffman : Bool :=
  match decodeHeaderBlockBytes bytesReq1Huffman with
  | .ok (hs, _) => hs == headersReq1
  | .error _ => false

def testHuffmanRoundtrip : Bool :=
  let input := ba "www.example.com"
  match decodeHuffman (encodeHuffman input) with
  | .ok out => out == input
  | .error _ => false

def testRoundtrip : Bool :=
  match decodeHeaderBlockBytes (encodeHeaderBlockBytes expected) with
  | .ok (hs, _) => hs == expected
  | .error _ => false

#eval testDecode
#eval testIntegerEncoding
#eval testDecodeC21
#eval testDecodeC22
#eval testDecodeC23
#eval testDecodeC24
#eval testEncodeRequestsNoHuffman
#eval testDecodeRequestsNoHuffman
#eval testEncodeRequestHuffman
#eval testDecodeRequestHuffman
#eval testHuffmanRoundtrip
#eval testRoundtrip
