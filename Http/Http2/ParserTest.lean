import Http.Http2.Parser

open Http.Http2
open Http.Http2.Parser
open Binary

def bytesData : ByteArray :=
  ByteArray.mk #[
    0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
    0x68, 0x65, 0x6c, 0x6c, 0x6f
  ]

def bytesHeadersPadded : ByteArray :=
  ByteArray.mk #[
    0x00, 0x00, 0x04, 0x01, 0x08, 0x00, 0x00, 0x00, 0x03,
    0x01, 0x61, 0x62, 0x00
  ]

def bytesSettingsAck : ByteArray :=
  ByteArray.mk #[
    0x00, 0x00, 0x00, 0x04, 0x01, 0x00, 0x00, 0x00, 0x00
  ]

def bytesPingAck : ByteArray :=
  ByteArray.mk #[
    0x00, 0x00, 0x08, 0x06, 0x01, 0x00, 0x00, 0x00, 0x00,
    0xde, 0xad, 0xbe, 0xef, 0x00, 0x01, 0x02, 0x03
  ]

def testData : Bool :=
  match frame_bytes bytesData with
  | .error _ => false
  | .ok f =>
      f.header.length == 5 &&
        f.header.typ == .data &&
        f.header.streamId == 1 &&
        match f.payload with
        | .data df => df.data == "hello".toUTF8 && df.padLength?.isNone
        | _ => false

def testHeadersPadded : Bool :=
  match frame_bytes bytesHeadersPadded with
  | .error _ => false
  | .ok f =>
      f.header.length == 4 &&
        f.header.typ == .headers &&
        f.header.streamId == 3 &&
        match f.payload with
        | .headers hf =>
            hf.padLength? == some 1 &&
              hf.priority?.isNone &&
              hf.headerBlock == "ab".toUTF8
        | _ => false

def testSettingsAck : Bool :=
  match frame_bytes bytesSettingsAck with
  | .error _ => false
  | .ok f =>
      f.header.length == 0 &&
        f.header.typ == .settings &&
        f.header.streamId == 0 &&
        match f.payload with
        | .settings sf => sf.ack && sf.settings.isEmpty
        | _ => false

def testPingAck : Bool :=
  match frame_bytes bytesPingAck with
  | .error _ => false
  | .ok f =>
      f.header.length == 8 &&
        f.header.typ == .ping &&
        f.header.streamId == 0 &&
        match f.payload with
        | .ping pf =>
            pf.ack &&
              pf.opaque_ == ByteArray.mk #[0xde, 0xad, 0xbe, 0xef, 0x00, 0x01, 0x02, 0x03]
        | _ => false

#eval testData
#eval testHeadersPadded
#eval testSettingsAck
#eval testPingAck
