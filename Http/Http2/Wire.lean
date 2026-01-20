module

public import Std

public section

namespace Http.Http2

abbrev StreamId := Nat

inductive FrameType where
  | data
  | headers
  | priority
  | rstStream
  | settings
  | pushPromise
  | ping
  | goaway
  | windowUpdate
  | continuation
  | unknown (typ : UInt8)
deriving Inhabited, Repr, BEq

@[inline]
def FrameType.ofByte (b : UInt8) : FrameType :=
  match b.toNat with
  | 0 => .data
  | 1 => .headers
  | 2 => .priority
  | 3 => .rstStream
  | 4 => .settings
  | 5 => .pushPromise
  | 6 => .ping
  | 7 => .goaway
  | 8 => .windowUpdate
  | 9 => .continuation
  | _ => .unknown b

@[inline]
def FrameType.toByte : FrameType → UInt8
  | .data => 0
  | .headers => 1
  | .priority => 2
  | .rstStream => 3
  | .settings => 4
  | .pushPromise => 5
  | .ping => 6
  | .goaway => 7
  | .windowUpdate => 8
  | .continuation => 9
  | .unknown b => b

structure FrameHeader where
  length : Nat
  typ : FrameType
  flags : UInt8
  streamId : StreamId
deriving Inhabited, Repr

structure PriorityInfo where
  exclusive : Bool
  streamDependency : StreamId
  weight : Nat
deriving Inhabited, Repr

structure DataFrame where
  padLength? : Option UInt8
  data : ByteArray
deriving Inhabited

structure HeadersFrame where
  padLength? : Option UInt8
  priority? : Option PriorityInfo
  headerBlock : ByteArray
deriving Inhabited

structure PriorityFrame where
  priority : PriorityInfo
deriving Inhabited, Repr

structure RstStreamFrame where
  errorCode : UInt32
deriving Inhabited, Repr

structure Setting where
  identifier : UInt16
  value : UInt32
deriving Inhabited, Repr

structure SettingsFrame where
  ack : Bool
  settings : Array Setting
deriving Inhabited, Repr

structure PushPromiseFrame where
  padLength? : Option UInt8
  promisedStreamId : StreamId
  headerBlock : ByteArray
deriving Inhabited

structure PingFrame where
  ack : Bool
  opaque_ : ByteArray
deriving Inhabited

structure GoAwayFrame where
  lastStreamId : StreamId
  errorCode : UInt32
  debugData : ByteArray
deriving Inhabited

structure WindowUpdateFrame where
  windowSizeIncrement : Nat
deriving Inhabited, Repr

structure ContinuationFrame where
  headerBlock : ByteArray
deriving Inhabited

inductive FramePayload where
  | data (f : DataFrame)
  | headers (f : HeadersFrame)
  | priority (f : PriorityFrame)
  | rstStream (f : RstStreamFrame)
  | settings (f : SettingsFrame)
  | pushPromise (f : PushPromiseFrame)
  | ping (f : PingFrame)
  | goaway (f : GoAwayFrame)
  | windowUpdate (f : WindowUpdateFrame)
  | continuation (f : ContinuationFrame)
  | unknown (typ : UInt8) (payload : ByteArray)
deriving Inhabited

structure Frame where
  header : FrameHeader
  payload : FramePayload
deriving Inhabited

def connectionPreface : ByteArray :=
  "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".toUTF8

end Http.Http2

end
