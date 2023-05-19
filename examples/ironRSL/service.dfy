module Native__NativeTypes_s {
newtype{:nativeType "sbyte"} sbyte = i:int | -0x80 <= i < 0x80
newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
newtype{:nativeType "short"} int16 = i:int | -0x8000 <= i < 0x8000
newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
newtype{:nativeType "long"} int64 = i:int | -0x8000000000000000 <= i < 0x8000000000000000
newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000

newtype{:nativeType "sbyte"} nat8 = i:int | 0 <= i < 0x80
newtype{:nativeType "short"} nat16 = i:int | 0 <= i < 0x8000
newtype{:nativeType "int"} nat32 = i:int | 0 <= i < 0x80000000
newtype{:nativeType "long"} nat64 = i:int | 0 <= i < 0x8000000000000000

} 

import opened Native__NativeTypes_s

datatype EndPoint = EndPoint(public_key:seq<byte>)

type Bytes = seq<byte>
type AppState = Bytes
type AppRequest = Bytes
type AppReply = Bytes

function AppInitialize() : AppState
{
    []
}
function AppHandleRequest(m:AppState, request:AppRequest) : (AppState, AppReply)
{
    ([],[])
}
function method MaxAppRequestSize() : int  { 0x800_0000 }            // 128 MB
function method MaxAppReplySize() : int    { 0x800_0000 }            // 128 MB
function method MaxAppStateSize() : int    { 0x1000_0000_0000_0000 } // 2^60 B

datatype AppRequestMessage = AppRequestMessage(client:EndPoint, seqno:int, request:AppRequest)
datatype AppReplyMessage   = AppReplyMessage(client:EndPoint, seqno:int, reply:AppReply)

datatype ServiceState' = ServiceState'(
  serverAddresses:set<EndPoint>,
  app:AppState,
  requests:set<AppRequestMessage>,
  replies:set<AppReplyMessage>
  )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
  && s.serverAddresses == serverAddresses
  && s.app == AppInitialize()
  && s.requests == {}
  && s.replies == {}
}

predicate ServiceExecutesAppRequest(s:ServiceState, s':ServiceState, req:AppRequestMessage)
// seqno requirement?
{
  && |req.request| <= MaxAppRequestSize()
  && s'.serverAddresses == s.serverAddresses
  && s'.requests == s.requests + { req }
  && s'.app == AppHandleRequest(s.app, req.request).0
  && s'.replies == s.replies + { AppReplyMessage(req.client, req.seqno, AppHandleRequest(s.app, req.request).1) }
}