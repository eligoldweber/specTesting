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


datatype ServiceState' = ServiceState'(
    hosts:set<EndPoint>,
    history:seq<EndPoint>
    )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.hosts == serverAddresses
    && |s.history| > 0
    && (exists e :: e in serverAddresses && s.history[0] == e)
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
       s'.hosts == s.hosts
    && (exists new_lock_holder:EndPoint :: 
         s'.history == s.history + [new_lock_holder])
}
