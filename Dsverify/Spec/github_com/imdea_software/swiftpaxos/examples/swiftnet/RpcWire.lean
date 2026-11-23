/-
The wire values of the kit's net/rpc calls (the master's `Register`, `GetLeader`,
`GetReplicaList`; a replica's `BeTheLeader`, `Ping`): the kit's generated codec
(`examples/swiftnet/rpc_gen.go`, by `models/net/rpc/rpcgen.py`) as pure Lean functions of the
abstract values. (The lab's `Interface/RpcPure.lean` described its own kitgen codec, `RpcVal`; it
is not ported: the bytes here are rpcgen's, as dsv-craq's `Craq/Wire.lean`.)

A top-level value is its type's name (`rpcPutTag`: the name's length, 8 bytes little-endian, and
its bytes) and the value. A string is its length and its bytes; an `int`, `int32`, `uint8` 8
bytes little-endian (the signed ones sign-extended to 64 bits); a `bool` one byte; a slice its
count and its elements. A struct is the byte 1, then per field a byte 1 and the field's value if
the field is sent (not its zero value: gob's rule), else a byte 0.
-/
module

public import Perennial.Std.Word.LittleEndian
public import Perennial.Std.ByteString

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.imdea_software.swiftpaxos.netrpcw

/-- A 64-bit word (`int`, rpcgen's `t4`; also `int32`'s and `uint8`'s extension). -/
def encU64 (x : w64) : List w8 := u64Le x

/-- A string: its length and its bytes (`t14`). -/
def encStr (s : GoString) : List w8 := u64Le (W64 s.length) ++ s

/-- A `bool` (`t16`). -/
def encBool (b : Bool) : List w8 := [if b then W8 1 else W8 0]

/-- An `int32` (`t26`): sign-extended. -/
def encI32 (x : w32) : List w8 := u64Le (W64 (sint.Z x))

/-- A `uint8` (`t66`). -/
def encU8 (x : w8) : List w8 := u64Le (W64 (uint.Z x))

/-- A `[]string` (`t13`): its count and its elements. -/
def encStrs (ss : List GoString) : List w8 := u64Le (W64 ss.length) ++ (ss.map encStr).flatten

/-- A `[]bool` (`t15`): its count and its elements. -/
def encBools (bs : List Bool) : List w8 := u64Le (W64 bs.length) ++ (bs.map encBool).flatten

/-- A struct field: sent (`1` and its value) or not (`0`). -/
def fld (sent : Bool) (body : List w8) : List w8 := if sent then W8 1 :: body else [W8 0]

def fStr (s : GoString) : List w8 := fld (decide (s ≠ [])) (encStr s)
def fInt (x : w64) : List w8 := fld (decide (x ≠ W64 0)) (encU64 x)
def fBool (b : Bool) : List w8 := fld b (encBool b)
def fI32 (x : w32) : List w8 := fld (decide (x ≠ W32 0)) (encI32 x)
def fU8 (x : w8) : List w8 := fld (decide (x ≠ W8 0)) (encU8 x)
def fStrs (ss : List GoString) : List w8 := fld (decide (ss ≠ [])) (encStrs ss)
def fBools (bs : List Bool) : List w8 := fld (decide (bs ≠ [])) (encBools bs)

/-- A struct of the fields `fs`. -/
def strct (fs : List (List w8)) : List w8 := W8 1 :: fs.flatten

/-- A top-level value of the type named `t`. -/
def tagged (t : GoString) (body : List w8) : List w8 := encStr t ++ body

/-- The type names (`rpcPutTag`'s arguments). -/
def tRegisterArgs : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.RegisterArgs"
def tRegisterReply : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.RegisterReply"
def tGetLeaderArgs : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.GetLeaderArgs"
def tGetLeaderReply : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.GetLeaderReply"
def tGetReplicaListArgs : GoString :=
  go!"github.com/imdea-software/swiftpaxos/replica/defs.GetReplicaListArgs"
def tGetReplicaListReply : GoString :=
  go!"github.com/imdea-software/swiftpaxos/replica/defs.GetReplicaListReply"
def tBeTheLeaderArgs : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.BeTheLeaderArgs"
def tBeTheLeaderReply : GoString :=
  go!"github.com/imdea-software/swiftpaxos/replica/defs.BeTheLeaderReply"
def tPingArgs : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.PingArgs"
def tPingReply : GoString := go!"github.com/imdea-software/swiftpaxos/replica/defs.PingReply"

/-! ## The values -/

/-- `defs.RegisterArgs{Addr, Port}`. -/
def encRegisterArgs (addr : GoString) (port : w64) : List w8 :=
  tagged tRegisterArgs (strct [fStr addr, fInt port])

/-- `defs.RegisterReply{ReplicaId, NodeList, Ready, IsLeader}`. -/
def encRegisterReply (id : w64) (nl : List GoString) (ready isLeader : Bool) : List w8 :=
  tagged tRegisterReply (strct [fInt id, fStrs nl, fBool ready, fBool isLeader])

/-- `defs.GetLeaderArgs{}`. -/
def encGetLeaderArgs : List w8 := tagged tGetLeaderArgs (strct [])

/-- `defs.GetLeaderReply{LeaderId}`. -/
def encGetLeaderReply (id : w64) : List w8 := tagged tGetLeaderReply (strct [fInt id])

/-- `defs.GetReplicaListArgs{}`. -/
def encGetReplicaListArgs : List w8 := tagged tGetReplicaListArgs (strct [])

/-- `defs.GetReplicaListReply{ReplicaList, AliveList, Ready}`. -/
def encGetReplicaListReply (rl : List GoString) (al : List Bool) (ready : Bool) : List w8 :=
  tagged tGetReplicaListReply (strct [fStrs rl, fBools al, fBool ready])

/-- `defs.BeTheLeaderArgs{}`. -/
def encBtlArgs : List w8 := tagged tBeTheLeaderArgs (strct [])

/-- `defs.BeTheLeaderReply{Leader, NextLeader}`. -/
def encBtlReply (l nl : w32) : List w8 := tagged tBeTheLeaderReply (strct [fI32 l, fI32 nl])

/-- `defs.PingArgs{ActAsLeader}`. -/
def encPingArgs (a : w8) : List w8 := tagged tPingArgs (strct [fU8 a])

/-- `defs.PingReply{}`. -/
def encPingReply : List w8 := tagged tPingReply (strct [])

end github_com.imdea_software.swiftpaxos.netrpcw

end Perennial
