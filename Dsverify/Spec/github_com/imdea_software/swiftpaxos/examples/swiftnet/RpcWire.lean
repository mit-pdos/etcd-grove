/-
**Step 5, the codec switch (started, eighth session).** The bytes the kit's generated net/rpc
codec (`examples/swiftnet/rpc_gen.go`, rpcgen) writes for the values of its listed rpc types, as
pure functions over the lab's `sp.KitVal` (Spec/swift/Wire.lean): what `sp.KitVal.encode` (the
lab's kitgen format) is to be restated as. Not used yet.

rpcgen's format (`rpcEncode`): the type's tag (`rpcPutTag`: its full Go name, as an 8-byte
little-endian length then the bytes), then the value (`rpcEnc_t*`): a struct is a presence byte
`1`, then per field a byte `1` and the field's encoding when it is sent (`rpcSent_t*`: gob's
non-zero test) or a byte `0`; an integer is 8 bytes little-endian (signed ones sign-extended,
`uint64(int64(v))`); a string or slice is its length (8 bytes) then its elements; a bool is a
byte.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- `rpcPutU64` of a signed 32-bit value (`rpcEnc_t26`: `uint64(int64(v))`). -/
def rI32 (x : w32) : List w8 := u64Le (BitVec.signExtend 64 x)

/-- `rpcEnc_t14` (a string), `rpcEnc_t13` (`[]string`), `rpcEnc_t16`/`t15` (bool, `[]bool`). -/
def rStr (s : GoString) : List w8 := u64Le (W64 s.length) ++ s
def rStrs (l : List GoString) : List w8 := u64Le (W64 l.length) ++ (l.map rStr).flatten
def rBool (b : Bool) : List w8 := [if b then W8 1 else W8 0]
def rBools (l : List Bool) : List w8 := u64Le (W64 l.length) ++ (l.map rBool).flatten

/-- A struct field: `1` and its encoding when sent, else `0`. -/
def rField (sent : Bool) (enc : List w8) : List w8 := if sent then W8 1 :: enc else [W8 0]

/-- `rpcPutTag`: the type name's length (8 bytes), then the name. -/
def rTag (t : GoString) : List w8 := u64Le (W64 t.length) ++ t

/-- The Go name of a listed type (`rpcEncode`'s tags). -/
def KitVal.rpcName : KitVal → GoString
  | .registerArgs .. => go!"github.com/imdea-software/swiftpaxos/replica/defs.RegisterArgs"
  | .registerReply .. => go!"github.com/imdea-software/swiftpaxos/replica/defs.RegisterReply"
  | .getLeaderArgs => go!"github.com/imdea-software/swiftpaxos/replica/defs.GetLeaderArgs"
  | .getLeaderReply .. => go!"github.com/imdea-software/swiftpaxos/replica/defs.GetLeaderReply"
  | .getReplicaListArgs =>
      go!"github.com/imdea-software/swiftpaxos/replica/defs.GetReplicaListArgs"
  | .getReplicaListReply .. =>
      go!"github.com/imdea-software/swiftpaxos/replica/defs.GetReplicaListReply"
  | .pingArgs .. => go!"github.com/imdea-software/swiftpaxos/replica/defs.PingArgs"
  | .pingReply => go!"github.com/imdea-software/swiftpaxos/replica/defs.PingReply"
  | .beTheLeaderArgs => go!"github.com/imdea-software/swiftpaxos/replica/defs.BeTheLeaderArgs"
  | .beTheLeaderReply .. => go!"github.com/imdea-software/swiftpaxos/replica/defs.BeTheLeaderReply"
  | .msync .. => go!"github.com/imdea-software/swiftpaxos/swift.MSync"

/-- The value's encoding after its tag (`rpcEnc_t*`). `MSync`'s (`rpcEnc_t86`, listed in
`rpc.toml` but never sent over net/rpc: `MSync` goes through `encoding/gob`) is left out. -/
def KitVal.rpcBody : KitVal → List w8
  | .registerArgs a p => W8 1 :: (rField (a ≠ []) (rStr a) ++ rField (p ≠ 0) (u64Le p))
  | .registerReply i ns r l => W8 1 :: (rField (i ≠ 0) (u64Le i) ++ rField (ns ≠ []) (rStrs ns) ++
      rField r (rBool r) ++ rField l (rBool l))
  | .getLeaderArgs => [W8 1]
  | .getLeaderReply i => W8 1 :: rField (i ≠ 0) (u64Le i)
  | .getReplicaListArgs => [W8 1]
  | .getReplicaListReply rs al r => W8 1 :: (rField (rs ≠ []) (rStrs rs) ++
      rField (al ≠ []) (rBools al) ++ rField r (rBool r))
  | .pingArgs a => W8 1 :: rField (a ≠ 0) (u64Le (BitVec.zeroExtend 64 a))
  | .pingReply => [W8 1]
  | .beTheLeaderArgs => [W8 1]
  | .beTheLeaderReply l n => W8 1 :: (rField (l ≠ 0) (rI32 l) ++ rField (n ≠ 0) (rI32 n))
  | .msync .. => []

/-- `rpcEncode`'s bytes of a value of a listed type (other than `MSync`). -/
def KitVal.rpcEncode (v : KitVal) : List w8 := rTag v.rpcName ++ v.rpcBody

end sp

end Perennial.github_com.imdea_software.swiftpaxos
