/-
The wire format of a replica's peer/client address (port `Port0 + i`), as the protocols of
`Epaxos/Interface/Client.lean` speak of it:

* pure encoders of SwiftPaxos's client messages, byte for byte as the Go marshalers write them
  (`state/state.go`, `replica/defs/defs.go`): `encValue` (`state.Value.Marshal`), `encCommand`
  (`state.Command.Marshal`), `encPropose` (`defs.Propose.Marshal`), `encProposeReplyTS`
  (`defs.ProposeReplyTS.Marshal`), the message tag `proposeTag` (`defs.PROPOSE`);
* the command of a model input as `Op` builds it (`cmdOf`: the model's key is SwiftPaxos's
  key; a scan's count is its value, 8 bytes little-endian), the keys a `SCAN` reads
  (`rangeKeys`), and the reply value an output is sent with (`replyValOk`).

The peer role's streams are in `Epaxos/Interface/PeerWire.lean` (encoders) and
`Epaxos/Interface/Net.lean` (`peerStreamOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.KvScan
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open github_com.imdea_software.swiftpaxos_epaxos.kvs

/-! ## Pure encoders -/

/-- `state.Operation`'s values: `NONE`, `PUT`, `GET`, `SCAN` (`state/state.go`). -/
def opNONE : w8 := W8 0
def opPUT : w8 := W8 1
def opGET : w8 := W8 2
def opSCAN : w8 := W8 3

/-- `defs.PROPOSE`, the tag byte of a client's proposal (`replica/defs/defs.go`). -/
def proposeTag : w8 := W8 0

/-- `defs.TRUE`. -/
def okTRUE : w8 := W8 1

/-- A `state.Command` as the wire sees it: the operation byte, the key (`state.Key`, an `int64`,
as its bits) and the value's bytes. -/
structure WCmd where
  op : w8
  key : w64
  val : List w8

/-- `state.Value.Marshal` (non-nil receiver): a 4-byte length field, whose first two bytes are
`uint16(len(v))` little-endian and the other two zero, then the bytes. (`uint16` truncates: the
field is the length modulo `2 ^ 16`; the input premise keeps put values below `2 ^ 15`, so that a
scan's reply, at most two values, stays below `2 ^ 16`, S5.) -/
def encValue (v : List w8) : List w8 :=
  u32Le (W32 (v.length % 2 ^ 16 : Nat)) ++ v

/-- `state.Command.Marshal`: the operation byte, the key (8 bytes little-endian), the value. -/
def encCommand (c : WCmd) : List w8 :=
  [c.op] ++ u64Le c.key ++ encValue c.val

/-- `defs.Propose.Marshal`: `CommandId`, `ClientId` (`int32`, 4 bytes little-endian each), the
command, `Timestamp` (`int64`, 8 bytes little-endian). -/
def encPropose (cmdId clientId : w32) (cmd : WCmd) (ts : w64) : List w8 :=
  u32Le cmdId ++ u32Le clientId ++ encCommand cmd ++ u64Le ts

/-- `defs.ProposeReplyTS.Marshal`: `OK` (1 byte), `CommandId` (4 bytes little-endian), the value,
`Timestamp` (8 bytes little-endian). -/
def encProposeReplyTS (ok : w8) (cmdId : w32) (v : List w8) (ts : w64) : List w8 :=
  [ok] ++ u32Le cmdId ++ encValue v ++ u64Le ts

/-! ## The commands of the model's inputs -/

/-- The keys a `SCAN` command `c` reads (`Command.Execute`'s `Select`: the keys `k` with
`c.K <= k && k <= c.K + Key(count)`, `count` = `binary.LittleEndian.Uint64(c.V)`, in `int64`
with Go's wrapping add), in increasing (signed) order: `K, K+1, ..., K+count` when `K + count`
does not wrap below `K`, none otherwise. (`Uint64` reads the first 8 bytes; a `SCAN` with a
shorter value is out of scope, S3.) -/
def rangeKeys (c : WCmd) : List w64 :=
  let hi := c.key + leToU64 (c.val.take 8)
  if sint.Z c.key ≤ sint.Z hi then
    (List.range ((sint.Z hi - sint.Z c.key).toNat + 1)).map (fun j : Nat => c.key + W64 (j : Int))
  else []

/-- The command `Op` sends for input `i` (the model's key `k` is SwiftPaxos's `state.Key(k)`): a
`GET` with the empty value (`state.NIL()`), a `PUT` with the value's bytes, a `SCAN` of `n` with
`n` as 8 little-endian bytes (`client.SendScan`). -/
def cmdOf : KvsInput (List w8) → WCmd
  | .get k => ⟨opGET, k, []⟩
  | .put k v => ⟨opPUT, k, v⟩
  | .scan k n => ⟨opSCAN, k, u64Le n⟩

/-- What `Op` writes on its connection for client `c`'s input `i`: the `PROPOSE` tag, then
`Propose{CommandId: 0, ClientId: int32(c), Command: cmdOf i, Timestamp: 0}`. -/
def proposeBytes (c : w64) (i : KvsInput (List w8)) : List w8 :=
  [proposeTag] ++ encPropose (W32 0) (W32 (uint.Z c)) (cmdOf i) (W64 0)

/-- The reply value `v` a replica may send for an op whose output is `o`: anything for a put
(`Op` ignores it), the empty value for a get of an absent key, the key's (non-empty) value
for a get of a present key, the scanned values (concatenated) for a scan. (A get's value is
never empty: put values are non-empty, the input premise; so `Op` reads an empty value as "not
found".) -/
def replyValOk : KvsOutput (List w8) → List w8 → Prop
  | .done, _ => True
  | .got none, v => v = []
  | .got (some x), v => v = x ∧ x ≠ []
  | .scanned x, v => v = x

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
