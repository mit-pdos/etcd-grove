/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Enc.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Gryff's wire encodings (stage 1 interface)

What `Marshal` writes, for every message type that crosses a connection in Gryff's proxy-mode
deployment, and how a Go struct holds a message. The specs of the `Marshal` / `Unmarshal`
methods over these are in `GryffProof/Wire/Specs.lean`.

**Types covered** (namespace `Perennial.gryff.wire.<pkg>`):
* `state`: `Key`, `Value`, `Command`;
* `gryffproto`: `Tag`, `ValTag`, `Dep`, `Read`, `ReadReply`, `Write`, `WriteReply`, `RMW`,
  `RMWReply`, `Read1Proxied`, `Read1Reply`, `Read2Proxied`, `Read2Reply`, `Write1Proxied`,
  `Write1Reply`, `Write2Proxied`, `Write2Reply`, `PreAccept`, `PreAcceptReply`, `EAccept`,
  `ECommit`, `TryPreAccept`, `PrepareReply`, `Executed`, `PreAcceptOKReply`, `AcceptOKReply`;
* `epaxosproto`: `Prepare`, `PreAcceptOK`, `AcceptReply`, `CommitShort`, `TryPreAcceptReply`;
* `clientproto`: `Ping`, `PingReply`;
* `genericsmrproto`: `Beacon`, `BeaconReply`, `Propose`, `ProposeReplyTS`.

**Per type `T`:**
* `T.Msg`: the message's values. For a type without a slice field it is Goose's own record
  (`src.<pkg>.T`, an `abbrev`: fields `F'`, `w32` for `int32`, `w64` for `int64` / `uint64`,
  `w8` for `uint8` / `int8`, Goose's records for nested structs, `GoArray w32 5` for `[5]int32`;
  `state.Key` / `state.Value` are `w64`). For the five gryffproto types with a
  `[]state.Command` field (`PreAccept`, `EAccept`, `ECommit`, `TryPreAccept`, `PrepareReply`)
  it is a new record with the same fields, `Command : List src.state.Command` holding the slice's elements;
  `T.goVal m s` is the Go struct holding `m` with the slice `s` as its `Command` field.
* `T.enc : T.Msg → List w8`: the bytes `(*T).Marshal(wire)` writes, in order (the
  concatenation of its `wire.Write` calls).
* `T.own t dq m` (in the heap section): `t` holds `m`. `t ↦{dq} m` for a type without a slice
  field; with one, the struct `goVal m s` and `s ↦*{dq} m.Command`.
* `T.wf m`: `m` is encodable faithfully (`True`, except: the slice length is below `2^63`).
* `T.nextOk D`: what the reader's later bytes `D` must be for `Unmarshal` to be safe (`True`,
  except for the slice types: `D` is comparable, by prefix, with the encoding of some `wf`
  message; `Unmarshal` does `make([]state.Command, n)` on the decoded length `n`, which panics
  when `n < 0`).

**How `enc` matches the Go code** (generated code: `gryffproto/tupaqprotomarsh.go`,
`epaxosproto/epaxosprotomarsh.go`, `genericsmrproto/genericsmrprotomarsh.go`,
`clientproto/clientprotomarsh.go`, `state/statemarsh.go`):
* An `int32` / `uint32` field: `bs[i] = byte(tmp32 >> 8j)`, `j = 0..3`, is its 4 bytes little
  endian: `u32Le` (Perennial's `split 4`, `Perennial/Std/Word/LittleEndian.lean`); an
  `int64` / `uint64` field the same with 8 bytes, `u64Le`; a `uint8` / `int8` field one byte,
  `[x]` (Go's `byte(x)` keeps the bits).
* A field with its own `Marshal` (`state.Key`, `state.Value`, `Tag`, `ValTag`, `Dep`,
  `state.Command`): that type's `enc`. A `Tag` copied inline field by field (`MaxSeenTag`,
  `MaxAppliedTag`, `T`) is written `Tag.enc` (the same bytes).
* `[5]int32`: the five elements in order, `arrLe32` (each `u32Le`).
* `[]state.Command`: `binary.PutVarint(int64(len))` (`varintEnc`: zigzag, then base-128 with
  the high bit as continuation, low group first), then each element's `Marshal`.
* `state.Key` / `state.Value`: `binary.LittleEndian.PutUint64`, `u64Le`.
The fixed-width fields of one `wire.Write(bs)` are exactly the bytes `bs[0:len(bs)]` set before
it (every one of them is set: no stale byte of the shared buffer `b` is written). Every
`Unmarshal` reads the same layout back (the same chunk sizes, the same byte indices per field,
nested `Unmarshal`s and the varint at the same places); each nested error ends it.
-/
module

public import Dsverify.GeneratedProof.gryff.src.gryffproto
public import Dsverify.GeneratedProof.gryff.src.epaxosproto
public import Dsverify.GeneratedProof.gryff.src.genericsmrproto
public import Dsverify.GeneratedProof.gryff.src.clientproto
public import Dsverify.GeneratedProof.gryff.src.state
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI

/-! ## Helpers -/

/-- Go's `binary.PutUvarint`: base 128, low group first, the high bit set on every byte but the
last (`byte(x) | 0x80` is `x % 128 + 128`). -/
def uvarintEnc (n : Nat) : List w8 :=
  if n < 128 then [BitVec.ofNat 8 n]
  else BitVec.ofNat 8 (n % 128 + 128) :: uvarintEnc (n / 128)
termination_by n
decreasing_by omega

/-- Go's zigzag (`binary.PutVarint`: `ux := uint64(x) << 1; if x < 0 { ux = ^ux }`), on an
`int64` value `x`: `2x` for `x ≥ 0`, `-2x - 1` for `x < 0`. -/
def zigzag (x : Int) : Nat := if 0 ≤ x then (2 * x).toNat else (-2 * x - 1).toNat

/-- Go's `binary.PutVarint(buf, x)`: the bytes `buf[0:n]` it writes, for an `int64` value `x`. -/
def varintEnc (x : Int) : List w8 := uvarintEnc (zigzag x)

/-- A `[n]int32` array's elements in order, each 4 bytes little endian. -/
def arrLe32 {n : Int} (a : GoArray w32 n) : List w8 :=
  (List.range n.toNat).flatMap fun i => u32Le (a.arr.getD i 0)

/-! ## Messages and encodings -/

section enc
variable [GooseExts]

namespace state

/-- `state.Key`'s values: Goose's representation. -/
abbrev Key.Msg := src.state.Key

/-- The bytes `(*Key).Marshal` writes. -/
def Key.enc (m : Key.Msg) : List w8 :=
    u64Le m

/-- No condition: every value is encodable. -/
def Key.wf (_m : Key.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Key.nextOk (_D : List w8) : Prop := True

end state

namespace state

/-- `state.Value`'s values: Goose's representation. -/
abbrev Value.Msg := src.state.Value

/-- The bytes `(*Value).Marshal` writes. -/
def Value.enc (m : Value.Msg) : List w8 :=
    u64Le m

/-- No condition: every value is encodable. -/
def Value.wf (_m : Value.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Value.nextOk (_D : List w8) : Prop := True

end state

namespace state

/-- `state.Command`'s values: Goose's representation. -/
abbrev Command.Msg := src.state.Command

/-- The bytes `(*Command).Marshal` writes. -/
def Command.enc (m : Command.Msg) : List w8 :=
    [m.Op'] ++
    u64Le m.K' ++
    u64Le m.V' ++
    u64Le m.OldValue'

/-- No condition: every value is encodable. -/
def Command.wf (_m : Command.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Command.nextOk (_D : List w8) : Prop := True

end state

namespace gryffproto

/-- `gryffproto.Tag`'s values: Goose's representation. -/
abbrev Tag.Msg := src.gryffproto.Tag

/-- The bytes `(*Tag).Marshal` writes. -/
def Tag.enc (m : Tag.Msg) : List w8 :=
    u32Le m.Ts' ++
    u32Le m.Cid' ++
    u32Le m.Rmwc'

/-- No condition: every value is encodable. -/
def Tag.wf (_m : Tag.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Tag.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.ValTag`'s values: Goose's representation. -/
abbrev ValTag.Msg := src.gryffproto.ValTag

/-- The bytes `(*ValTag).Marshal` writes. -/
def ValTag.enc (m : ValTag.Msg) : List w8 :=
    state.Value.enc m.V' ++
    gryffproto.Tag.enc m.T'

/-- No condition: every value is encodable. -/
def ValTag.wf (_m : ValTag.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def ValTag.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Dep`'s values: Goose's representation. -/
abbrev Dep.Msg := src.gryffproto.Dep

/-- The bytes `(*Dep).Marshal` writes. -/
def Dep.enc (m : Dep.Msg) : List w8 :=
    state.Key.enc m.Key' ++
    gryffproto.ValTag.enc m.Vt'

/-- No condition: every value is encodable. -/
def Dep.wf (_m : Dep.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Dep.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Read`'s values: Goose's representation. -/
abbrev Read.Msg := src.gryffproto.Read

/-- The bytes `(*Read).Marshal` writes. -/
def Read.enc (m : Read.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    state.Key.enc m.K' ++
    gryffproto.Dep.enc m.D'

/-- No condition: every value is encodable. -/
def Read.wf (_m : Read.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Read.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.ReadReply`'s values: Goose's representation. -/
abbrev ReadReply.Msg := src.gryffproto.ReadReply

/-- The bytes `(*ReadReply).Marshal` writes. -/
def ReadReply.enc (m : ReadReply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    state.Value.enc m.V' ++
    gryffproto.Tag.enc m.MaxSeenTag' ++
    [m.OK']

/-- No condition: every value is encodable. -/
def ReadReply.wf (_m : ReadReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def ReadReply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Write`'s values: Goose's representation. -/
abbrev Write.Msg := src.gryffproto.Write

/-- The bytes `(*Write).Marshal` writes. -/
def Write.enc (m : Write.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    state.Key.enc m.K' ++
    state.Value.enc m.V' ++
    gryffproto.Dep.enc m.D'

/-- No condition: every value is encodable. -/
def Write.wf (_m : Write.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Write.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.WriteReply`'s values: Goose's representation. -/
abbrev WriteReply.Msg := src.gryffproto.WriteReply

/-- The bytes `(*WriteReply).Marshal` writes. -/
def WriteReply.enc (m : WriteReply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    gryffproto.Tag.enc m.MaxSeenTag' ++
    [m.OK']

/-- No condition: every value is encodable. -/
def WriteReply.wf (_m : WriteReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def WriteReply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.RMW`'s values: Goose's representation. -/
abbrev RMW.Msg := src.gryffproto.RMW

/-- The bytes `(*RMW).Marshal` writes. -/
def RMW.enc (m : RMW.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    state.Key.enc m.K' ++
    gryffproto.Dep.enc m.D' ++
    state.Value.enc m.OldValue' ++
    state.Value.enc m.NewValue'

/-- No condition: every value is encodable. -/
def RMW.wf (_m : RMW.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def RMW.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.RMWReply`'s values: Goose's representation. -/
abbrev RMWReply.Msg := src.gryffproto.RMWReply

/-- The bytes `(*RMWReply).Marshal` writes. -/
def RMWReply.enc (m : RMWReply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ReplicaId' ++
    state.Value.enc m.OldValue' ++
    [m.OK']

/-- No condition: every value is encodable. -/
def RMWReply.wf (_m : RMWReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def RMWReply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Read1Proxied`'s values: Goose's representation. -/
abbrev Read1Proxied.Msg := src.gryffproto.Read1Proxied

/-- The bytes `(*Read1Proxied).Marshal` writes. -/
def Read1Proxied.enc (m : Read1Proxied.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    state.Key.enc m.K' ++
    gryffproto.Dep.enc m.D' ++
    u32Le m.ReplicaId' ++
    gryffproto.ValTag.enc m.Vt'

/-- No condition: every value is encodable. -/
def Read1Proxied.wf (_m : Read1Proxied.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Read1Proxied.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Read1Reply`'s values: Goose's representation. -/
abbrev Read1Reply.Msg := src.gryffproto.Read1Reply

/-- The bytes `(*Read1Reply).Marshal` writes. -/
def Read1Reply.enc (m : Read1Reply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    u32Le m.ReplicaId' ++
    gryffproto.ValTag.enc m.Vt'

/-- No condition: every value is encodable. -/
def Read1Reply.wf (_m : Read1Reply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Read1Reply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Read2Proxied`'s values: Goose's representation. -/
abbrev Read2Proxied.Msg := src.gryffproto.Read2Proxied

/-- The bytes `(*Read2Proxied).Marshal` writes. -/
def Read2Proxied.enc (m : Read2Proxied.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    state.Key.enc m.K' ++
    gryffproto.ValTag.enc m.Vt' ++
    u32Le m.ReplicaId' ++
    u64Le m.UpdateId'

/-- No condition: every value is encodable. -/
def Read2Proxied.wf (_m : Read2Proxied.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Read2Proxied.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Read2Reply`'s values: Goose's representation. -/
abbrev Read2Reply.Msg := src.gryffproto.Read2Reply

/-- The bytes `(*Read2Reply).Marshal` writes. -/
def Read2Reply.enc (m : Read2Reply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    u32Le m.ReplicaId' ++
    gryffproto.Tag.enc m.T'

/-- No condition: every value is encodable. -/
def Read2Reply.wf (_m : Read2Reply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Read2Reply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Write1Proxied`'s values: Goose's representation. -/
abbrev Write1Proxied.Msg := src.gryffproto.Write1Proxied

/-- The bytes `(*Write1Proxied).Marshal` writes. -/
def Write1Proxied.enc (m : Write1Proxied.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    u32Le m.N' ++
    u32Le m.ForceWrite' ++
    state.Key.enc m.K' ++
    state.Value.enc m.V' ++
    gryffproto.Dep.enc m.D' ++
    u32Le m.ReplicaId' ++
    gryffproto.Tag.enc m.MaxAppliedTag'

/-- No condition: every value is encodable. -/
def Write1Proxied.wf (_m : Write1Proxied.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Write1Proxied.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Write1Reply`'s values: Goose's representation. -/
abbrev Write1Reply.Msg := src.gryffproto.Write1Reply

/-- The bytes `(*Write1Reply).Marshal` writes. -/
def Write1Reply.enc (m : Write1Reply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    u32Le m.ReplicaId' ++
    gryffproto.ValTag.enc m.Vt'

/-- No condition: every value is encodable. -/
def Write1Reply.wf (_m : Write1Reply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Write1Reply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Write2Proxied`'s values: Goose's representation. -/
abbrev Write2Proxied.Msg := src.gryffproto.Write2Proxied

/-- The bytes `(*Write2Proxied).Marshal` writes. -/
def Write2Proxied.enc (m : Write2Proxied.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    u32Le m.N' ++
    state.Key.enc m.K' ++
    gryffproto.ValTag.enc m.Vt' ++
    u32Le m.ReplicaId'

/-- No condition: every value is encodable. -/
def Write2Proxied.wf (_m : Write2Proxied.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Write2Proxied.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.Write2Reply`'s values: Goose's representation. -/
abbrev Write2Reply.Msg := src.gryffproto.Write2Reply

/-- The bytes `(*Write2Reply).Marshal` writes. -/
def Write2Reply.enc (m : Write2Reply.Msg) : List w8 :=
    u32Le m.RequestId' ++
    u32Le m.ClientId' ++
    u32Le m.ReplicaId' ++
    gryffproto.Tag.enc m.T' ++
    u32Le m.Applied'

/-- No condition: every value is encodable. -/
def Write2Reply.wf (_m : Write2Reply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Write2Reply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- The values of a `gryffproto.PreAccept` (`Command`: the elements of its `[]state.Command`). -/
structure PreAccept.Msg where
  mk ::
  LeaderId : w32
  Replica : w32
  Instance : w32
  Ballot : w32
  Command : List src.state.Command
  Seq : w32
  Deps : GoArray w32 5
  Base : src.gryffproto.ValTag

/-- The Go struct holding `m`, its `Command` field the slice `s` (whose elements are
`m.Command`). -/
def PreAccept.goVal (m : PreAccept.Msg) (s : GoSlice) : src.gryffproto.PreAccept :=
  src.gryffproto.PreAccept.mk m.LeaderId m.Replica m.Instance m.Ballot s m.Seq m.Deps m.Base

/-- The bytes `(*PreAccept).Marshal` writes. -/
def PreAccept.enc (m : PreAccept.Msg) : List w8 :=
    u32Le m.LeaderId ++
    u32Le m.Replica ++
    u32Le m.Instance ++
    u32Le m.Ballot ++
    varintEnc (sint.Z (W64 m.Command.length)) ++
    (m.Command.flatMap state.Command.enc) ++
    u32Le m.Seq ++
    arrLe32 m.Deps ++
    gryffproto.ValTag.enc m.Base

/-- `m`'s slice length is an `int64` (true of a slice in memory). -/
def PreAccept.wf (m : PreAccept.Msg) : Prop := m.Command.length < 2 ^ 63

/-- The bytes `D` after a reader's position are comparable with (a prefix or an extension of)
the encoding of some `PreAccept`: the length varint is that of a real slice. -/
def PreAccept.nextOk (D : List w8) : Prop :=
  ∃ m : PreAccept.Msg, PreAccept.wf m ∧ (D <+: PreAccept.enc m ∨ PreAccept.enc m <+: D)

end gryffproto

namespace gryffproto

/-- `gryffproto.PreAcceptReply`'s values: Goose's representation. -/
abbrev PreAcceptReply.Msg := src.gryffproto.PreAcceptReply

/-- The bytes `(*PreAcceptReply).Marshal` writes. -/
def PreAcceptReply.enc (m : PreAcceptReply.Msg) : List w8 :=
    u32Le m.Replica' ++
    u32Le m.Instance' ++
    [m.OK'] ++
    u32Le m.Ballot' ++
    u32Le m.Seq' ++
    arrLe32 m.Deps' ++
    arrLe32 m.CommittedDeps' ++
    gryffproto.ValTag.enc m.Base'

/-- No condition: every value is encodable. -/
def PreAcceptReply.wf (_m : PreAcceptReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def PreAcceptReply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- The values of a `gryffproto.EAccept` (`Command`: the elements of its `[]state.Command`). -/
structure EAccept.Msg where
  mk ::
  LeaderId : w32
  Replica : w32
  Instance : w32
  Ballot : w32
  Count : w32
  Seq : w32
  Deps : GoArray w32 5
  Command : List src.state.Command
  Base : src.gryffproto.ValTag

/-- The Go struct holding `m`, its `Command` field the slice `s` (whose elements are
`m.Command`). -/
def EAccept.goVal (m : EAccept.Msg) (s : GoSlice) : src.gryffproto.EAccept :=
  src.gryffproto.EAccept.mk m.LeaderId m.Replica m.Instance m.Ballot m.Count m.Seq m.Deps s m.Base

/-- The bytes `(*EAccept).Marshal` writes. -/
def EAccept.enc (m : EAccept.Msg) : List w8 :=
    u32Le m.LeaderId ++
    u32Le m.Replica ++
    u32Le m.Instance ++
    u32Le m.Ballot ++
    u32Le m.Count ++
    u32Le m.Seq ++
    arrLe32 m.Deps ++
    varintEnc (sint.Z (W64 m.Command.length)) ++
    (m.Command.flatMap state.Command.enc) ++
    gryffproto.ValTag.enc m.Base

/-- `m`'s slice length is an `int64` (true of a slice in memory). -/
def EAccept.wf (m : EAccept.Msg) : Prop := m.Command.length < 2 ^ 63

/-- The bytes `D` after a reader's position are comparable with (a prefix or an extension of)
the encoding of some `EAccept`: the length varint is that of a real slice. -/
def EAccept.nextOk (D : List w8) : Prop :=
  ∃ m : EAccept.Msg, EAccept.wf m ∧ (D <+: EAccept.enc m ∨ EAccept.enc m <+: D)

end gryffproto

namespace gryffproto

/-- The values of a `gryffproto.ECommit` (`Command`: the elements of its `[]state.Command`). -/
structure ECommit.Msg where
  mk ::
  LeaderId : w32
  Replica : w32
  Instance : w32
  Command : List src.state.Command
  Seq : w32
  Deps : GoArray w32 5
  Base : src.gryffproto.ValTag

/-- The Go struct holding `m`, its `Command` field the slice `s` (whose elements are
`m.Command`). -/
def ECommit.goVal (m : ECommit.Msg) (s : GoSlice) : src.gryffproto.ECommit :=
  src.gryffproto.ECommit.mk m.LeaderId m.Replica m.Instance s m.Seq m.Deps m.Base

/-- The bytes `(*ECommit).Marshal` writes. -/
def ECommit.enc (m : ECommit.Msg) : List w8 :=
    u32Le m.LeaderId ++
    u32Le m.Replica ++
    u32Le m.Instance ++
    varintEnc (sint.Z (W64 m.Command.length)) ++
    (m.Command.flatMap state.Command.enc) ++
    u32Le m.Seq ++
    arrLe32 m.Deps ++
    gryffproto.ValTag.enc m.Base

/-- `m`'s slice length is an `int64` (true of a slice in memory). -/
def ECommit.wf (m : ECommit.Msg) : Prop := m.Command.length < 2 ^ 63

/-- The bytes `D` after a reader's position are comparable with (a prefix or an extension of)
the encoding of some `ECommit`: the length varint is that of a real slice. -/
def ECommit.nextOk (D : List w8) : Prop :=
  ∃ m : ECommit.Msg, ECommit.wf m ∧ (D <+: ECommit.enc m ∨ ECommit.enc m <+: D)

end gryffproto

namespace gryffproto

/-- The values of a `gryffproto.TryPreAccept` (`Command`: the elements of its `[]state.Command`). -/
structure TryPreAccept.Msg where
  mk ::
  LeaderId : w32
  Replica : w32
  Instance : w32
  Ballot : w32
  Command : List src.state.Command
  Seq : w32
  Deps : GoArray w32 5
  Base : src.gryffproto.ValTag

/-- The Go struct holding `m`, its `Command` field the slice `s` (whose elements are
`m.Command`). -/
def TryPreAccept.goVal (m : TryPreAccept.Msg) (s : GoSlice) : src.gryffproto.TryPreAccept :=
  src.gryffproto.TryPreAccept.mk m.LeaderId m.Replica m.Instance m.Ballot s m.Seq m.Deps m.Base

/-- The bytes `(*TryPreAccept).Marshal` writes. -/
def TryPreAccept.enc (m : TryPreAccept.Msg) : List w8 :=
    u32Le m.LeaderId ++
    u32Le m.Replica ++
    u32Le m.Instance ++
    u32Le m.Ballot ++
    varintEnc (sint.Z (W64 m.Command.length)) ++
    (m.Command.flatMap state.Command.enc) ++
    u32Le m.Seq ++
    arrLe32 m.Deps ++
    gryffproto.ValTag.enc m.Base

/-- `m`'s slice length is an `int64` (true of a slice in memory). -/
def TryPreAccept.wf (m : TryPreAccept.Msg) : Prop := m.Command.length < 2 ^ 63

/-- The bytes `D` after a reader's position are comparable with (a prefix or an extension of)
the encoding of some `TryPreAccept`: the length varint is that of a real slice. -/
def TryPreAccept.nextOk (D : List w8) : Prop :=
  ∃ m : TryPreAccept.Msg, TryPreAccept.wf m ∧ (D <+: TryPreAccept.enc m ∨ TryPreAccept.enc m <+: D)

end gryffproto

namespace gryffproto

/-- The values of a `gryffproto.PrepareReply` (`Command`: the elements of its `[]state.Command`). -/
structure PrepareReply.Msg where
  mk ::
  AcceptorId : w32
  Replica : w32
  Instance : w32
  OK : w8
  Ballot : w32
  VBallot : w32
  Status : w8
  Command : List src.state.Command
  Seq : w32
  Deps : GoArray w32 5
  Base : src.gryffproto.ValTag

/-- The Go struct holding `m`, its `Command` field the slice `s` (whose elements are
`m.Command`). -/
def PrepareReply.goVal (m : PrepareReply.Msg) (s : GoSlice) : src.gryffproto.PrepareReply :=
  src.gryffproto.PrepareReply.mk m.AcceptorId m.Replica m.Instance m.OK m.Ballot m.VBallot m.Status s m.Seq m.Deps m.Base

/-- The bytes `(*PrepareReply).Marshal` writes. -/
def PrepareReply.enc (m : PrepareReply.Msg) : List w8 :=
    u32Le m.AcceptorId ++
    u32Le m.Replica ++
    u32Le m.Instance ++
    [m.OK] ++
    u32Le m.Ballot ++
    u32Le m.VBallot ++
    [m.Status] ++
    varintEnc (sint.Z (W64 m.Command.length)) ++
    (m.Command.flatMap state.Command.enc) ++
    u32Le m.Seq ++
    arrLe32 m.Deps ++
    gryffproto.ValTag.enc m.Base

/-- `m`'s slice length is an `int64` (true of a slice in memory). -/
def PrepareReply.wf (m : PrepareReply.Msg) : Prop := m.Command.length < 2 ^ 63

/-- The bytes `D` after a reader's position are comparable with (a prefix or an extension of)
the encoding of some `PrepareReply`: the length varint is that of a real slice. -/
def PrepareReply.nextOk (D : List w8) : Prop :=
  ∃ m : PrepareReply.Msg, PrepareReply.wf m ∧ (D <+: PrepareReply.enc m ∨ PrepareReply.enc m <+: D)

end gryffproto

namespace gryffproto

/-- `gryffproto.Executed`'s values: Goose's representation. -/
abbrev Executed.Msg := src.gryffproto.Executed

/-- The bytes `(*Executed).Marshal` writes. -/
def Executed.enc (m : Executed.Msg) : List w8 :=
    u32Le m.Replica' ++
    u32Le m.Instance'

/-- No condition: every value is encodable. -/
def Executed.wf (_m : Executed.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Executed.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.PreAcceptOKReply`'s values: Goose's representation. -/
abbrev PreAcceptOKReply.Msg := src.gryffproto.PreAcceptOKReply

/-- The bytes `(*PreAcceptOKReply).Marshal` writes. -/
def PreAcceptOKReply.enc (m : PreAcceptOKReply.Msg) : List w8 :=
    u32Le m.Replica' ++
    u32Le m.Instance'

/-- No condition: every value is encodable. -/
def PreAcceptOKReply.wf (_m : PreAcceptOKReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def PreAcceptOKReply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace gryffproto

/-- `gryffproto.AcceptOKReply`'s values: Goose's representation. -/
abbrev AcceptOKReply.Msg := src.gryffproto.AcceptOKReply

/-- The bytes `(*AcceptOKReply).Marshal` writes. -/
def AcceptOKReply.enc (m : AcceptOKReply.Msg) : List w8 :=
    u32Le m.Replica' ++
    u32Le m.Instance'

/-- No condition: every value is encodable. -/
def AcceptOKReply.wf (_m : AcceptOKReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def AcceptOKReply.nextOk (_D : List w8) : Prop := True

end gryffproto

namespace epaxosproto

/-- `epaxosproto.Prepare`'s values: Goose's representation. -/
abbrev Prepare.Msg := src.epaxosproto.Prepare

/-- The bytes `(*Prepare).Marshal` writes. -/
def Prepare.enc (m : Prepare.Msg) : List w8 :=
    u32Le m.LeaderId' ++
    u32Le m.Replica' ++
    u32Le m.Instance' ++
    u32Le m.Ballot'

/-- No condition: every value is encodable. -/
def Prepare.wf (_m : Prepare.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Prepare.nextOk (_D : List w8) : Prop := True

end epaxosproto

namespace epaxosproto

/-- `epaxosproto.PreAcceptOK`'s values: Goose's representation. -/
abbrev PreAcceptOK.Msg := src.epaxosproto.PreAcceptOK

/-- The bytes `(*PreAcceptOK).Marshal` writes. -/
def PreAcceptOK.enc (m : PreAcceptOK.Msg) : List w8 :=
    u32Le m.Instance'

/-- No condition: every value is encodable. -/
def PreAcceptOK.wf (_m : PreAcceptOK.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def PreAcceptOK.nextOk (_D : List w8) : Prop := True

end epaxosproto

namespace epaxosproto

/-- `epaxosproto.AcceptReply`'s values: Goose's representation. -/
abbrev AcceptReply.Msg := src.epaxosproto.AcceptReply

/-- The bytes `(*AcceptReply).Marshal` writes. -/
def AcceptReply.enc (m : AcceptReply.Msg) : List w8 :=
    u32Le m.Replica' ++
    u32Le m.Instance' ++
    [m.OK'] ++
    u32Le m.Ballot'

/-- No condition: every value is encodable. -/
def AcceptReply.wf (_m : AcceptReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def AcceptReply.nextOk (_D : List w8) : Prop := True

end epaxosproto

namespace epaxosproto

/-- `epaxosproto.CommitShort`'s values: Goose's representation. -/
abbrev CommitShort.Msg := src.epaxosproto.CommitShort

/-- The bytes `(*CommitShort).Marshal` writes. -/
def CommitShort.enc (m : CommitShort.Msg) : List w8 :=
    u32Le m.LeaderId' ++
    u32Le m.Replica' ++
    u32Le m.Instance' ++
    u32Le m.Count' ++
    u32Le m.Seq' ++
    arrLe32 m.Deps'

/-- No condition: every value is encodable. -/
def CommitShort.wf (_m : CommitShort.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def CommitShort.nextOk (_D : List w8) : Prop := True

end epaxosproto

namespace epaxosproto

/-- `epaxosproto.TryPreAcceptReply`'s values: Goose's representation. -/
abbrev TryPreAcceptReply.Msg := src.epaxosproto.TryPreAcceptReply

/-- The bytes `(*TryPreAcceptReply).Marshal` writes. -/
def TryPreAcceptReply.enc (m : TryPreAcceptReply.Msg) : List w8 :=
    u32Le m.AcceptorId' ++
    u32Le m.Replica' ++
    u32Le m.Instance' ++
    [m.OK'] ++
    u32Le m.Ballot' ++
    u32Le m.ConflictReplica' ++
    u32Le m.ConflictInstance' ++
    [m.ConflictStatus']

/-- No condition: every value is encodable. -/
def TryPreAcceptReply.wf (_m : TryPreAcceptReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def TryPreAcceptReply.nextOk (_D : List w8) : Prop := True

end epaxosproto

namespace clientproto

/-- `clientproto.Ping`'s values: Goose's representation. -/
abbrev Ping.Msg := src.clientproto.Ping

/-- The bytes `(*Ping).Marshal` writes. -/
def Ping.enc (m : Ping.Msg) : List w8 :=
    u32Le m.ClientId' ++
    u64Le m.Ts'

/-- No condition: every value is encodable. -/
def Ping.wf (_m : Ping.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Ping.nextOk (_D : List w8) : Prop := True

end clientproto

namespace clientproto

/-- `clientproto.PingReply`'s values: Goose's representation. -/
abbrev PingReply.Msg := src.clientproto.PingReply

/-- The bytes `(*PingReply).Marshal` writes. -/
def PingReply.enc (m : PingReply.Msg) : List w8 :=
    u32Le m.ReplicaId' ++
    u64Le m.Ts'

/-- No condition: every value is encodable. -/
def PingReply.wf (_m : PingReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def PingReply.nextOk (_D : List w8) : Prop := True

end clientproto

namespace genericsmrproto

/-- `genericsmrproto.Beacon`'s values: Goose's representation. -/
abbrev Beacon.Msg := src.genericsmrproto.Beacon

/-- The bytes `(*Beacon).Marshal` writes. -/
def Beacon.enc (m : Beacon.Msg) : List w8 :=
    u64Le m.Timestamp'

/-- No condition: every value is encodable. -/
def Beacon.wf (_m : Beacon.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Beacon.nextOk (_D : List w8) : Prop := True

end genericsmrproto

namespace genericsmrproto

/-- `genericsmrproto.BeaconReply`'s values: Goose's representation. -/
abbrev BeaconReply.Msg := src.genericsmrproto.BeaconReply

/-- The bytes `(*BeaconReply).Marshal` writes. -/
def BeaconReply.enc (m : BeaconReply.Msg) : List w8 :=
    u64Le m.Timestamp'

/-- No condition: every value is encodable. -/
def BeaconReply.wf (_m : BeaconReply.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def BeaconReply.nextOk (_D : List w8) : Prop := True

end genericsmrproto

namespace genericsmrproto

/-- `genericsmrproto.Propose`'s values: Goose's representation. -/
abbrev Propose.Msg := src.genericsmrproto.Propose

/-- The bytes `(*Propose).Marshal` writes. -/
def Propose.enc (m : Propose.Msg) : List w8 :=
    u32Le m.CommandId' ++
    state.Command.enc m.Command' ++
    u64Le m.Timestamp'

/-- No condition: every value is encodable. -/
def Propose.wf (_m : Propose.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def Propose.nextOk (_D : List w8) : Prop := True

end genericsmrproto

namespace genericsmrproto

/-- `genericsmrproto.ProposeReplyTS`'s values: Goose's representation. -/
abbrev ProposeReplyTS.Msg := src.genericsmrproto.ProposeReplyTS

/-- The bytes `(*ProposeReplyTS).Marshal` writes. -/
def ProposeReplyTS.enc (m : ProposeReplyTS.Msg) : List w8 :=
    [m.OK'] ++
    u32Le m.CommandId' ++
    state.Value.enc m.Value' ++
    u64Le m.Timestamp'

/-- No condition: every value is encodable. -/
def ProposeReplyTS.wf (_m : ProposeReplyTS.Msg) : Prop := True

/-- No condition: `Unmarshal` handles any bytes. -/
def ProposeReplyTS.nextOk (_D : List w8) : Prop := True

end genericsmrproto
end enc

/-! ## Ownership -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace state
/-- `t` holds `m`. -/
abbrev Key.own (t : Loc) (dq : DFrac) (m : Key.Msg) : IProp GF := t ↦{dq} m

end state

namespace state
/-- `t` holds `m`. -/
abbrev Value.own (t : Loc) (dq : DFrac) (m : Value.Msg) : IProp GF := t ↦{dq} m

end state

namespace state
/-- `t` holds `m`. -/
abbrev Command.own (t : Loc) (dq : DFrac) (m : Command.Msg) : IProp GF := t ↦{dq} m

end state

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Tag.own (t : Loc) (dq : DFrac) (m : Tag.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev ValTag.own (t : Loc) (dq : DFrac) (m : ValTag.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Dep.own (t : Loc) (dq : DFrac) (m : Dep.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Read.own (t : Loc) (dq : DFrac) (m : Read.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev ReadReply.own (t : Loc) (dq : DFrac) (m : ReadReply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Write.own (t : Loc) (dq : DFrac) (m : Write.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev WriteReply.own (t : Loc) (dq : DFrac) (m : WriteReply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev RMW.own (t : Loc) (dq : DFrac) (m : RMW.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev RMWReply.own (t : Loc) (dq : DFrac) (m : RMWReply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Read1Proxied.own (t : Loc) (dq : DFrac) (m : Read1Proxied.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Read1Reply.own (t : Loc) (dq : DFrac) (m : Read1Reply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Read2Proxied.own (t : Loc) (dq : DFrac) (m : Read2Proxied.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Read2Reply.own (t : Loc) (dq : DFrac) (m : Read2Reply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Write1Proxied.own (t : Loc) (dq : DFrac) (m : Write1Proxied.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Write1Reply.own (t : Loc) (dq : DFrac) (m : Write1Reply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Write2Proxied.own (t : Loc) (dq : DFrac) (m : Write2Proxied.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Write2Reply.own (t : Loc) (dq : DFrac) (m : Write2Reply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`: the struct, its `Command` slice holding `m.Command` (both at `dq`). -/
def PreAccept.own (t : Loc) (dq : DFrac) (m : PreAccept.Msg) : IProp GF :=
  iprop(∃ s : GoSlice, t ↦{dq} PreAccept.goVal m s ∗ s ↦*{dq} m.Command)

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev PreAcceptReply.own (t : Loc) (dq : DFrac) (m : PreAcceptReply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`: the struct, its `Command` slice holding `m.Command` (both at `dq`). -/
def EAccept.own (t : Loc) (dq : DFrac) (m : EAccept.Msg) : IProp GF :=
  iprop(∃ s : GoSlice, t ↦{dq} EAccept.goVal m s ∗ s ↦*{dq} m.Command)

end gryffproto

namespace gryffproto
/-- `t` holds `m`: the struct, its `Command` slice holding `m.Command` (both at `dq`). -/
def ECommit.own (t : Loc) (dq : DFrac) (m : ECommit.Msg) : IProp GF :=
  iprop(∃ s : GoSlice, t ↦{dq} ECommit.goVal m s ∗ s ↦*{dq} m.Command)

end gryffproto

namespace gryffproto
/-- `t` holds `m`: the struct, its `Command` slice holding `m.Command` (both at `dq`). -/
def TryPreAccept.own (t : Loc) (dq : DFrac) (m : TryPreAccept.Msg) : IProp GF :=
  iprop(∃ s : GoSlice, t ↦{dq} TryPreAccept.goVal m s ∗ s ↦*{dq} m.Command)

end gryffproto

namespace gryffproto
/-- `t` holds `m`: the struct, its `Command` slice holding `m.Command` (both at `dq`). -/
def PrepareReply.own (t : Loc) (dq : DFrac) (m : PrepareReply.Msg) : IProp GF :=
  iprop(∃ s : GoSlice, t ↦{dq} PrepareReply.goVal m s ∗ s ↦*{dq} m.Command)

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev Executed.own (t : Loc) (dq : DFrac) (m : Executed.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev PreAcceptOKReply.own (t : Loc) (dq : DFrac) (m : PreAcceptOKReply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace gryffproto
/-- `t` holds `m`. -/
abbrev AcceptOKReply.own (t : Loc) (dq : DFrac) (m : AcceptOKReply.Msg) : IProp GF := t ↦{dq} m

end gryffproto

namespace epaxosproto
/-- `t` holds `m`. -/
abbrev Prepare.own (t : Loc) (dq : DFrac) (m : Prepare.Msg) : IProp GF := t ↦{dq} m

end epaxosproto

namespace epaxosproto
/-- `t` holds `m`. -/
abbrev PreAcceptOK.own (t : Loc) (dq : DFrac) (m : PreAcceptOK.Msg) : IProp GF := t ↦{dq} m

end epaxosproto

namespace epaxosproto
/-- `t` holds `m`. -/
abbrev AcceptReply.own (t : Loc) (dq : DFrac) (m : AcceptReply.Msg) : IProp GF := t ↦{dq} m

end epaxosproto

namespace epaxosproto
/-- `t` holds `m`. -/
abbrev CommitShort.own (t : Loc) (dq : DFrac) (m : CommitShort.Msg) : IProp GF := t ↦{dq} m

end epaxosproto

namespace epaxosproto
/-- `t` holds `m`. -/
abbrev TryPreAcceptReply.own (t : Loc) (dq : DFrac) (m : TryPreAcceptReply.Msg) : IProp GF := t ↦{dq} m

end epaxosproto

namespace clientproto
/-- `t` holds `m`. -/
abbrev Ping.own (t : Loc) (dq : DFrac) (m : Ping.Msg) : IProp GF := t ↦{dq} m

end clientproto

namespace clientproto
/-- `t` holds `m`. -/
abbrev PingReply.own (t : Loc) (dq : DFrac) (m : PingReply.Msg) : IProp GF := t ↦{dq} m

end clientproto

namespace genericsmrproto
/-- `t` holds `m`. -/
abbrev Beacon.own (t : Loc) (dq : DFrac) (m : Beacon.Msg) : IProp GF := t ↦{dq} m

end genericsmrproto

namespace genericsmrproto
/-- `t` holds `m`. -/
abbrev BeaconReply.own (t : Loc) (dq : DFrac) (m : BeaconReply.Msg) : IProp GF := t ↦{dq} m

end genericsmrproto

namespace genericsmrproto
/-- `t` holds `m`. -/
abbrev Propose.own (t : Loc) (dq : DFrac) (m : Propose.Msg) : IProp GF := t ↦{dq} m

end genericsmrproto

namespace genericsmrproto
/-- `t` holds `m`. -/
abbrev ProposeReplyTS.own (t : Loc) (dq : DFrac) (m : ProposeReplyTS.Msg) : IProp GF := t ↦{dq} m

end genericsmrproto
end own

end Perennial.gryff.wire
