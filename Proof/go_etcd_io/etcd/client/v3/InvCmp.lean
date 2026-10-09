/-
The vocabulary of `clientv3`'s comparisons (`client/v3/compare.go`), as a transaction's `If`
takes them: the model `CmpModel` of a `Cmp`, the predicate `cmpAt` relating a `Cmp` value to it,
and the models of the builders (`Value`, `Version`, `CreateRevision`, `ModRevision`,
`LeaseValue`, `Compare`, `Cmp.WithRange`, `Cmp.WithPrefix`). Lean-first (no Rocq counterpart).
What a comparison *means* (`cmpHolds`, etcd's rule) is in `InvEtcdTxn.lean`.

**`Cmp` models.** A `Cmp` is a pointer to a `pb.Compare`; `cmpAt c m` says that its fields hold,
for good (read-only), `m`'s key, range end, target, result (the comparison operator) and operand
(`TargetUnion`, a oneof: a `*pb.Compare_Value`, `_Version`, `_CreateRevision`, `_ModRevision` or
`_Lease` wrapper matching the target, or nil, which etcd reads as the empty value or `0`). The
fields are stated one by one (as `kvValAt` does for `mvccpb.KeyValue`), not as a struct
points-to: the message's opaque protobuf state is never read.

**`proto.Clone`.** `Compare(cmp, ...)` and `Cmp.WithRange`/`WithPrefix` clone the comparison
(`cmp.Clone()`, `cloneCompare`, protobuf's `proto.Clone`, which Goose does not translate) before
writing the clone: `compareOwn p m` is a clone's fields, owned. `proto.Clone`'s specification
(of a `*pb.Compare`) is the trust boundary (`Proof/google_golang_org/protobuf/proto/Clone.lean`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The model -/

/-- `pb.Compare_CompareTarget`: what a comparison reads of a key. -/
inductive CmpTarget where
  | version | create | mod | value | lease
  deriving DecidableEq

/-- `pb.Compare_CompareTarget`'s values (`VERSION = 0`, ..., `LEASE = 4`). -/
def CmpTarget.code : CmpTarget → w32
  | .version => W32 0 | .create => W32 1 | .mod => W32 2 | .value => W32 3 | .lease => W32 4

/-- `pb.Compare_CompareResult`: the comparison operator. -/
inductive CmpOp where
  | eq | gt | lt | neq
  deriving DecidableEq

/-- `pb.Compare_CompareResult`'s values (`EQUAL = 0`, `GREATER = 1`, `LESS = 2`,
`NOT_EQUAL = 3`). -/
def CmpOp.code : CmpOp → w32
  | .eq => W32 0 | .gt => W32 1 | .lt => W32 2 | .neq => W32 3

/-- `Compare(cmp, result, v)`'s `result` string: `"="`, `"!="`, `">"`, `"<"` (anything else
panics). -/
def cmpOpOf (result : GoString) : Option CmpOp :=
  if result = go!"=" then some .eq
  else if result = go!"!=" then some .neq
  else if result = go!">" then some .gt
  else if result = go!"<" then some .lt
  else none

/-- A comparison (`clientv3.Cmp`, a `pb.Compare`): the key, the range end (empty: the key alone;
`[0]`: every key from `key` on; otherwise `[key, rangeEnd)`), the target, the operator, and the
operand: `num` for a version, revision or lease comparison, `val` for a value comparison. -/
structure CmpModel where
  key : GoString
  rangeEnd : GoString
  target : CmpTarget
  op : CmpOp
  num : w64
  val : GoString

/-- `Value(key)`, `Version(key)`, `CreateRevision(key)`, `ModRevision(key)`, `LeaseValue(key)`:
`&pb.Compare{Key: []byte(key), Target: target}` (operator `EQUAL`, no operand). -/
def cmpKeyM (t : CmpTarget) (key : GoString) : CmpModel :=
  { key := key, rangeEnd := [], target := t, op := .eq, num := W64 0, val := [] }

/-- `Compare`'s operand `v` (an `any`). -/
inductive CmpArg where
  | num (n : w64)
  | str (s : GoString)

/-- `Compare(cmp, result, v)`: the comparison `cmp` with operator `op` and operand `v`. -/
def compareM (m : CmpModel) (op : CmpOp) : CmpArg → CmpModel
  | .num n => { m with op := op, num := n, val := [] }
  | .str s => { m with op := op, num := W64 0, val := s }

/-- `cmp.WithRange(end)` -/
def cmpWithRangeM (endKey : GoString) (m : CmpModel) : CmpModel := { m with rangeEnd := endKey }

/-- `cmp.WithPrefix()`: the keys with prefix `key` (`getPrefix(key)`: every key from `"\x00"`...
for an empty key, `[0]`). -/
def cmpWithPrefixM (m : CmpModel) : CmpModel := { m with rangeEnd := prefixRangeEnd m.key }

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `Compare(cmp, result, v)`'s operand: for a value comparison a `string`; for a lease
comparison an `int64`, an `int` or a `LeaseID` (`mustInt64orLeaseID`); for the others an `int64`
or an `int` (`mustInt64`). Anything else panics. -/
def cmpArgOf (t : CmpTarget) (v : GoInterface) (x : CmpArg) : Prop :=
  match t with
  | .value => ∃ s : GoString, v = interface.mkOk go.string #s ∧ x = .str s
  | .lease => ∃ n : w64, (v = interface.mkOk go.int64 #n ∨ v = interface.mkOk go.int #n ∨
      v = interface.mkOk go_etcd_io.etcd.client.v3.LeaseID.ty #n) ∧ x = .num n
  | _ => ∃ n : w64, (v = interface.mkOk go.int64 #n ∨ v = interface.mkOk go.int #n) ∧ x = .num n

/-- The comparison's operand `u` (`TargetUnion`, read-only): nil (etcd reads the empty value or
`0`), or the wrapper of the target's type holding `m`'s operand. -/
def compareUnionAt (u : GoInterface) (m : CmpModel) : IProp GF :=
  match m.target with
  | .value => iprop(⌜u = interface.nil ∧ m.val = []⌝ ∨
      ∃ (w : Loc) (vsl : GoSlice),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_Value.ty) #w⌝ ∗
        structFieldRef etcdserverpb.Compare_Value go!"Value" w ↦□ vsl ∗ vsl ↦*□ m.val)
  | .version => iprop(⌜u = interface.nil ∧ m.num = W64 0⌝ ∨
      ∃ w : Loc, ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_Version.ty) #w⌝ ∗
        structFieldRef etcdserverpb.Compare_Version go!"Version" w ↦□ m.num)
  | .create => iprop(⌜u = interface.nil ∧ m.num = W64 0⌝ ∨
      ∃ w : Loc,
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_CreateRevision.ty) #w⌝ ∗
        structFieldRef etcdserverpb.Compare_CreateRevision go!"CreateRevision" w ↦□ m.num)
  | .mod => iprop(⌜u = interface.nil ∧ m.num = W64 0⌝ ∨
      ∃ w : Loc,
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_ModRevision.ty) #w⌝ ∗
        structFieldRef etcdserverpb.Compare_ModRevision go!"ModRevision" w ↦□ m.num)
  | .lease => iprop(⌜u = interface.nil ∧ m.num = W64 0⌝ ∨
      ∃ w : Loc, ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_Lease.ty) #w⌝ ∗
        structFieldRef etcdserverpb.Compare_Lease go!"Lease" w ↦□ m.num)

instance compareUnionAt_persistent (u : GoInterface) (m : CmpModel) :
    Persistent (compareUnionAt (GF := GF) u m) := by
  unfold compareUnionAt; split <;> infer_instance

/-- The `*pb.Compare` `p` holds `m`, for good (its fields read-only; the byte slices and the
operand's wrapper too). -/
def compareAt (p : Loc) (m : CmpModel) : IProp GF :=
  iprop(∃ (ksl esl : GoSlice) (u : GoInterface),
    structFieldRef etcdserverpb.Compare go!"Result" p ↦□ m.op.code ∗
    structFieldRef etcdserverpb.Compare go!"Target" p ↦□ m.target.code ∗
    structFieldRef etcdserverpb.Compare go!"Key" p ↦□ ksl ∗ ksl ↦*□ m.key ∗
    structFieldRef etcdserverpb.Compare go!"RangeEnd" p ↦□ esl ∗ esl ↦*□ m.rangeEnd ∗
    structFieldRef etcdserverpb.Compare go!"TargetUnion" p ↦□ u ∗ compareUnionAt u m)

instance compareAt_persistent (p : Loc) (m : CmpModel) : Persistent (compareAt (GF := GF) p m) := by
  unfold compareAt; infer_instance

/-- A clone of a comparison holding `m` (`proto.Clone`'s result): the fields it writes
(`Result`, `TargetUnion`, `RangeEnd`) owned, the others and the contents read-only. -/
def compareOwn (p : Loc) (m : CmpModel) : IProp GF :=
  iprop(∃ (ksl esl : GoSlice) (u : GoInterface),
    structFieldRef etcdserverpb.Compare go!"Result" p ↦ m.op.code ∗
    structFieldRef etcdserverpb.Compare go!"Target" p ↦□ m.target.code ∗
    structFieldRef etcdserverpb.Compare go!"Key" p ↦□ ksl ∗ ksl ↦*□ m.key ∗
    structFieldRef etcdserverpb.Compare go!"RangeEnd" p ↦ esl ∗ esl ↦*□ m.rangeEnd ∗
    structFieldRef etcdserverpb.Compare go!"TargetUnion" p ↦ u ∗ compareUnionAt u m)

/-- The `Cmp` value `c` is a comparison modelled by `m` (its `*pb.Compare` is not nil). -/
def cmpAt (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) : IProp GF :=
  iprop(⌜c.c' ≠ null⌝ ∗ compareAt c.c' m)

instance cmpAt_persistent (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) :
    Persistent (cmpAt (GF := GF) c m) := by
  unfold cmpAt; infer_instance

/-- The `[]Cmp` slice `sl` (read-only) holds comparisons modelled by `ms`, in order. -/
def cmpsAt (sl : GoSlice) (ms : List CmpModel) : IProp GF :=
  iprop(∃ cs : List go_etcd_io.etcd.client.v3.Cmp, sl ↦*□ cs ∗ ⌜cs.length = ms.length⌝ ∗
    □ ∀ (i : Nat) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel), ⌜cs[i]? = some c⌝ -∗
      ⌜ms[i]? = some m⌝ -∗ cmpAt c m)

instance cmpsAt_persistent (sl : GoSlice) (ms : List CmpModel) :
    Persistent (cmpsAt (GF := GF) sl ms) := by
  unfold cmpsAt; infer_instance

/-- The `[]Op` slice `sl` (read-only) holds operations modelled by `os`, in order. -/
def opsAt (sl : GoSlice) (os : List OpFull) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.Op, sl ↦*□ vs ∗ ⌜vs.length = os.length⌝ ∗
    □ ∀ (i : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs[i]? = some v⌝ -∗
      ⌜os[i]? = some o⌝ -∗ opFullAt v o)

instance opsAt_persistent (sl : GoSlice) (os : List OpFull) :
    Persistent (opsAt (GF := GF) sl os) := by
  unfold opsAt; infer_instance

end defs

end EtcdGrove
end Perennial
