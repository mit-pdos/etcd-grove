/-
`client/v3/leasing`'s evaluation of a transaction against the lease cache (`util.go`'s `evalCmp`,
`cache.go`'s `leaseCache.evalCmp` and `evalOps`, used by `txnLeasing.eval`): what they compute.
Lean-first (no Rocq counterpart).

**`evalCmp(resp, cmp)`** compares the cached key-value (`resp.Kvs[0]`), if any, with the
comparison's operand: its sign is `0` when nothing is cached, and for a lease comparison (the
switch has no `LEASE` case); otherwise the target's comparison (`bytes.Compare` of the values,
`compareInt64` of the revisions or versions). The operator is then applied to that sign
(`leaseCmpHolds`). **This is not etcd's `applyCompare`** (`cmpHolds`): on a key known to be absent
etcd compares the zero key-value (so `CreateRevision(k) < 5` holds, `Version(k) = 3` fails) and
fails a value comparison, while `evalCmp` compares `0` with nothing (`<` fails, `=` holds); and a
lease comparison always holds for `=`. A transaction whose keys are all cached is answered from the
cache with `evalCmp`'s outcome (a finding, `notes/STATUS.md`).

**`lc.evalCmp(cmps)`** (the caller holds the read lock): `(false, false)` at the first comparison
of a range or of a key not cached, `(false, true)` at the first failing one, else `(true, true)`
(`leaseEvalCmps`). **`lc.evalOps(ops)`**: every operation a get the cache serves, of a cached key
(`leaseEvalOk`): their cached answers, each in a fresh `ResponseOp`; otherwise `(nil, false)`.

The comparisons evaluated are `Compare(...)`'s (`cmpSetAt`: the operand is set, as `Compare`
sets it); a comparison with no operand (`Value(k)` alone) reads none in `evalCmp` and the empty
value or `0` in etcd.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section model
variable [ext : FfiSyntax]

/-- `evalCmp`'s sign of the cached key-value `kv` against `m`: `0` with none, or for a lease
target. -/
def leaseCmpSign (m : CmpModel) : Option EtcdKv → Int
  | none => 0
  | some v => match m.target with
    | .value => bytesCmp v.value m.val
    | .create => int64Cmp v.createRev m.num
    | .mod => int64Cmp v.modRev m.num
    | .version => int64Cmp v.version m.num
    | .lease => 0

/-- `evalCmp(resp, cmp)`'s result. -/
def leaseCmpHolds (m : CmpModel) (kv : Option EtcdKv) : Bool := m.op.holds (leaseCmpSign m kv)

/-- `lc.evalCmp(cmps)`'s result `(cmpVal, ok)` on the state `st`. -/
def leaseEvalCmps (st : LeaseCacheSt) : List CmpModel → Bool × Bool
  | [] => (true, true)
  | m :: ms =>
    if m.rangeEnd ≠ [] then (false, false)
    else match st.entries !! m.key with
      | none => (false, false)
      | some e => if leaseCmpHolds m e.kv then leaseEvalCmps st ms else (false, true)

/-- `lc.evalOps(ops)`'s `ok`: every operation a get the cache serves (`isBadOp`), of a cached key. -/
def leaseEvalOk (st : LeaseCacheSt) (os : List OpFull) : Bool :=
  os.all (fun o => decide (o.t = W64 1) && !isBadOpM o && (st.entries !! o.key).isSome)

end model

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- The `Cmp` value `c` is a comparison modelled by `m` whose operand is set (`cmpAt`, with the
`TargetUnion` a wrapper, not nil, at a non-nil address: `Compare(...)` allocates the wrapper,
`&pb.Compare_Value{...}`, and `evalCmp` tests `tv != nil`). Persistent. -/
def cmpSetAt (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) : IProp GF :=
  iprop(⌜c.c' ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (u : GoInterface),
    structFieldRef etcdserverpb.Compare go!"Result" c.c' ↦□ m.op.code ∗
    structFieldRef etcdserverpb.Compare go!"Target" c.c' ↦□ m.target.code ∗
    structFieldRef etcdserverpb.Compare go!"Key" c.c' ↦□ ksl ∗ ksl ↦*□ m.key ∗
    structFieldRef etcdserverpb.Compare go!"RangeEnd" c.c' ↦□ esl ∗ esl ↦*□ m.rangeEnd ∗
    structFieldRef etcdserverpb.Compare go!"TargetUnion" c.c' ↦□ u ∗ compareUnionAt u m ∗
    ⌜u ≠ interface.nil⌝ ∗ ⌜∀ (t : go.GoType) (w : Loc), u = interface.mkOk t #w → w ≠ null⌝)

instance cmpSetAt_persistent (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) :
    Persistent (cmpSetAt (GF := GF) c m) := by
  unfold cmpSetAt; infer_instance

/-- The `[]Cmp` slice `sl` (read-only) holds comparisons modelled by `ms` with their operands set. -/
def cmpsSetAt (sl : GoSlice) (ms : List CmpModel) : IProp GF :=
  iprop(∃ cs : List go_etcd_io.etcd.client.v3.Cmp, sl ↦*□ cs ∗ ⌜cs.length = ms.length⌝ ∗
    □ ∀ (i : Nat) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel), ⌜cs[i]? = some c⌝ -∗
      ⌜ms[i]? = some m⌝ -∗ cmpSetAt c m)

instance cmpsSetAt_persistent (sl : GoSlice) (ms : List CmpModel) :
    Persistent (cmpsSetAt (GF := GF) sl ms) := by
  unfold cmpsSetAt; infer_instance

/-- A fresh `*pb.ResponseOp` `p` (owned) wrapping the cached get's answer to `o` from the entry
`e` (a fresh response, `freshGetResp`). -/
def respOpFresh (p : Loc) (o : OpFull) (e : LeaseEntry) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
    structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦
      interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
    structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦ r ∗
    freshGetResp r e.hm e.more e.count (getResult o e))

end defs

end EtcdGrove
end Perennial
