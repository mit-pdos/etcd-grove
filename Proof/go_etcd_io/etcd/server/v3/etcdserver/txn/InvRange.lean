/-
The server's range in the heap (unit 2): what `executeRange`'s helpers own. Lean-first;
`RangeModel.lean` for the pure side.

* `kvAt p v`: an owned `*mvccpb.KeyValue` holding `v`: mvcc's fresh key-values
  (`kvPtrIs true`); a fast keys-only read's (`kvPtrIs false`) is one holding `kvRead true v`
  (`kvPtrIs_false`).
* `kvsAt l`: the owned key-values of `l` (pointer, value), as `sort.Sort`'s sorter holds them;
  `kvsOwnAt sl l`: the slice `sl` holds `l`'s pointers, in order, and their key-values.
* `rangeResultIs rr rev count vs`: a `*mvcc.RangeResult` holding the key-values `vs` (its
  `KVs` slice owned, element by element), `Rev`, `Count`: what mvcc's `Range` returns
  (`rangeKvs`), and what `filterRangeResults` (`pruneKVs`), `sortRangeResults` and
  `asembleRangeResponse` work on.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- An owned `*mvccpb.KeyValue` at `p` holding `v` (mvcc's fresh key-values). -/
abbrev kvAt (p : Loc) (v : EtcdKv) : IProp GF := mvcc.kvPtrIs true p v

/-- The owned key-values of `l` (pointer, value). -/
def kvsAt (l : List (Loc × EtcdKv)) : IProp GF := iprop([∗list] x ∈ l, kvAt x.1 x.2)

/-- The slice `sl` holds `l`'s pointers, in order, and their key-values are owned. -/
def kvsOwnAt (sl : GoSlice) (l : List (Loc × EtcdKv)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ kvsAt l)

/-- **A `*mvcc.RangeResult`** at `rr` holding the key-values `vs` (owned), `Rev` and `Count`. -/
def rangeResultIs (rr : Loc) (rev count : w64) (vs : List EtcdKv) : IProp GF :=
  iprop(∃ (sl : GoSlice) (l : List (Loc × EtcdKv)), ⌜l.map Prod.snd = vs⌝ ∗
    rr ↦ ({ KVs' := sl, Rev' := rev, Count' := count } : RangeResult) ∗ kvsOwnAt sl l)

/-- **What `executeRange` (and `Range`) return** for the request `o` on the read transaction of
the committed log `log` at revision `rev`, with `withTotal`:
* a future revision (`o.base.rev > rev`): no response, mvcc's `ErrFutureRev`;
* the context done (mvcc's `rangeOutcome`: a full read checks `ctx.Done()`): no response and an
  error;
* else a response at header revision `rev`, its key-values and `More` the server's selection
  of the state at the revision read (`rangeRev rev o.base.rev`: `srvRangeOk`), its count
  `srvCount`. -/
def rangeResult (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (o : OpFull)
    (withTotal : Bool) : IProp GF :=
  iprop(
    (⌜sint.Z rev < sint.Z o.base.rev ∧ resp = null⌝ ∗
      ∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∨
    (⌜sint.Z o.base.rev ≤ sint.Z rev ∧ o.base.countOnly = false ∧ fastKeysOnly o = false ∧
      resp = null ∧ err ≠ GoInterface.nil⌝) ∨
    (⌜sint.Z o.base.rev ≤ sint.Z rev ∧ err = GoInterface.nil⌝ ∗ ∃ (kvs : List EtcdKv) (more : Bool),
      rangeResponseIs resp rev kvs more
        (srvCount o (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev o.base.rev))) withTotal) ∗
      ⌜srvRangeOk o (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev o.base.rev))) kvs more⌝))

/-- **What `checkRange` returns** for the request `o` on a read transaction at revision `rev`
(whose first revision is `-1`): `nil` for revision `0` or in `[-1, rev]`; mvcc's `ErrFutureRev`
above `rev`; mvcc's `ErrCompacted` below `-1`. -/
def checkRangeErr (rev : w64) (o : OpFull) (err : GoInterface) : IProp GF :=
  iprop(
    ⌜err = GoInterface.nil ∧
      (o.base.rev = W64 0 ∨ (sint.Z o.base.rev ≤ sint.Z rev ∧ -1 ≤ sint.Z o.base.rev))⌝ ∨
    (⌜o.base.rev ≠ W64 0 ∧ sint.Z rev < sint.Z o.base.rev⌝ ∗
      ∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∨
    (⌜o.base.rev ≠ W64 0 ∧ sint.Z o.base.rev ≤ sint.Z rev ∧ sint.Z o.base.rev < -1⌝ ∗
      ∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝))

instance rangeResult_persistent (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64)
    (o : OpFull) (withTotal : Bool) : Persistent (rangeResult (GF := GF) resp err log rev o withTotal) := by
  unfold rangeResult; infer_instance

instance checkRangeErr_persistent (rev : w64) (o : OpFull) (err : GoInterface) :
    Persistent (checkRangeErr (GF := GF) rev o err) := by
  unfold checkRangeErr; infer_instance

end defs

/-- `bytes.Compare(a, b) < 0` is `a < b`. -/
theorem compareResult_neg (x y : GoString) :
    decide (sint.Z (bytes.compareResult x y) < sint.Z (W64 0)) = decide (go.GoStringLt x y) := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt x y
  · simp only [h, ↓reduceIte, decide_true]; decide
  · simp only [h, ↓reduceIte, decide_false]
    split <;> decide

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A fast keys-only read's key-value is an owned one without value and lease. -/
theorem kvPtrIs_false (p : Loc) (v : EtcdKv) :
    mvcc.kvPtrIs (GF := GF) false p v ⊢ |==> kvAt p (kvRead true v) := by
  simp only [kvAt, mvcc.kvPtrIs, kvRead, ↓reduceIte, Bool.false_eq_true]
  iintro ⟨%ks, %st, %uf, %sc, #Hk, Hp⟩
  ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imodintro
  iexists ks, st, uf, sc
  isplitr
  · iexact Hk
  iexists slice.nil
  isplitr
  · iexact Hnil
  iexact Hp

theorem kvsAt_cons (x : Loc × EtcdKv) (l : List (Loc × EtcdKv)) :
    kvsAt (GF := GF) (x :: l) ⊣⊢ kvAt x.1 x.2 ∗ kvsAt l := by
  unfold kvsAt; exact BigSepL.bigSepL_cons

/-- The `k`-th owned key-value, and back. -/
theorem kvsAt_acc (l : List (Loc × EtcdKv)) (k : Nat) (x : Loc × EtcdKv) (h : l[k]? = some x) :
    kvsAt (GF := GF) l ⊢ kvAt x.1 x.2 ∗ (kvAt x.1 x.2 -∗ kvsAt l) := by
  have hs : l.set k x = l := by
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_set]
    split
    · rename_i hn; subst hn; rw [h]; simp [(List.getElem?_eq_some_iff.1 h).1]
    · rfl
  unfold kvsAt
  refine (BigSepL.bigSepL_lookup_acc (PROP := IProp GF) (Φ := fun _ y => kvAt y.1 y.2) h).1.trans ?_
  iintro ⟨H, Hw⟩
  iframe H
  iintro H
  ihave Hr := Hw $$ %x H
  rw [hs]
  iexact Hr

theorem kvsAt_nil : ⊢ kvsAt (GF := GF) [] := by
  unfold kvsAt; exact BigSepL.bigSepL_nil.2

end lemmas

end txn
end EtcdGrove
end Perennial
