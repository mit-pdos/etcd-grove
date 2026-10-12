/-
The freelist interface (`freelist.Interface`) as its users (the `bbolt` package) see it: the
spec of each of its methods, called through the interface value of an implementation `I`, on
the whole freelist `ownFL I s σ`, and `FLImpl.IfaceContract`, the record of them that
`array` (and `hashMap`) meet.

The specs are functional on `FLState`, up to `FLState.equiv` where the Go code keeps only what
its users observe: the order of the free ids before they are sorted again, of the read-only
transactions, and of the (id, allocating transaction) pairs of a pending entry
(`ReleasePendingPages` swaps them around).

`Rollback` and `ReleasePendingPages` (through `release` and `releaseRange`) delete map entries
while ranging over the map, which Go allows and the GooseLang map model does not (the range
body runs under a read of the map): their specs here are stated, not proved.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Read
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- A pending entry's (id, allocating transaction) pairs. -/
def Pending.pairs (pd : Pending) : List (w64 × w64) := pd.ids.zip pd.alloctx

/-- Two pending entries agree up to the order of their pairs. -/
def Pending.equiv (p q : Pending) : Prop :=
  p.pairs.Perm q.pairs ∧ p.lastReleaseBegin = q.lastReleaseBegin

/-- Two states agree up to the order of the free ids, of the read-only transactions and of
each pending entry's pairs. -/
def FLState.equiv (σ τ : FLState) : Prop :=
  σ.free.Perm τ.free ∧ σ.readonly.Perm τ.readonly ∧ σ.allocs = τ.allocs ∧
  (∀ t, (σ.pending !! t).isSome ↔ (τ.pending !! t).isSome) ∧
  ∀ t p q, σ.pending !! t = some p → τ.pending !! t = some q → p.equiv q

/-- `Rollback(txid)` does not panic: no page `txid` freed was allocated by `txid`. -/
def FLState.canRollback (σ : FLState) (txid : w64) : Prop :=
  ∀ pd, σ.pending !! txid = some pd → ∀ t ∈ pd.alloctx, t ≠ W64 0 → t ≠ txid

/-- `σ` after `Rollback(txid)`: the pages `txid` freed are allocated again (by the transactions
that allocated them, when known), and `txid` allocated nothing. -/
def FLState.rollback (σ : FLState) (txid : w64) : FLState :=
  match σ.pending !! txid with
  | none => σ
  | some pd =>
    { σ with
      pending := GMap.delete txid σ.pending,
      allocs := GMap.filter (fun _ t => decide (t ≠ txid))
        (pd.pairs.foldl (fun m x => if x.2 = W64 0 then m else <[x.1 := x.2]> m) σ.allocs) }

/-- `t` is in the transaction range `[b, e]`. -/
def inTxRange (b e t : w64) : Bool := decide (uint.Z b ≤ uint.Z t ∧ uint.Z t ≤ uint.Z e)

/-- `σ` after `release(txid)`: the pages pending for transactions up to `txid` are free. -/
def FLState.release (σ : FLState) (txid : w64) : FLState :=
  { σ with
    free := σ.free ++ flatIds (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid))),
    pending := σ.pending.filter (fun t _ => decide (uint.Z txid < uint.Z t)) }

/-- `σ` after `releaseRange(b, e)`: each entry of a transaction in `[b, e]` not already looked
at from `b` frees its pages allocated in `[b, e]` (and is dropped if none is left). -/
def FLState.releaseRange (σ : FLState) (b e : w64) : FLState :=
  if uint.Z e < uint.Z b then σ else
  let touched (t : w64) (pd : Pending) : Bool := inTxRange b e t && pd.lastReleaseBegin != b
  let keep (pd : Pending) : Pending :=
    let k := pd.pairs.filter (fun x => !inTxRange b e x.2)
    ⟨k.map Prod.fst, k.map Prod.snd, b⟩
  let rel (pd : Pending) : List w64 := (pd.pairs.filter (fun x => inTxRange b e x.2)).map Prod.fst
  let done := σ.pending.filter touched
  { σ with
    free := σ.free ++ done.toList.flatMap (fun kv => rel kv.2),
    pending := σ.pending.filter (fun t pd => !touched t pd) ∪
      (done.fmap keep).filter (fun _ pd => !pd.ids.isEmpty) }

/-- The read-only transactions, sorted. -/
def sortedTxids (l : List w64) : List w64 := l.mergeSort (fun a b => decide (uint.Z a ≤ uint.Z b))

/-- `σ` after `ReleasePendingPages()`: the pages freed before the oldest read-only transaction
are free, and so are those both allocated and freed between two consecutive read-only
transactions (after the newest); the read-only transactions are sorted. -/
def FLState.releasePending (σ : FLState) : FLState :=
  let ro := sortedTxids σ.readonly
  let minid := ro.headD (W64 (2 ^ 64 - 1))
  let σ1 := if 0 < uint.Z minid then σ.release (minid - W64 1) else σ
  let acc := ro.foldl (fun (acc : FLState × w64) tid =>
    (acc.1.releaseRange acc.2 (tid - W64 1), tid + W64 1)) (σ1, minid)
  { acc.1.releaseRange acc.2 (W64 (2 ^ 64 - 1)) with readonly := ro }

section specs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `AddReadonlyTXID(tid)`: `tid` is a read-only transaction. -/
def FLImpl.AddReadonlySpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (tid : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"AddReadonlyTXID" I.iv)) (Val #tid))
    {{ RET #(); ownFL I s { σ with readonly := σ.readonly ++ [tid] } }}

/-- `RemoveReadonlyTXID(tid)`: one `tid` is no longer a read-only transaction (the rest in
some order: `shared`'s swaps the last one into its place). -/
def FLImpl.RemoveReadonlySpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (tid : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"RemoveReadonlyTXID" I.iv)) (Val #tid))
    {{ (ro : List w64), RET #(); ⌜ro.Perm (σ.readonly.erase tid)⌝ ∗
        ownFL I s { σ with readonly := ro } }}

/-- `ReleasePendingPages()` (`FLState.releasePending`, up to order). -/
def FLImpl.ReleasePendingSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"ReleasePendingPages" I.iv)) (Val #()))
    {{ (σ' : FLState), RET #(); ⌜σ'.equiv σ.releasePending⌝ ∗ ownFL I s σ' }}

/-- `Free(txid, p)`: the page `p` and its overflow pages are pending for `txid`. -/
def FLImpl.FreeSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (txid : w64) (p : Loc)
    (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac),
    σ.canFree txid pv.id' (uint.nat pv.overflow' + 1) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦{dq} pv }}
      (App (App (Val #(methods I.ity go!"Free" I.iv)) (Val #txid)) (Val #p))
    {{ RET #(); ownFL I s (σ.freePages txid pv.id' (uint.nat pv.overflow' + 1)) ∗ p ↦{dq} pv }}

/-- `Rollback(txid)` (`FLState.rollback`). -/
def FLImpl.RollbackSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (txid : w64), σ.canRollback txid →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"Rollback" I.iv)) (Val #txid))
    {{ RET #(); ownFL I s (σ.rollback txid) }}

/-- `Freed(id)`: `id` is free or pending. -/
def FLImpl.FreedSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (id : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"Freed" I.iv)) (Val #id))
    {{ RET #(decide (σ.cached id)); ownFL I s σ }}

/-- `FreeCount()`: the number of free ids. -/
def FLImpl.IfaceFreeCountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"FreeCount" I.iv)) (Val #()))
    {{ RET #(W64 (σ.free.length : Int)); ownFL I s σ }}

/-- `PendingCount()`: the number of pending ids. -/
def FLImpl.PendingCountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"PendingCount" I.iv)) (Val #()))
    {{ RET #(W64 (σ.pendingCount : Int)); ownFL I s σ }}

/-- `Count()`: the number of free and pending ids. -/
def FLImpl.CountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"Count" I.iv)) (Val #()))
    {{ RET #(W64 ((σ.free.length + σ.pendingCount : Nat) : Int)); ownFL I s σ }}

/-- `Read(p)`: the free ids become the ids of the freelist page `p`, sorted. -/
def FLImpl.ReadSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (p : Loc) (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac)
    (c : w64) (xs : List w64) (dq2 : DFrac),
    p.locCar ≠ 0 → pv.flags' = W16 16 → (fpOverflow pv → 0 ≤ sint.Z c) →
    xs.Nodup → (∀ x ∈ xs, 2 ≤ uint.Z x ∧ x ∉ σ.pendingIds) → xs.length + σ.pendingCount < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}
      (App (Val #(methods I.ity go!"Read" I.iv)) (Val #p))
    {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm xs⌝ ∗
        ownFL I s { σ with free := free' } ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}

/-- `Reload(p)`: as `Read(p)` (no page id is pending). -/
def FLImpl.ReloadSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (p : Loc) (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac)
    (c : w64) (xs : List w64) (dq2 : DFrac),
    p.locCar ≠ 0 → pv.flags' = W16 16 → (fpOverflow pv → 0 ≤ sint.Z c) →
    xs.Nodup → (∀ x ∈ xs, 2 ≤ uint.Z x ∧ x ∉ σ.pendingIds) → xs.length + σ.pendingCount < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}
      (App (Val #(methods I.ity go!"Reload" I.iv)) (Val #p))
    {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm xs⌝ ∗
        ownFL I s { σ with free := free' } ∗
        p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}

/-- `NoSyncReload(pgIds)`: the free ids become the increasing ids `pgIds` but the pending ones. -/
def FLImpl.NoSyncReloadSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (pg : GoSlice) (xs : List w64) (dq : DFrac),
    PgidsIncr xs → (∀ x ∈ xs, 2 ≤ uint.Z x) → xs.length + σ.pendingCount < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        pg ↦*{dq} xs }}
      (App (Val #(methods I.ity go!"NoSyncReload" I.iv)) (Val #pg))
    {{ RET #(); ownFL I s { σ with free := xs.filter (fun x => decide (x ∉ σ.pendingIds)) } ∗
        pg ↦*{dq} xs }}

/-- `EstimatedWritePageSize()`: the size of the page `Write` writes. -/
def FLImpl.EstimatedWritePageSizeSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ }}
      (App (Val #(methods I.ity go!"EstimatedWritePageSize" I.iv)) (Val #()))
    {{ RET #(W64 (16 + 8 * (flCells σ.allIds.length : Nat))); ownFL I s σ }}

/-- `Write(p)`: `p` becomes a freelist page of the free and pending ids, sorted. -/
def FLImpl.WriteSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (p : Loc) (pv : go_etcd_io.bbolt.internal.common.Page)
    (old : List w64),
    p.locCar ≠ 0 → old.length = flCells σ.allIds.length →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        p ↦ pv ∗ slice.mk (p +ₗ 16) (W64 (old.length : Int)) (W64 (old.length : Int)) ↦* old }}
      (App (Val #(methods I.ity go!"Write" I.iv)) (Val #p))
    {{ (out : List w64), RET #(); ⌜PgidsSorted out ∧ out.Perm σ.allIds⌝ ∗ ownFL I s σ ∗
        p ↦ ({ pv with flags' := W16 16, count' := flCount σ.allIds.length } :
          go_etcd_io.bbolt.internal.common.Page) ∗
        slice.mk (p +ₗ 16) (W64 (old.length : Int)) (W64 (old.length : Int)) ↦*
          (if 65535 ≤ σ.allIds.length then W64 (σ.allIds.length : Int) :: out else out) }}

/-- `Init(ids)`: the free ids become `ids` (the new state well-formed; the slice is kept). -/
def FLImpl.IfaceInitSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (ids : GoSlice) (xs : List w64),
    ({ σ with free := xs } : FLState).WF →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL I s σ ∗
        ids ↦* xs ∗ ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"Init" I.iv)) (Val #ids))
    {{ RET #(); ownFL I s { σ with free := xs } }}

/-- The freelist interface's methods, as its users call them. -/
structure FLImpl.IfaceContract (I : FLImpl (GF := GF)) : Prop where
  addReadonly : I.AddReadonlySpec
  removeReadonly : I.RemoveReadonlySpec
  releasePending : I.ReleasePendingSpec
  allocate : I.AllocateSpec
  free : I.FreeSpec
  rollback : I.RollbackSpec
  freed : I.FreedSpec
  freeCount : I.IfaceFreeCountSpec
  pendingCount : I.PendingCountSpec
  count : I.CountSpec
  read : I.ReadSpec
  write : I.WriteSpec
  estimatedWritePageSize : I.EstimatedWritePageSizeSpec
  reload : I.ReloadSpec
  noSyncReload : I.NoSyncReloadSpec
  init : I.IfaceInitSpec

end specs

end bbolt
end EtcdGrove
end Perennial
