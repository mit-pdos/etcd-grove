/-
The state of a freelist (`internal/freelist`), the predicate of its `shared` part, and the
contract an implementation (`array`, `hashMap`) meets for `shared`'s methods.

A freelist's state (`FLState`) is what the specs speak of:
* `free`: the free page ids, strictly increasing (`array` keeps exactly this list; `hashMap`
  keeps spans, whose pages are this list);
* `pending`: for each transaction id, the pages it freed (not reusable until no reader can see
  them), each with the id of the transaction that allocated it (`alloctx`, `0` if unknown),
  and the start of the last `releaseRange` that looked at it;
* `allocs`: the transaction that allocated each page (as far as it is known);
* `readonly`: the ids of the open read-only transactions.

It is well-formed (`FLState.WF`) when all its free and pending ids are distinct and at least 2
(pages 0 and 1 are the metas), the free ids increase, there are fewer than `2^63` of them
(lengths of Go slices), and each pending entry has as many allocating transactions as ids.

The `cache` map of `shared` is a function of the state (every free or pending id):
`ownShared` says that it holds exactly those keys; `ownSharedC` leaves it unconstrained (it
is stale between an implementation's `Init` changing the free ids and `reindex`).

`shared` embeds the freelist interface (`shared.Interface`) and calls back through it
(`t.FreeCount()`, `t.Init(..)`, ...): its specs are stated for any implementation `I`
(`FLImpl`: the interface value's dynamic type and value, and the predicate `I.own s free` of
the implementation's own part, holding the free ids, whose `shared` is at `s`) meeting
`FLImpl.Contract` (the specs of the methods called back).
-/
module

public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.internal.common.Model
public import GeneratedProof.go_etcd_io.bbolt.internal.freelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- A transaction's pending pages (`txPending`). -/
structure Pending where
  ids : List w64
  alloctx : List w64
  lastReleaseBegin : w64

/-- The state of a freelist. -/
structure FLState where
  free : List w64
  pending : GMap w64 Pending
  allocs : GMap w64 w64
  readonly : List w64

/-- The pending ids, all transactions together (in the map's list order). -/
def FLState.pendingIds (σ : FLState) : List w64 := σ.pending.toList.flatMap (fun kv => kv.2.ids)

/-- The free and pending ids. -/
def FLState.allIds (σ : FLState) : List w64 := σ.free ++ σ.pendingIds

/-- `id` is free or pending (in the `cache`). -/
def FLState.cached (σ : FLState) (id : w64) : Prop := id ∈ σ.allIds

instance (σ : FLState) (id : w64) : Decidable (σ.cached id) := by
  unfold FLState.cached; infer_instance

/-- The number of pending pages (`PendingCount`). -/
def FLState.pendingCount (σ : FLState) : Nat := σ.pendingIds.length

/-- Strictly increasing page ids. -/
def PgidsIncr (l : List w64) : Prop := l.Pairwise (fun x y => uint.Z x < uint.Z y)

/-- A well-formed state. -/
def FLState.WF (σ : FLState) : Prop :=
  σ.allIds.Nodup ∧ (∀ id ∈ σ.allIds, 2 ≤ uint.Z id) ∧ PgidsIncr σ.free ∧
  σ.allIds.length < 2 ^ 63 ∧
  (∀ t p, σ.pending !! t = some p → p.ids.length = p.alloctx.length)

/-- `x` is one of the `n` ids from `r` on (`r`, `r+1`, ..., `r+n-1`). -/
def inRun (r : w64) (n : Nat) (x : w64) : Prop := uint.Z r ≤ uint.Z x ∧ uint.Z x < uint.Z r + n

instance (r : w64) (n : Nat) (x : w64) : Decidable (inRun r n x) := by
  unfold inRun; infer_instance

/-- The `n` ids from `r` on are free (and are ids: none is past the largest). -/
def FLState.canAllocate (σ : FLState) (r : w64) (n : Nat) : Prop :=
  uint.Z r + n ≤ 2 ^ 64 ∧ ∀ x, inRun r n x → x ∈ σ.free

/-- `σ` after transaction `txid` allocated the `n` ids from `r` on (`Allocate`). -/
def FLState.allocate (σ : FLState) (txid r : w64) (n : Nat) : FLState :=
  { σ with free := σ.free.filter (fun x => decide ¬ inRun r n x),
           allocs := <[r := txid]> σ.allocs }

/-- The `n` ids from `id` on. -/
def runIds (id : w64) (n : Nat) : List w64 := (List.range n).map (fun j : Nat => id + W64 (j : Int))

/-- `σ` after transaction `txid` freed the `n` pages from `id` on (`Free`): they are pending
for `txid`, with the transaction that allocated the first (`0` if unknown), which forgets
it. -/
def FLState.freePages (σ : FLState) (txid id : w64) (n : Nat) : FLState :=
  let pd := (σ.pending !! txid).getD ⟨[], [], 0⟩
  { σ with
    pending := <[txid := ⟨pd.ids ++ runIds id n,
      pd.alloctx ++ List.replicate n ((σ.allocs !! id).getD 0), pd.lastReleaseBegin⟩]> σ.pending,
    allocs := GMap.delete id σ.allocs }

/-- `Free` of the `n` pages from `id` on by `txid` does not panic: they are neither meta pages
nor free nor pending, `txid` did not allocate the first, and there are not too many. -/
def FLState.canFree (σ : FLState) (txid id : w64) (n : Nat) : Prop :=
  2 ≤ uint.Z id ∧ uint.Z id + n < 2 ^ 64 ∧ (∀ x ∈ runIds id n, ¬ σ.cached x) ∧
  (σ.allocs !! id).getD 0 ≠ txid ∧ σ.allIds.length + n < 2 ^ 63

/-- The empty state (`newShared`). -/
def FLState.empty : FLState := ⟨[], ∅, ∅, []⟩

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- A `*txPending` at `p` holding `pd`. -/
def ownPending (p : Loc) (pd : Pending) : IProp GF :=
  iprop(∃ (tv : txPending),
    "Hp" ∷ p ↦ tv ∗
    "Hids" ∷ tv.ids' ↦* pd.ids ∗ "Hids_cap" ∷ ownSliceCap w64 tv.ids' (DFrac.own 1) ∗
    "Hatx" ∷ tv.alloctx' ↦* pd.alloctx ∗
    "Hatx_cap" ∷ ownSliceCap w64 tv.alloctx' (DFrac.own 1) ∗
    "%Hlrb" ∷ ⌜tv.lastReleaseBegin' = pd.lastReleaseBegin⌝)

/-- The `shared` at `s` (its value `sv`, with interface field `iface`), holding `σ`'s
read-only transactions, allocations and pending pages, and the cache `c`. -/
def ownSharedC (s : Loc) (sv : shared) (iface : GoInterface) (σ : FLState)
    (c : GMap w64 Unit) : IProp GF :=
  iprop(∃ (pp : GMap w64 Loc),
    "Hs" ∷ s ↦ sv ∗ "%Hiface" ∷ ⌜sv.Interface' = iface⌝ ∗
    "Hro" ∷ sv.readonlyTXIDs' ↦* σ.readonly ∗
    "Hro_cap" ∷ ownSliceCap w64 sv.readonlyTXIDs' (DFrac.own 1) ∗
    "Hallocs" ∷ sv.allocs' ↦$ σ.allocs ∗
    "Hcache" ∷ sv.cache' ↦$ c ∗
    "Hpending" ∷ sv.pending' ↦$ pp ∗
    "Hpds" ∷ [∗map] _t ↦ p;pd ∈ pp;σ.pending, ownPending p pd)

/-- The cache holds exactly the free and pending ids. -/
def cacheOK (c : GMap w64 Unit) (σ : FLState) : Prop := ∀ id, (c !! id).isSome ↔ σ.cached id

/-- The `shared` at `s` in the well-formed state `σ`, its cache up to date. -/
def ownShared (s : Loc) (iface : GoInterface) (σ : FLState) : IProp GF :=
  iprop(∃ (sv : shared) (c : GMap w64 Unit),
    ownSharedC s sv iface σ c ∗ ⌜cacheOK c σ ∧ σ.WF⌝)

/-- The state of a `shared` is well-formed. -/
theorem ownShared_wf (s : Loc) (iface : GoInterface) (σ : FLState) :
    ownShared (GF := GF) s iface σ ⊢ ownShared s iface σ ∗ ⌜σ.WF⌝ := by
  unfold ownShared
  iintro ⟨%sv, %c, H, %Hok⟩
  isplitl
  · iexists sv, c; iframe; ipureintro; exact Hok
  · ipureintro; exact Hok.2

/-- An implementation of the freelist interface: the interface value's dynamic type `ity` and
value `iv`, and `own s free`, its own part (holding the free ids `free`; its `shared` at
`s`). -/
structure FLImpl where
  ity : go.GoType
  iv : val
  /-- The implementation's own part, holding the free ids. -/
  own : Loc → List w64 → IProp GF
  /-- What does not change: the implementation's pointer to its `shared` (persistent). -/
  hdl : Loc → IProp GF
  hdl_persistent : ∀ s, Persistent (hdl s)

/-- The interface value of `I`. -/
def FLImpl.iface (I : FLImpl (GF := GF)) : GoInterface := interface.mkOk I.ity I.iv

instance FLImpl.hdl_persistent' (I : FLImpl (GF := GF)) (s : Loc) : Persistent (I.hdl s) :=
  I.hdl_persistent s

/-- `FreeCount()`: the number of free ids. -/
def FLImpl.FreeCountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (free : List w64),
    {{ I.own s free }}
      (App (Val #(methods I.ity go!"FreeCount" I.iv)) (Val #()))
    {{ RET #(W64 (free.length : Int)); I.own s free }}

/-- `freePageIds()`: a slice of the free ids, to be given back. -/
def FLImpl.FreePageIdsSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (free : List w64),
    {{ I.own s free }}
      (App (Val #(methods I.ity go!"freePageIds" I.iv)) (Val #()))
    {{ (r : GoSlice), RET #r; r ↦* free ∗ (r ↦* free -∗ I.own s free) }}

/-- `pendingPageIds()`: the `shared`'s pending map. -/
def FLImpl.PendingPageIdsSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (sv : shared) (dq : DFrac),
    {{ I.hdl s ∗ s ↦{dq} sv }}
      (App (Val #(methods I.ity go!"pendingPageIds" I.iv)) (Val #()))
    {{ RET #sv.pending'; s ↦{dq} sv }}

/-- `Init(ids)`: the free ids become `ids` (the new state well-formed), the cache rebuilt. -/
def FLImpl.InitSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (ids : GoSlice) (xs : List w64),
    ({ σ with free := xs } : FLState).WF →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
        I.hdl s ∗ ownShared s I.iface σ ∗ I.own s σ.free ∗ ids ↦* xs ∗
        ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"Init" I.iv)) (Val #ids))
    {{ RET #(); ownShared s I.iface { σ with free := xs } ∗ I.own s xs }}

/-- `mergeSpans(ids)`: the ids (distinct, at least 2, not free) become free (the slice is
consumed: an implementation may keep it). -/
def FLImpl.MergeSpansSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (free : List w64) (ids : GoSlice) (ys : List w64),
    (free ++ ys).Nodup → (∀ y ∈ ys, 2 ≤ uint.Z y) → free.length + ys.length < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
        I.own s free ∗ ids ↦* ys ∗ ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"mergeSpans" I.iv)) (Val #ids))
    {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm (free ++ ys)⌝ ∗
        I.own s free' }}

/-- A whole freelist: an implementation meeting the contract, its `shared` at `s`. -/
def ownFL (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) : IProp GF :=
  iprop(I.hdl s ∗ ownShared s I.iface σ ∗ I.own s σ.free)

/-- `Allocate(txid, n)`, as the freelist's users see it: either nothing (`0`) or `n` free ids from
some `r` on, now allocated by `txid` (which run, and whether one is found when one exists, is
the implementation's: `array` takes the first, `hashMap` any). -/
def FLImpl.AllocateSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (txid n : w64), 0 < sint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
        ownFL I s σ }}
      (App (App (Val #(methods I.ity go!"Allocate" I.iv)) (Val #txid)) (Val #n))
    {{ (r : w64), RET #r; ⌜r = W64 0⌝ ∗ ownFL I s σ ∨
        ⌜σ.canAllocate r (sint.nat n)⌝ ∗ ownFL I s (σ.allocate txid r (sint.nat n)) }}

/-- The specs of the methods `shared`'s methods call back through the interface. -/
def FLImpl.Contract (I : FLImpl (GF := GF)) : Prop :=
  I.FreeCountSpec ∧ I.FreePageIdsSpec ∧ I.PendingPageIdsSpec ∧ I.InitSpec ∧ I.MergeSpansSpec

end preds

end bbolt
end EtcdGrove
end Perennial
