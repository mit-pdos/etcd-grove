/-
**`WatchCacheStorage`, as the specs see it** (KEP-6404, `notes/kep-6404-plan.md`; 2026-10-26).
Lean-first (no Rocq counterpart).

`WatchCacheStorage` (`watch_cache_storage.go`) keeps the watch cache's objects: under its lock
(`lock`, an `RWMutex`) the store (`store`, a `btreeStore`), the indexer and the snapshotter; and,
outside the lock, `latestSnapshot`, an atomic pointer to an immutable clone of the store, which
every write republishes and readers load without a lock.

Its abstract state is `st : SnapSt`, the entries and the resource version of the store as last
published (the state `latestSnapshot` points to; between two writes, the store's own). A ghost
variable `γ.st` holds it, split three ways:

* a quarter in the invariant around `latestSnapshot` (`isWCS`), with the published snapshot;
* half in the lock's resource (`wcsLockP`, at `q.half` for a fraction `q`: the guarded `RWMutex`
  splits it), with the store's fields, the indexer and the snapshotter, of that state;
* a quarter to the writer (`wcsOwn γ 1 st`): the watch cache, which calls the store's writes under
  its own lock. A reader that holds part of the writer's quarter (the watch cache's readers,
  under its read lock) knows the state, and the snapshot it loads (`LatestSnapshot`'s view shift
  at the load, against the invariant's quarter).

The indexer's index functions never fail (`isIndexFn`): a premise of the store's specs, the
store's update being half done when one does (`issues/k8s-watchcache-index-error-partial-update.md`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.store.Defs
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Std.Qextra

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher.store

/-- The store's abstract state: its entries and its resource version. -/
abbrev SnapSt := List (Loc × GoString) × w64

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

open Iris.ProofMode in
/-- The builtin `max` on `uint64` (a copy of raft's `wp_max2_uint64` and mvcc's
`sw_wp_max_int64`: a candidate for Perennial, `notes/perennial-changes.md`). -/
theorem wp_max_uint64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #x)) (Val #y))
    {{ RET #(if uint.Z y < uint.Z x then x else y); True }} := by
  wp_start
  wp_if_destruct
  all_goals
    first
    | rw [ite_cond_eq_true _ _ (eq_true (by omega))]
    | rw [ite_cond_eq_false _ _ (eq_false (by omega))]
    iapply HΦ; itrivial

/-! ## Elements and the indexer -/

/-- **An index function that never fails** on an element (`cache.IndexFunc`, here
`ElementIndexFunc` of the caller's): it returns some index values and no error. -/
def isIndexFn (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (e : Loc) (k : GoString),
    {{ isElem e k }}
      (App (Val #f) (Val #(interface.mkOk (go.GoType.PointerType Element.ty) #e)))
    {{ (sl : GoSlice) (vs : List GoString), RET (PairV #sl #GoInterface.nil); sl ↦* vs }})

instance isIndexFn_persistent (f : GoFunc) : Persistent (isIndexFn (GF := GF) f) := by
  unfold isIndexFn; infer_instance

/-- **The indices** (`indices`: index name, index value, key, element), owned at `dq`. -/
def ownIndices (m : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ m1 : GMap GoString Loc, ownMap m dq m1 ∗
    [∗map] _n ↦ l2 ∈ m1, ∃ m2 : GMap GoString Loc, ownMap l2 dq m2 ∗
      [∗map] _v ↦ l3 ∈ m2, ∃ m3 : GMap GoString Loc, ownMap l3 dq m3)

/-- **The indexer at `l`** (`indexer`), at `dq`: its indices, and its index functions (read-only,
each `isIndexFn`). -/
def ownIndexer (l : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ (ixs fns : Loc) (rv : w64) (fs : GMap GoString GoFunc),
    structFieldRef indexer go!"indices" l ↦{dq} ixs ∗ ownIndices ixs dq ∗
    structFieldRef indexer go!"indexers" l ↦{dq} fns ∗ ownMap fns DFrac.discard fs ∗
    □ ([∗map] _n ↦ f ∈ fs, isIndexFn f) ∗
    structFieldRef indexer go!"resourceVersion" l ↦{dq} rv)

/-! ## The snapshotter -/

/-- The snapshotter's order: snapshots by their resource versions (`newSnapshotter`'s `less`),
each snapshot related to its read-only `resourceVersion` field. -/
def snapOrder : btree.ItemOrder GF Loc w64 where
  lt a b := uint.Z a < uint.Z b
  order := ⟨fun _ => by omega, fun _ _ _ h1 h2 => by omega, fun a b => by
    rcases Int.lt_trichotomy (uint.Z a) (uint.Z b) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by word))
    · exact Or.inr (Or.inr h)⟩
  item p rv := iprop(structFieldRef k8s_io.apiserver.pkg.storage.cacher.store.btreeStore
    go!"resourceVersion" p ↦□ rv)
  item_persistent _ _ := by infer_instance

/-- **The snapshotter at `l`** (`snapshotter`), at `dq`, of a store at resource version `rv`: the
stored snapshots (published ones, each `isSnap`), and its resource version, at most the store's
(so that adding the next write's snapshot, at a later version, does not panic). -/
def ownSnapshotter (l : Loc) (dq : DFrac) (rv : w64) : IProp GF :=
  iprop(∃ (t : Loc) (srv : w64) (en : Bool) (ss : List (Loc × w64)),
    structFieldRef snapshotter go!"snapshots" l ↦{dq} t ∗ btree.ownBTree snapOrder t dq ss ∗
    □ (∀ x, ⌜x ∈ ss⌝ -∗ ∃ s, isSnap x.1 s x.2) ∗
    structFieldRef snapshotter go!"resourceVersion" l ↦{dq} srv ∗
    structFieldRef snapshotter go!"enabled" l ↦{dq} en ∗
    ⌜uint.Z srv ≤ uint.Z rv⌝)

/-! ## The storage -/

/-- The ghost names. -/
structure WCSNames where
  st : GName

/-- The namespace of the invariant around `latestSnapshot`. -/
def wcsN : Namespace := nroot .@ "watch_cache_storage"

/-- **The lock's resource** at fraction `q` (see the file header). -/
def wcsLockP (w : Loc) (γ : WCSNames) (q : Qp) : IProp GF :=
  iprop(∃ st : SnapSt, ghostVar γ.st q.half st ∗
    ownStore (structFieldRef WatchCacheStorage go!"store" w) (DFrac.own q) st.1 st.2 ∗
    ownIndexer (structFieldRef WatchCacheStorage go!"indexer" w) (DFrac.own q) ∗
    ownSnapshotter (structFieldRef WatchCacheStorage go!"snapshots" w) (DFrac.own q) st.2)

/-- **The published state** (the invariant's quarter): what a reader's view shift at
`LatestSnapshot`'s load sees. -/
def wcsPub (γ : WCSNames) (st : SnapSt) : IProp GF := ghostVar γ.st (1 : Qp).half.half st

instance wcsPub_timeless (γ : WCSNames) (st : SnapSt) : Timeless (wcsPub (GF := GF) γ st) := by
  unfold wcsPub; infer_instance

/-- **The writer's token**, at fraction `q` of its quarter (see the file header): whole (`q = 1`)
for the writes; a part for each of the watch cache's readers, under its read lock. -/
def wcsOwn (γ : WCSNames) (q : Qp) (st : SnapSt) : IProp GF := ghostVar γ.st q.half.half st

instance wcsOwn_timeless (γ : WCSNames) (q : Qp) (st : SnapSt) :
    Timeless (wcsOwn (GF := GF) γ q st) := by
  unfold wcsOwn; infer_instance

/-- **`w` is a `WatchCacheStorage`** (persistent): the invariant around `latestSnapshot` (the
published snapshot of the published state, and the caller's persistent fact `Ψ` of every state
it publishes: e.g. that it is the watched store's at its resource version) and the guarded lock. -/
def isWCS (w : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) : IProp GF :=
  iprop(inv wcsN iprop(∃ (p : Loc) (st : SnapSt),
      sync.atomic.ownPointer (T' := k8s_io.apiserver.pkg.storage.cacher.store.btreeStore)
        (structFieldRef WatchCacheStorage go!"latestSnapshot" w) (DFrac.own 1) p ∗
      isSnap p st.1 st.2 ∗ □ Ψ st ∗ wcsPub γ st) ∗
    sync.isRWMutexGuard (structFieldRef WatchCacheStorage go!"lock" w) (wcsLockP w γ))

instance isWCS_persistent (w : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) :
    Persistent (isWCS (GF := GF) w γ Ψ) := by
  unfold isWCS; infer_instance

/-! ## Lemmas -/

/-- A key's element in the entries is an entry. -/
theorem lookup_mem {s : List (Loc × GoString)} {k : GoString} {v : Loc}
    (h : btree.lookup s k = some v) : (v, k) ∈ s := by
  unfold btree.lookup at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hk := List.find?_some hx
  simp only [decide_eq_true_eq] at hk
  rw [← hk]
  exact List.mem_of_find?_eq_some hx

/-- **The element with key `k` in the entries `s`, if any, is a read-only element** (persistent). -/
def lookupFact (s : List (Loc × GoString)) (k : GoString) : IProp GF :=
  match btree.lookup s k with
  | some e' => isElem e' k
  | none => iprop(True)

instance lookupFact_persistent (s : List (Loc × GoString)) (k : GoString) :
    Persistent (lookupFact (GF := GF) s k) := by
  unfold lookupFact; split <;> infer_instance

open Iris.ProofMode in
/-- What the indexer takes of the element `getByKey` returns: `nil`, or a read-only element. -/
theorem lookupFact_prev (s : List (Loc × GoString)) (k : GoString) :
    lookupFact (GF := GF) s k ⊢ ⌜lookupElem s k = null⌝ ∨ isElem (lookupElem s k) k := by
  unfold lookupFact lookupElem
  cases h : btree.lookup s k with
  | none => iintro -; ileft; ipureintro; rfl
  | some e' => simp only [Option.getD_some]; iintro H; iright; iexact H

open Iris.ProofMode in
/-- **The store's element with a key** is a read-only element (the B-tree's item facts). -/
theorem ownStore_lookup (p : Loc) (dq : DFrac) (s : List (Loc × GoString)) (rv : w64)
    (k : GoString) :
    ownStore (GF := GF) p dq s rv ⊢ ownStore p dq s rv ∗ lookupFact s k := by
  unfold ownStore btree.ownBTree
  iintro ⟨%t, Htr, Hrv, ⟨%tv, %f, %less, %d, Hb⟩⟩
  iNamed Hb
  isplitl [Htr Hrv Ht Hroot]
  · iexists t; iframe Htr Hrv
    iexists tv, f, less, d
    simp only [named]
    iframe; iframe #
    ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩
  unfold lookupFact
  cases h : btree.lookup s k with
  | none => itrivial
  | some e' =>
    simp only
    iunfold btree.allItems at Hitems
    ihave Hx := Hitems $$ %(e', k) %(lookup_mem h)
    simp only [elemOrder]
    iexact Hx

open Iris.ProofMode in
/-- **A clone, made read-only for good, is a published snapshot.** -/
theorem isSnap_of_ownStore (p : Loc) (q : Qp) (s : List (Loc × GoString)) (rv : w64) :
    ownStore (GF := GF) p (DFrac.own q) s rv ⊢ |==> isSnap p s rv := by
  unfold isSnap ownStore
  iintro ⟨%t, Htr, Hrv, Ht⟩
  ipersist Htr
  ipersist Hrv
  imod btree.ownBTree_persist _ _ _ _ $$ Ht with Ht
  imodintro
  iexists t
  iframe
  iframe #

open Iris.ProofMode in
/-- Two pieces of a ghost variable agree, and stay. -/
theorem ghostVar_agree_keep {A : Type} [Pos.Countable A] (γ : GName) (a1 a2 : A) (q1 q2 : Qp) :
    ghostVar (GF := GF) γ q1 a1 ∗ ghostVar γ q2 a2 ⊢ ⌜a1 = a2⌝ ∗ ghostVar γ q1 a1 ∗ ghostVar γ q2 a2 := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 as H gives % ⟨_, h⟩
  subst h
  isplitr
  · ipureintro; rfl
  iapply ghostVar_split $$ H

open Iris.ProofMode in
/-- **A write's ghost update**: the lock's half, the writer's quarter and the invariant's quarter,
all of one state, move together to a new one. -/
theorem wcs_update (E : CoPset) (γ : WCSNames) (st st' : SnapSt) :
    ghostVar (GF := GF) γ.st (1 : Qp).half st ∗ wcsOwn γ 1 st ∗ wcsPub γ st ⊢ |={E}=>
      ghostVar γ.st (1 : Qp).half st' ∗ wcsOwn γ 1 st' ∗ wcsPub γ st' := by
  unfold wcsOwn wcsPub
  iintro ⟨Hg, Ho, Hp⟩
  ihave Hh := (ghostVar_split_half (GF := GF) γ.st (1 : Qp).half st).2 $$ [Ho Hp]
  · iframe
  imod ghostVar_update_halves (GF := GF) st' γ.st st st $$ Hg Hh with ⟨Hg, Hh⟩
  imodintro
  iframe Hg
  iapply (ghostVar_split_half (GF := GF) γ.st (1 : Qp).half st').1 $$ Hh

/-- The state after an update of the event type `et` with the element `e` of key `k`, at `rv`:
a delete removes the key's element, an add or a modification puts `e` in its place. -/
def updSt (et : GoString) (e : Loc) (k : GoString) (st : SnapSt) (rv : w64) : SnapSt :=
  (if et = go!"DELETED" then btree.delete st.1 k else btree.insert go.GoStringLt st.1 (e, k), rv)

end defs

end cacher
end EtcdGrove
end Perennial
