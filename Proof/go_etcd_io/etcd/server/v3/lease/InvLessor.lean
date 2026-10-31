/-
The lessor's lock and what it holds (`server/lease/lessor.go`, 2026-10-13, unit 8 of the
backend). Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The lessor's KV-facing
methods and the live leases (unit 8)".

**The lock** `le.mu` (an `RWMutex`, `lessorMu lp γl`): the fields `leaseMap` (the granted leases,
id to `*Lease`), `itemMap` (item to lease id) and `rd` (the range deleter), and the lessor's half
of the **live-lease set**: a ghost variable `γl` (the store's `γ.leases`) at `(lp, L)`, `L` the
domain of `leaseMap`. Every `*Lease` of the map is `isLeaseObj`: not nil, its own lock `l.mu`
guarding its `itemSet`.

**The lease owner's half** (`leaseOwn γl L`): the other half of `γl`, held by the apply thread
(the one goroutine that grants and revokes leases: `lessor.Grant`/`Revoke` run only in the
applier). Holding it, `L` is the live set: `Attach(id, …)` of an `id ∈ L` succeeds, `Lookup(id)`
returns non-nil exactly for `id ∈ L`. A lease known live is a pure fact `id ∈ L` relative to the
half the caller holds, not a persistent fact: `Revoke` takes the half and shrinks `L`.

**The readers** (`lessorRd lp γl`): `GetLease` and `Lookup` take `le.mu`'s read lock, which needs a
reader slot (`sync.ownRWMutex`); the writers (`Attach`, `Detach`, `SetRangeDeleter`) only the
guard.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace go_etcd_io.etcd.server.v3.lease

deriving instance DecidableEq for LeaseItem

/-- A `LeaseItem` is countable through its key (ghost state stores item sets: Part B). -/
instance LeaseItem.countable [GooseExts] : Pos.Countable LeaseItem :=
  .ofInjective (fun it => Pos.Countable.encode it.Key')
    (fun a b h => by cases a; cases b; simp only at h; rw [Pos.encode_inj h])

end go_etcd_io.etcd.server.v3.lease

namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&le.<f>` -/
abbrev lF (f : GoString) (lp : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.lessor f lp

/-- `&l.<f>` (a `*Lease`) -/
abbrev lsF (f : GoString) (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.Lease f l

/-- `&it.<f>` (a `*LeaseWithTime`) -/
abbrev lwF (f : GoString) (p : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.LeaseWithTime f p

/-- `&n.<f>` (a `*LeaseExpiredNotifier`) -/
abbrev nF (f : GoString) (p : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier f p

/-- The lessor `lp` as a `Lessor` interface value. -/
abbrev lessorIface (lp : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty) #lp

end fields

section keys
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [LeaseItem.TypeAssumptions]

/-- A `LeaseItem` is its key: its Go value determines it (the field read is deterministic). -/
instance leaseItem_intoValInj [go.BasicIntoValInj] : go.IntoValInj LeaseItem where
  intoVal_inj x y h := by
    have hx := (LeaseItem.TypeAssumptions.get_Key x).isGoStep_det_internal.isGoStep_pure_det
    have hy := (LeaseItem.TypeAssumptions.get_Key y).isGoStep_det_internal.isGoStep_pure_det
    rw [h] at hx
    have h2 := congrFun (hx.symm.trans hy) (Val #(x.Key'))
    simp only [eq_iff_iff, true_iff] at h2
    have h3 : (#(x.Key') : val) = #(y.Key') := by
      have := h2.symm
      injection this
    have h4 : x.Key' = y.Key' := go.intoVal_inj h3
    cases x; cases y
    simp only at h4
    subst h4; rfl

end keys

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The right to close a lease's `revokec`** (unit T3, 2026-10-24): `NewLease` makes it,
`Revoke` closes the channel with it. -/
def revokeCloser (c : GoChan) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan c γc Unit ∗ ownChan γc Unit .Idle)

/-- **The lessor's reader-side ghost names** (the lease-keys plan, Part B, 2026-10-31): the
history of its snapshots (`γr.1`, a monotone list), the item sets' map (`γr.2.1`, each `*Lease` to
its item set) and the slot pool (`γr.2.2`, each borrowing token to the lease it lent a reader slot
of). -/
abbrev LessorRdNames := GName × GName × GName

/-- **A snapshot of the lessor**: its lease map (id to `*Lease`) and its item map (item to id). -/
abbrev LSnap := GMap w64 Loc × GMap LeaseItem w64

/-- The values of the lessor's ghost map `γl`: at `false` its location, the name of its grant
guard (D19n), (unit T3) of its closers' map `γcl` (lease id to `*Lease`) and (Part B) its
reader-side names, at `true` its live set. -/
abbrev LessorGV := (Loc × GName × GName × LessorRdNames) ⊕ List w64

/-- The lessor's ghost map `γl`'s contents: its location and its names at `false` (pinned for
good), its live set at `true`. -/
def lessorGhost (lp : Loc) (γga γcl : GName) (γr : LessorRdNames) (L : List w64) :
    GMap Bool LessorGV :=
  (((∅ : GMap Bool LessorGV).insert false (Sum.inl (lp, γga, γcl, γr))).insert true (Sum.inr L))

/-- A share `q` of the live set `L` (the ghost map `γl`'s element `true`). -/
def leaseFrag (γl : GName) (q : Qp) (L : List w64) : IProp GF :=
  ghostMapElem γl true (DFrac.own q) (Sum.inr L : LessorGV)

/-- The lessor of `γl` is at `lp`, its grant guard named `γga`, its closers' map `γcl` and its
reader-side names `γr` (persistent: the ghost map's element `false`, discarded). -/
def lessorPinAll (γl : GName) (lp : Loc) (γga γcl : GName) (γr : LessorRdNames) : IProp GF :=
  ghostMapElem γl false DFrac.discard (Sum.inl (lp, γga, γcl, γr) : LessorGV)

instance lessorPinAll_persistent (γl : GName) (lp : Loc) (γga γcl : GName) (γr : LessorRdNames) :
    Persistent (lessorPinAll (GF := GF) γl lp γga γcl γr) := by
  unfold lessorPinAll; infer_instance

/-- The lessor of `γl` is at `lp`, its grant guard named `γga`, its closers' map `γcl`
(persistent). -/
def lessorPinG (γl : GName) (lp : Loc) (γga γcl : GName) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinAll γl lp γga γcl γr)

instance lessorPinG_persistent (γl : GName) (lp : Loc) (γga γcl : GName) :
    Persistent (lessorPinG (GF := GF) γl lp γga γcl) := by
  unfold lessorPinG; infer_instance

/-- The lessor of `γl` has the reader-side names `γr` (persistent). -/
def lessorPinR (γl : GName) (γr : LessorRdNames) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName), lessorPinAll γl lp γga γcl γr)

instance lessorPinR_persistent (γl : GName) (γr : LessorRdNames) :
    Persistent (lessorPinR (GF := GF) γl γr) := by
  unfold lessorPinR; infer_instance

/-- The lessor of `γl` is at `lp` (persistent). -/
def lessorPin (γl : GName) (lp : Loc) : IProp GF :=
  iprop(∃ γga γcl : GName, lessorPinG γl lp γga γcl)

instance lessorPin_persistent (γl : GName) (lp : Loc) : Persistent (lessorPin (GF := GF) γl lp) := by
  unfold lessorPin; infer_instance

/-- What a lease's lock `l.mu` guards: half of its item set (unit T3, L2b, 2026-10-25: the other
half is the lease owner's, `leaseItemsOwn`, so that `Keys()` under the read lock returns the set
the owner knows) and (Part B, 2026-10-31) the lease's element of the lessor `γl`'s item sets' map
at the same set, so that `Keys()` under a reader's read lock returns the set the lessor's history
records (`lessorRdInv`). -/
def leaseItems (γl : GName) (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit) (γr : LessorRdNames), lessorPinR γl γr ∗
    lsF go!"itemSet" l ↦{DFrac.own q.half} sm ∗ sm ↦${DFrac.own q.half} S ∗
    ghostMapElem γr.2.1 l (DFrac.own q) S)

/-- **The item set `S` of the lease `id` is what the item map `I` attaches to it** (unit T3,
L2b). -/
def itemsFor (I : GMap LeaseItem w64) (id : w64) (S : GMap LeaseItem Unit) : Prop :=
  ∀ it : LeaseItem, S.lookup it = some () ↔ I.lookup it = some id

/-- `m` with every key of `xs` set to `v` (the item map and set after `Attach`'s loop). -/
def insertAll {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (v : V) : GMap K V :=
  xs.foldl (fun m k => m.insert k v) m

/-- `m` without the keys of `xs` (the item map and set after `Detach`'s loop). -/
def deleteAll {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) : GMap K V :=
  xs.foldl (fun m k => m.delete k) m

theorem insertAll_lookup {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (v : V)
    (k : K) : (insertAll m xs v).lookup k = if k ∈ xs then some v else m.lookup k := by
  induction xs generalizing m with
  | nil => simp [insertAll]
  | cons x xs ih =>
    have h : insertAll m (x :: xs) v = insertAll (m.insert x v) xs v := rfl
    rw [h, ih]
    rw [GMap.lookup_insert_eq_iff]
    by_cases hk : k ∈ xs
    · simp [hk]
    · by_cases hx : x = k
      · subst hx; simp [hk]
      · simp [hk, hx, Ne.symm hx]

theorem deleteAll_lookup {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (k : K) :
    (deleteAll m xs).lookup k = if k ∈ xs then none else m.lookup k := by
  induction xs generalizing m with
  | nil => simp [deleteAll]
  | cons x xs ih =>
    have h : deleteAll m (x :: xs) = deleteAll (m.delete x) xs := rfl
    rw [h, ih]
    rw [GMap.lookup_delete_iff]
    by_cases hk : k ∈ xs
    · simp [hk]
    · by_cases hx : x = k
      · subst hx; simp [hk]
      · simp [hk, hx, Ne.symm hx]

/-- **Every key of the item map `I` is shorter than `2 ^ 63 - 1` bytes** (the lease-keys plan, Q4
(b), 2026-10-31): what the auth store's checks take of each key `Keys()` returns
(`IsPutPermitted`); a key gets it from the request that put it (`Attach`'s premise). -/
def itemKeysShort (I : GMap LeaseItem w64) : Prop :=
  ∀ (it : LeaseItem) (id : w64), I.lookup it = some id → (it.Key'.length : Int) < 2 ^ 63 - 1

/-- A map whose keys are keys of `I` keeps `I`'s short keys. -/
theorem itemKeysShort_of_sub {I J : GMap LeaseItem w64}
    (h : ∀ (it : LeaseItem) (id : w64), J.lookup it = some id → ∃ id', I.lookup it = some id')
    (hI : itemKeysShort I) : itemKeysShort J := by
  intro it id hj
  obtain ⟨id', h'⟩ := h it id hj
  exact hI it id' h'

/-- `Detach`'s item map keeps the short keys. -/
theorem itemKeysShort_deleteAll (I : GMap LeaseItem w64) (xs : List LeaseItem)
    (hI : itemKeysShort I) : itemKeysShort (deleteAll I xs) := by
  apply itemKeysShort_of_sub _ hI
  intro it id h
  rw [deleteAll_lookup] at h
  by_cases hi : it ∈ xs
  · simp [hi] at h
  · simp only [hi, ↓reduceIte] at h; exact ⟨id, h⟩

/-- `Attach`'s item map of short keys, from short items. -/
theorem itemKeysShort_insertAll (I : GMap LeaseItem w64) (xs : List LeaseItem) (v : w64)
    (hI : itemKeysShort I) (hxs : ∀ it ∈ xs, (it.Key'.length : Int) < 2 ^ 63 - 1) :
    itemKeysShort (insertAll I xs v) := by
  intro it id h
  rw [insertAll_lookup] at h
  by_cases hi : it ∈ xs
  · exact hxs it hi
  · simp only [hi, ↓reduceIte] at h; exact hI it id h

/-! ### The lessor from a reader (the lease-keys plan, Part B, 2026-10-31)

A goroutine other than the lease owner (the server's API layer: `checkLeaseRenew`, ...) looks a
lease up and reads its keys. What it learns is stated over the **history** of the lessor's
snapshots (lease map, item map), which the owner appends to at each change, under `le.mu`'s write
lock: a reader with a lower bound `m` of the history (`lessorLb`) finds the lease map of an index
`≥ m` (`leaseLiveFrom`, `leaseAbsentFrom`), and the keys of a lease `l` of `id` at an index `≥ m`
where the lease map has `l` (`leaseKeysFrom`): each `*Lease`'s item set is its id's items at the
last index the lease map has it (`setsOk`; frozen at its revocation: Go's `Revoke` does not clear
`l.itemSet`, and the id can be granted again). -/

/-- **`l` is the lease of `id` at the index `i` of `hs`, and at no later index.** -/
def lastLiveAt (hs : List LSnap) (id : w64) (l : Loc) (i : Nat) : Prop :=
  (∃ σ, hs[i]? = some σ ∧ σ.1.lookup id = some l) ∧
    ∀ (j : Nat) (σ : LSnap), i < j → hs[j]? = some σ → σ.1.lookup id ≠ some l

/-- **Every `*Lease` of the history is the lease of one id.** -/
def oneIdPerLease (hs : List LSnap) : Prop :=
  ∀ (i j : Nat) (σ τ : LSnap) (id id' : w64) (l : Loc), hs[i]? = some σ → hs[j]? = some τ →
    σ.1.lookup id = some l → τ.1.lookup id' = some l → id = id'

/-- **The item sets agree with the history**: each `*Lease`'s set is empty if no lease map of the
history has it, and otherwise its id's items at the last index the lease map has it. -/
def setsOk (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)) : Prop :=
  ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S →
    ((∀ (i : Nat) (σ : LSnap) (id : w64), hs[i]? = some σ → σ.1.lookup id ≠ some l) ∧ S = ∅) ∨
    ∃ (id : w64) (i : Nat) (σ : LSnap), lastLiveAt hs id l i ∧ hs[i]? = some σ ∧ itemsFor σ.2 id S

/-- **The history's facts**: not empty, each lease under one id, every snapshot's keys short. -/
def histOk (hs : List LSnap) : Prop :=
  hs ≠ [] ∧ oneIdPerLease hs ∧ ∀ σ ∈ hs, itemKeysShort σ.2

/-- **The number of borrowing tokens** of the slot pool: a lease's lock has
`actualMaxReaders` reader slots, one of them the owner's (`closerAt`). -/
def rdPoolSize : Nat := Int.toNat sync.rwmutex.actualMaxReaders - 1

def lessorRdN : Namespace := nroot .@ "lessor_rd"

/-- **The lessor's reader-side invariant** at the names `γr`: a quarter of the history's
authority (`hs`; the owner holds half, `leaseClosers`, and `le.mu`'s invariant a quarter, so that
the owner appends holding the write lock), half of the item sets' map's authority (`Sm`; the owner
the other half), `setsOk` and `histOk`; and the slot pool: each borrowing token `j <
rdPoolSize`'s state `B j` (half here, half with the token's holder, `lessorReader`), the lease it
has lent a slot of, and for every `*Lease` of the item sets' map, its slot for `j` unless lent. -/
def lessorRdBody (γl : GName) (γr : LessorRdNames) : IProp GF :=
  iprop(∃ (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)) (B : GMap Nat (Option Loc)),
    monoListAuthOwn γr.1 Qp.quarter hs ∗ ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗
    ⌜setsOk hs Sm ∧ histOk hs⌝ ∗
    ghostMapAuth γr.2.2 1 B ∗ ⌜∀ j, (B.lookup j).isSome ↔ j < rdPoolSize⌝ ∗
    [∗map] j ↦ b ∈ B, ghostMapElem γr.2.2 j (DFrac.own (1 : Qp).half) b ∗
      [∗map] l ↦ _S ∈ Sm, (⌜b = some l⌝ ∨ sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l)))

/-- **The lessor `γl`'s reader-side invariant** (persistent). -/
def lessorRdInv (γl : GName) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ inv lessorRdN (lessorRdBody γl γr))

instance lessorRdInv_persistent (γl : GName) : Persistent (lessorRdInv (GF := GF) γl) := by
  unfold lessorRdInv; infer_instance

/-- **The index `i` of the lessor `γl`'s history is the snapshot `σ`** (persistent). -/
def lessorAt (γl : GName) (i : Nat) (σ : LSnap) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ monoListIdxOwn γr.1 i σ)

instance lessorAt_persistent (γl : GName) (i : Nat) (σ : LSnap) :
    Persistent (lessorAt (GF := GF) γl i σ) := by
  unfold lessorAt; infer_instance

/-- **A lower bound `m` of the lessor's history** (persistent): its index `m` is recorded. What a
reader holds of the history it has observed. -/
def lessorLb (γl : GName) (m : Nat) : IProp GF :=
  iprop(∃ σ : LSnap, lessorAt γl m σ)

instance lessorLb_persistent (γl : GName) (m : Nat) : Persistent (lessorLb (GF := GF) γl m) := by
  unfold lessorLb; infer_instance

/-- **`l` is the lease of `id` at an index no earlier than `m`** (persistent). -/
def leaseLiveFrom (γl : GName) (m : Nat) (id : w64) (l : Loc) : IProp GF :=
  iprop(∃ (i : Nat) (σ : LSnap), ⌜m ≤ i ∧ σ.1.lookup id = some l⌝ ∗ lessorAt γl i σ)

instance leaseLiveFrom_persistent (γl : GName) (m : Nat) (id : w64) (l : Loc) :
    Persistent (leaseLiveFrom (GF := GF) γl m id l) := by
  unfold leaseLiveFrom; infer_instance

/-- **No lease of `id` at an index no earlier than `m`** (persistent). -/
def leaseAbsentFrom (γl : GName) (m : Nat) (id : w64) : IProp GF :=
  iprop(∃ (i : Nat) (σ : LSnap), ⌜m ≤ i ∧ σ.1.lookup id = none⌝ ∗ lessorAt γl i σ)

instance leaseAbsentFrom_persistent (γl : GName) (m : Nat) (id : w64) :
    Persistent (leaseAbsentFrom (GF := GF) γl m id) := by
  unfold leaseAbsentFrom; infer_instance

/-- **`ks` are the keys of the lease `l` of `id` at an index no earlier than `m`** (persistent):
the keys the item map attaches to `id` there, where the lease map has `l`; every key of that item
map short. -/
def leaseKeysFrom (γl : GName) (m : Nat) (id : w64) (l : Loc) (ks : List GoString) : IProp GF :=
  iprop(∃ (i : Nat) (σ : LSnap),
    ⌜m ≤ i ∧ σ.1.lookup id = some l ∧ (∀ k : GoString, k ∈ ks ↔ σ.2.lookup ⟨k⟩ = some id) ∧
      itemKeysShort σ.2⌝ ∗ lessorAt γl i σ)

instance leaseKeysFrom_persistent (γl : GName) (m : Nat) (id : w64) (l : Loc) (ks : List GoString) :
    Persistent (leaseKeysFrom (GF := GF) γl m id l ks) := by
  unfold leaseKeysFrom; infer_instance

/-- **The lease owner's half of the item set of the lease `l`** (of id `id`), which is what the
item map `I` attaches to `id` (unit T3, L2b). -/
def leaseItemsOwn (l : Loc) (I : GMap LeaseItem w64) (id : w64) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own (1 : Qp).half} sm ∗
    sm ↦${DFrac.own (1 : Qp).half} S ∗ ⌜itemsFor I id S⌝)

/-- A lease of the map: not nil, its lock guarding its item set, the lessor's reader-side
invariant (persistent). -/
def isLeaseObj (γl : GName) (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ sync.isRWMutexGuard (lsF go!"mu" l) (leaseItems γl l) ∗ lessorRdInv γl)

instance isLeaseObj_persistent (γl : GName) (l : Loc) : Persistent (isLeaseObj (GF := GF) γl l) := by
  unfold isLeaseObj; infer_instance

/-- **The lessor's grant guard** (D19n, 2026-10-18; persistent): the predicate `GA` its caller
chose at `NewLessor`, a saved predicate pinned in the lessor's ghost map. A lease is granted only
with `GA` of its id (`Grant`'s `leaseGranted`); so every lease of the lessor's map, and every
lease its expiry loop sends on `expiredC`, has it. A server whose policy admits no `LeaseGrant`
picks `GA := False`. -/
def lessorGuard (γl : GName) (GA : w64 → IProp GF) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName), lessorPinG γl lp γga γcl ∗
    savedPredOwn γga DFrac.discard GA)

instance lessorGuard_persistent (γl : GName) (GA : w64 → IProp GF) :
    Persistent (lessorGuard (GF := GF) γl GA) := by
  unfold lessorGuard; infer_instance

/-- **The lease `id` may be granted** (D19n; persistent): it meets the lessor's grant guard. -/
def leaseGranted (γl : GName) (id : w64) : IProp GF :=
  iprop(∃ GA : w64 → IProp GF, lessorGuard γl GA ∗ □ GA id)

instance leaseGranted_persistent (γl : GName) (id : w64) :
    Persistent (leaseGranted (GF := GF) γl id) := by
  unfold leaseGranted; infer_instance

/-- **The lessor's share `q` of its ghost map's authority**, at the live set `L`, every lease of
which may be granted (D19n); (unit T3) and of its closers' map, at the lease map `M`. -/
def lessorAuth (γl : GName) (q : Qp) (lp : Loc) (L : List w64) (M : GMap w64 Loc) : IProp GF :=
  iprop(∃ (γga γcl : GName) (γr : LessorRdNames), ghostMapAuth γl q (lessorGhost lp γga γcl γr L) ∗
    ghostMapAuth γcl q M ∗
    □ ([∗list] id ∈ L, leaseGranted γl id))

/-! ### The lessor's apply-side state (2026-10-13, unit 9)

`Grant`, `Checkpoint` (and `Promote`, `Demote`, the expiry loop) touch more of the lessor
under `le.mu`: the primary's channel `demotec`, the expiry notifier (a map from lease id to the
queue's item, and a heap of the items by expiry time), the checkpoint heap, the checkpointer, and
of each lease its `remainingTTL` and the lessor's half of its `expiry` (the other half is
`l.expiryMu`'s: `refresh`/`forever` write it holding both locks, `Grant` and the expiry loop read
it under `le.mu` alone, `Remaining` under `l.expiryMu` alone). -/

/-- Swap the elements at `i` and `j` (`h.Swap(i, j)`; unchanged out of range). -/
def listSwap {α : Type} (xs : List α) (i j : Nat) : List α :=
  match xs[i]?, xs[j]? with
  | some a, some b => (xs.set i b).set j a
  | _, _ => xs

/-- A queue item `&LeaseWithTime` at `p`, at share `q`: its `id` (read-only), its `time`, and
its `index` `k` (its position in its queue). -/
def lwtAt (p : Loc) (id : w64) (k : w64) (q : Qp) : IProp GF :=
  iprop(lwF go!"id" p ↦□ id ∗ (∃ t : _root_.Perennial.time.Time, lwF go!"time" p ↦{DFrac.own q} t) ∗
    lwF go!"index" p ↦{DFrac.own q} k)

/-- A `LeaseQueue` value `s` holding the items `xs` (pointer, lease id), at share `q`, each
item's `index` its position (what `heap.Fix(&q, old.index)` needs), with the slice's capacity
(`append`). -/
def queueAt (s : GoSlice) (xs : List (Loc × w64)) (q : Qp) : IProp GF :=
  iprop(s ↦*{DFrac.own q} (xs.map Prod.fst) ∗ ownSliceCap Loc s (DFrac.own q) ∗
    [∗list] k ↦ x ∈ xs, lwtAt x.1 x.2 (W64 k) q)

/-- **The expiry notifier** at `np` (`LeaseExpiredNotifier`), at share `q`: its map `m` (lease id
to item) holds exactly the items of its queue, each under its own id, no item twice. -/
def notifierAt (np : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (mp : Loc) (s : GoSlice) (M : GMap w64 Loc) (xs : List (Loc × w64)),
    nF go!"m" np ↦{DFrac.own q} mp ∗ mp ↦${DFrac.own q} M ∗ nF go!"queue" np ↦{DFrac.own q} s ∗
    queueAt s xs q ∗
    ⌜(xs.map Prod.fst).Nodup ∧ ∀ (id : w64) (p : Loc), M.lookup id = some p ↔ (p, id) ∈ xs⌝)

/-- What `l.expiryMu` guards at `q`: half of `l.expiry` at `q` (the other half is the lessor's,
in `leaseMeta`). -/
def leaseExpiry (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ e : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own q.half} e)

/-- **A granted lease's state** (`l`, of id `id`) under `le.mu`, at `q`: its `ID` and `ttl`
(read-only once granted), its `revokec` (read-only), its `remainingTTL` and the lessor's half
of `expiry`; its `expiryMu` guards the other half. -/
def leaseMeta (id : w64) (l : Loc) (q : Qp) : IProp GF :=
  iprop(lsF go!"ID" l ↦□ id ∗ (∃ t : w64, lsF go!"ttl" l ↦□ t) ∗
    (∃ c : GoChan, lsF go!"revokec" l ↦□ c) ∗
    (∃ r : w64, lsF go!"remainingTTL" l ↦{DFrac.own q} r) ∗
    (∃ e : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own q.half} e) ∗
    sync.isRWMutexGuard (lsF go!"expiryMu" l) (leaseExpiry l))

/-- **The lessor's apply-side fields** under `le.mu` at `q`, for its lease map `M`: `demotec`,
the expiry notifier, the checkpoint heap (a queue of fresh items, any ids), the checkpointer
`cp`, and every granted lease's `leaseMeta`; (D22 receiver epochs, S7c, 2026-10-23) half the
fraction of the backend `b` (the other half its user's, `lessorBeOn`: `Recover` replaces it). -/
def lessorExtra (lp : Loc) (M : GMap w64 Loc) (q : Qp) : IProp GF :=
  iprop(∃ (dc : GoChan) (np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (cp : GoFunc)
      (b : GoInterface),
    lF go!"demotec" lp ↦{DFrac.own q} dc ∗
    lF go!"leaseExpiredNotifier" lp ↦{DFrac.own q} np ∗ notifierAt np q ∗
    lF go!"leaseCheckpointHeap" lp ↦{DFrac.own q} h ∗ queueAt h hx q ∗
    lF go!"cp" lp ↦{DFrac.own q} cp ∗
    ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗
    lF go!"b" lp ↦{DFrac.own q.half} b)

/-- **What `le.mu` guards** at fraction `q`: the lease map `M` (whose domain is the live set
`L`; the lessor's share of it, `q/2`, and of the ghost map's authority), half of the item map
(`q/2`: unit T3, L2b, the other half is the lease owner's, `leaseClosers`), half of
the range deleter (`q/2`: unit T3, the other half is `rdOwn`'s, since `Revoke` reads `le.rd`
after releasing the lock); every lease of the map `isLeaseObj`; and (2026-10-13, unit 9) the apply-side fields
(`lessorExtra`). -/
def lessorMu (lp : Loc) (γl : GName) (q : Qp) : IProp GF :=
  iprop(∃ (lm im : Loc) (M : GMap w64 Loc) (I : GMap LeaseItem w64) (rd : GoFunc)
      (L : List w64),
    lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗ lm ↦${DFrac.own q} M ∗
    lF go!"itemMap" lp ↦{DFrac.own q.half} im ∗ im ↦${DFrac.own q.half} I ∗
    lF go!"rd" lp ↦{DFrac.own q.half} rd ∗
    lessorAuth γl q lp L M ∗ leaseFrag γl q.half L ∗
    ⌜∀ id : w64, id ∈ L ↔ (M.lookup id).isSome⌝ ∗
    ([∗map] _id ↦ l ∈ M, isLeaseObj γl l) ∗ lessorExtra lp M q ∗
    (∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗
      monoListAuthOwn γr.1 q.half.half hs ∗ ⌜hs.getLast? = some (M, I)⌝))

/-- **The lessor** at `lp` with ghost map `γl` (persistent): pinned, its lock's guard. -/
def lessorInv (lp : Loc) (γl : GName) : IProp GF :=
  iprop(⌜lp ≠ null⌝ ∗ lessorPin γl lp ∗ sync.isRWMutexGuard (lF go!"mu" lp) (lessorMu lp γl) ∗
    lessorRdInv γl)

instance lessorInv_persistent (lp : Loc) (γl : GName) :
    Persistent (lessorInv (GF := GF) lp γl) := by
  unfold lessorInv; infer_instance

/-- The lessor's `cluster` `cl` (2026-10-13, unit 9): not nil, its `Version()` returns `nil` or
a read-only version (the server's `RaftCluster`, names-only: a contract). -/
def clusterOk (cl : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cl = GoInterface.ok ci⌝ ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Version" ci.v)) (Val #()))
      {{ (v : Loc), RET #v;
        ⌜v = null⌝ ∨ ∃ ver : github_com.Masterminds.semver.v3.Version, v ↦□ ver }}))

instance clusterOk_persistent (cl : GoInterface) : Persistent (clusterOk (GF := GF) cl) := by
  unfold clusterOk; infer_instance

/-- **The lessor's configuration** (2026-10-13, unit 9; persistent): the fields `newLessor` sets
and nothing writes after (`minLeaseTTL`, `checkpointPersist`, `cluster` with its contract,
`checkpointInterval`, `lg`, `leaseRevokeRate`, positive: `Promote` indexes the sorted leases'
first when there are at least `leaseRevokeRate` of them, so a rate below `1` with no lease panics;
audit B4b, 2026-10-18). -/
def lessorCfg (lp : Loc) : IProp GF :=
  iprop(∃ (mt : w64) (cpp : Bool) (cl : GoInterface) (ci : _root_.Perennial.time.Duration)
      (lg : Loc) (rr : w64),
    lF go!"minLeaseTTL" lp ↦□ mt ∗ lF go!"checkpointPersist" lp ↦□ cpp ∗
    lF go!"cluster" lp ↦□ cl ∗ clusterOk cl ∗
    lF go!"checkpointInterval" lp ↦□ ci ∗ lF go!"lg" lp ↦□ lg ∗
    lF go!"leaseRevokeRate" lp ↦□ rr ∗ ⌜0 < sint.Z rr⌝)

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 1024 in
instance lessorCfg_persistent (lp : Loc) : Persistent (lessorCfg (GF := GF) lp) := by
  unfold lessorCfg; infer_instance

/-- `err` is one of the lessor's error variables `Grant` returns (`ErrLeaseNotFound`,
`ErrLeaseExists`, `ErrLeaseTTLTooLarge`: `leaseErrVar` of the package's facts). -/
def lessorErrIs (err : GoInterface) : IProp GF :=
  iprop(∃ (g : GoString) (e : GoInterfaceOk),
    ⌜g = ErrLeaseNotFound ∨ g = ErrLeaseExists ∨ g = ErrLeaseTTLTooLarge⌝ ∗
    globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance lessorErrIs_persistent (err : GoInterface) : Persistent (lessorErrIs (GF := GF) err) := by
  unfold lessorErrIs; infer_instance

/-- A reader slot of the lessor's lock (`GetLease`, `Lookup`). -/
def lessorRd (lp : Loc) (γl : GName) : IProp GF :=
  sync.ownRWMutex (lF go!"mu" lp) (lessorMu lp γl)

/-- **The range deleter's owner** (unit T3, 2026-10-24): the other half of the lessor's `rd`
field, at `rd`. `SetRangeDeleter` takes it (with the lock's half it writes the field) and
`Revoke` reads the field by it, outside the lock. `NewLessor` gives it at `nil`; mvcc's
constructors set the store's deleter with it. -/
def rdOwn (γl : GName) (rd : GoFunc) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lF go!"rd" lp ↦{DFrac.own (1 : Qp).half} rd)

/-- **The owner's resource of the live lease `l`** (of id `id`; unit T3): half the closers'
map's element (the other half is `leaseRevokers`'), (L2b) its half of the lease's item set (what
the item map `I` attaches to `id`) and a reader slot of the lease's lock (`Keys()`, in
`Revoke`). -/
def closerAt (γl γcl : GName) (I : GMap LeaseItem w64) (id : w64) (l : Loc) : IProp GF :=
  iprop(ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗ leaseItemsOwn l I id ∗
    sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l))

/-- **The lease owner's closers and items** (unit T3, 2026-10-24): for every lease of the live
set `L`, the closers' map's element (its `*Lease`, which the lessor's map agrees with), the right
to close its `revokec` and (L2b, 2026-10-25) the owner's half of its item set, the items the item
map `I` attaches to it; the owner's half of the item map `I`, every lease of which is live, (Q4 (b), 2026-10-31) every key of which is short.
Exclusive, so outside `le.mu`'s fractional invariant. -/
def leaseClosers (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName) (C : GMap w64 Loc) (im : Loc), lessorPinG γl lp γga γcl ∗
    ⌜∀ id : w64, id ∈ L ↔ (C.lookup id).isSome⌝ ∗
    lF go!"itemMap" lp ↦{DFrac.own (1 : Qp).half} im ∗ im ↦${DFrac.own (1 : Qp).half} I ∗
    ⌜∀ (it : LeaseItem) (id : w64), I.lookup it = some id → id ∈ L⌝ ∗ ⌜itemKeysShort I⌝ ∗
    ([∗map] id ↦ l ∈ C, closerAt γl γcl I id l) ∗
    (∃ (γr : LessorRdNames) (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)),
      lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗ ⌜hs.getLast? = some (C, I)⌝ ∗
      ghostMapAuth γr.2.1 (1 : Qp).half Sm))

/-- **The lease owner's revokers** (unit T3, 2026-10-25): for every lease of the live set `L`,
the other half of the closers' map's element and the right to close its `revokec`. Apart from
`leaseOwn` (which the store's puts and deletes take): `Revoke` keeps it while it deletes the
lease's keys, so that its half of the element says the lessor's map still has the lease it
looked up (`Grant` and `Revoke` take both). -/
def leaseRevokers (γl : GName) (L : List w64) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName) (C : GMap w64 Loc), lessorPinG γl lp γga γcl ∗
    ⌜∀ id : w64, id ∈ L ↔ (C.lookup id).isSome⌝ ∗
    [∗map] id ↦ l ∈ C, ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗
      ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c)

/-- **The lease owner's half** of the live set: holding it, `L` is the live set (the apply
thread's); (unit T3) with the live leases' closers and (L2b) the item map `I` (item to lease id)
and the live leases' item sets, which agree with it. -/
def leaseOwn (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(leaseFrag γl (1 : Qp).half L ∗ leaseClosers γl L I)

/-- The owner's resource at an equal item map. -/
theorem leaseOwn_eq {γl : GName} {L : List w64} {I J : GMap LeaseItem w64} (h : I = J) :
    leaseOwn (GF := GF) γl L I ⊢ leaseOwn γl L J := by
  subst h; exact .rfl

/-- A reader slot of the lessor of `γl`, wherever it is (`lessorPin`). -/
def lessorRdOf (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lessorRd lp γl)

/-- **A reader of the lessor `γl`** (the lease-keys plan, Part B, 2026-10-31): a reader slot of its
lock (`Lookup`) and a borrowing token `j` of the slot pool, at rest (`none`): with it, the reader
borrows the slot `j` of a lease's lock for one `Keys()` (`lessorRdBody`). -/
def lessorReader (γl : GName) : IProp GF :=
  iprop(∃ (γr : LessorRdNames) (j : Nat), lessorPinR γl γr ∗ lessorRdOf γl ∗
    ghostMapElem γr.2.2 j (DFrac.own (1 : Qp).half) (none : Option Loc))

/-- **The lease owner's resource** at the txn layer: its half of the live set and a reader slot
of the lessor's lock (`Lookup`); (unit T3) its revokers. -/
def lessorUser (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(leaseOwn γl L I ∗ lessorRdOf γl ∗ leaseRevokers γl L)

/-- **The owner's resource opened at the live lease `l` of `id`** (the lease-keys plan, item 1,
2026-10-31): the item map's keys short (`itemKeysShort`, which `leaseClosers` keeps), the lease `l`
(`isLeaseObj`), the owner's half of its item set (what `I` attaches to `id`) and a reader slot of
its lock, which `Keys()` takes, and the wand that closes the owner's resource back. `Lookup(id)`
by the owner gives it. Not persistent: a revoked lease keeps its `ID`
and `id` can be granted again, so "`l` is the lease of `id`" holds only of the owner's closers
at the time. -/
def leaseOwnOpen (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (id : w64) (l : Loc) :
    IProp GF :=
  iprop(⌜itemKeysShort I⌝ ∗ isLeaseObj γl l ∗ leaseItemsOwn l I id ∗
    sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l) ∗
    (leaseItemsOwn l I id ∗ sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l) -∗ leaseOwn γl L I))

/-- **The txn layer's owner resource after `Lookup(id)` returned `l`**: `nil` and the resource as
it was, or the reader slot, the revokers and the owner's resource opened at `l`. -/
def lessorUserOpen (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (id : w64) (l : Loc) :
    IProp GF :=
  iprop((⌜l = null⌝ ∗ lessorUser γl L I) ∨
    (lessorRdOf γl ∗ leaseRevokers γl L ∗ leaseOwnOpen γl L I id l))

/-- Two pins of one ghost map agree. -/
theorem lessorPin_agree (γl : GName) (lp lp' : Loc) :
    lessorPin (GF := GF) γl lp ∗ lessorPin γl lp' ⊢ ⌜lp = lp'⌝ := by
  unfold lessorPin lessorPinG lessorPinAll
  iintro ⟨⟨%γ1, %γ1', %γr1, H1⟩, ⟨%γ2, %γ2', %γr2, H2⟩⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

/-- Two pins of one ghost map agree on all their names. -/
theorem lessorPinG_agree (γl : GName) (lp lp' : Loc) (γga γga' γcl γcl' : GName) :
    lessorPinG (GF := GF) γl lp γga γcl ∗ lessorPinG γl lp' γga' γcl' ⊢
      ⌜lp = lp' ∧ γga = γga' ∧ γcl = γcl'⌝ := by
  unfold lessorPinG lessorPinAll
  iintro ⟨⟨%γr1, H1⟩, ⟨%γr2, H2⟩⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; exact ⟨rfl, rfl, rfl⟩

/-- Two pins of one ghost map agree on the reader-side names. -/
theorem lessorPinR_agree (γl : GName) (γr γr' : LessorRdNames) :
    lessorPinR (GF := GF) γl γr ∗ lessorPinR γl γr' ⊢ ⌜γr = γr'⌝ := by
  unfold lessorPinR lessorPinAll
  iintro ⟨⟨%lp1, %γa1, %γc1, H1⟩, ⟨%lp2, %γa2, %γc2, H2⟩⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

/-- Two shares of the live set agree. -/
theorem leaseFrag_agree (γl : GName) (q1 q2 : Qp) (L1 L2 : List w64) :
    leaseFrag (GF := GF) γl q1 L1 ∗ leaseFrag γl q2 L2 ⊢ ⌜L1 = L2⌝ := by
  unfold leaseFrag
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

/-- The owner's resource, closed back from its opening at a lease. -/
theorem leaseOwnOpen_close (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (id : w64)
    (l : Loc) : leaseOwnOpen (GF := GF) γl L I id l ⊢ leaseOwn γl L I := by
  unfold leaseOwnOpen
  iintro ⟨-, -, Hio, Hslot, Hback⟩
  iapply Hback; iframe

/-- The txn layer's owner resource, closed back after `Lookup`. -/
theorem lessorUserOpen_close (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (id : w64)
    (l : Loc) : lessorUserOpen (GF := GF) γl L I id l ⊢ lessorUser γl L I := by
  unfold lessorUserOpen
  iintro (⟨-, Hu⟩ | ⟨Hrd, Hrvk, Ho⟩)
  · iexact Hu
  · unfold lessorUser
    iframe Hrd Hrvk
    iapply leaseOwnOpen_close $$ Ho

/-- **Every lease of the owner's item map is live** (the lease-keys plan, item 2): so a lease not
in `L` (a `nil` `Lookup`) holds no key. -/
theorem leaseOwn_items_live (γl : GName) (L : List w64) (I : GMap LeaseItem w64) :
    leaseOwn (GF := GF) γl L I ⊢
      leaseOwn γl L I ∗ ⌜∀ (it : LeaseItem) (id : w64), I.lookup it = some id → id ∈ L⌝ := by
  unfold leaseOwn leaseClosers
  iintro ⟨Hfr, %lp, %γga, %γcl, %C, %im, #Hp, %HC, Him, HI, %HIL, %HIS, Hcm⟩
  isplitl
  · iframe Hfr
    iexists lp, γga, γcl, C, im
    iframe Hp Him HI Hcm
    ipureintro; exact ⟨HC, HIL, HIS⟩
  · ipureintro; exact HIL

/-- **Every key of the owner's item map is short** (Q4 (b)). -/
theorem leaseOwn_items_short (γl : GName) (L : List w64) (I : GMap LeaseItem w64) :
    leaseOwn (GF := GF) γl L I ⊢ leaseOwn γl L I ∗ ⌜itemKeysShort I⌝ := by
  unfold leaseOwn leaseClosers
  iintro ⟨Hfr, %lp, %γga, %γcl, %C, %im, #Hp, %HC, Him, HI, %HIL, %HIS, Hcm⟩
  isplitl
  · iframe Hfr
    iexists lp, γga, γcl, C, im
    iframe Hp Him HI Hcm
    ipureintro; exact ⟨HC, HIL, HIS⟩
  · ipureintro; exact HIS

/-- **The owner's item map's facts, through the txn layer's resource**: its keys short, its
leases live (the lease-keys plan: `checkLeasePuts` reads both before `Lookup`). -/
theorem lessorUser_items (γl : GName) (L : List w64) (I : GMap LeaseItem w64) :
    lessorUser (GF := GF) γl L I ⊢ lessorUser γl L I ∗
      ⌜itemKeysShort I ∧ ∀ (it : LeaseItem) (id : w64), I.lookup it = some id → id ∈ L⌝ := by
  unfold lessorUser
  iintro ⟨Ho, Hrd, Hrv⟩
  ihave ⟨Ho, %HIS⟩ := leaseOwn_items_short γl L I $$ Ho
  ihave ⟨Ho, %HIL⟩ := leaseOwn_items_live γl L I $$ Ho
  iframe Ho Hrd Hrv
  ipureintro; exact ⟨HIS, HIL⟩

end defs

end lease
end EtcdGrove
end Perennial
