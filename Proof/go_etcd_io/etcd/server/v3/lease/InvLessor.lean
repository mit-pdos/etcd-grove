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
public import Perennial.Proof.ThreadPool

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
history of its snapshots (`γr.1`, a monotone list) and the item sets' map (`γr.2`, each `*Lease`
to its item set). -/
abbrev LessorRdNames := GName × GName

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
    ghostMapElem γr.2 l (DFrac.own q) S)

/-- `Unit` values are equal (the item sets' values). -/
instance unit_intoValInj : go.IntoValInj Unit where
  intoVal_inj x y _ := by cases x; cases y; rfl

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

/-- **The item sets agree with the history**: every lease of the history has a set (so a `*Lease`
`Grant` has just made, not in the map `Sm`, is in no snapshot: the Probe, 2026-10-31); and each
`*Lease`'s set is its id's items at the last index the lease map has it, or, if no lease map of the
history has it yet, empty (`Grant` registers a new lease's empty set when it makes the lease's
lock, before it takes `le.mu` and puts the lease in the map; a lease `Grant` then refuses,
`ErrLeaseExists`, stays there, never live). -/
def setsOk (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)) : Prop :=
  (∀ (i : Nat) (σ : LSnap) (id : w64) (l : Loc), hs[i]? = some σ → σ.1.lookup id = some l →
    (Sm.lookup l).isSome) ∧
  ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S →
    ((∀ (i : Nat) (σ : LSnap) (id : w64), hs[i]? = some σ → σ.1.lookup id ≠ some l) ∧ S = ∅) ∨
    ∃ (id : w64) (i : Nat) (σ : LSnap), lastLiveAt hs id l i ∧ hs[i]? = some σ ∧ itemsFor σ.2 id S

/-- **The history's facts**: not empty, each lease under one id, every snapshot's keys short. -/
def histOk (hs : List LSnap) : Prop :=
  hs ≠ [] ∧ oneIdPerLease hs ∧ ∀ σ ∈ hs, itemKeysShort σ.2

def lessorRdN : Namespace := nroot .@ "lessor_rd"

/-- **The lessor's reader-side invariant** at the names `γr`: a quarter of the history's
authority (`hs`; the owner holds half, `leaseClosers`, and `le.mu`'s invariant a quarter, so that
the owner appends holding the write lock), half of the item sets' map's authority (`Sm`; the owner
the other half), `setsOk` and `histOk`, and every `*Lease` of the item sets' map's `ID` (read-only:
so a `*Lease` `Grant` has just made, whose `ID` it owns, is not one of them). -/
def lessorRdBody (γr : LessorRdNames) : IProp GF :=
  iprop(∃ (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)),
    monoListAuthOwn γr.1 Qp.quarter hs ∗ ghostMapAuth γr.2 (1 : Qp).half Sm ∗
    ⌜setsOk hs Sm ∧ histOk hs⌝ ∗ [∗map] l ↦ _S ∈ Sm, ∃ id : w64, lsF go!"ID" l ↦□ id)

/-- **The lessor `γl`'s reader-side invariant** (persistent). -/
def lessorRdInv (γl : GName) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ inv lessorRdN (lessorRdBody γr))

instance lessorRdInv_persistent (γl : GName) : Persistent (lessorRdInv (GF := GF) γl) := by
  unfold lessorRdInv; infer_instance

/-- **The index `i` of the lessor `γl`'s history is the snapshot `σ`** (persistent). -/
def lessorAt (γl : GName) (i : Nat) (σ : LSnap) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ monoListIdxOwn γr.1 i σ)

instance lessorAt_persistent (γl : GName) (i : Nat) (σ : LSnap) :
    Persistent (lessorAt (GF := GF) γl i σ) := by
  unfold lessorAt; infer_instance

/-- **A lower bound `m` of the lessor's history** (persistent): a prefix of it, with an index `m`.
What a reader holds of the history it has observed (`lessorLb_get`); smaller bounds follow
(`lessorLb_le`). -/
def lessorLb (γl : GName) (m : Nat) : IProp GF :=
  iprop(∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗ monoListLbOwn γr.1 hs ∗
    ⌜m < hs.length⌝)

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

/-- A smaller lower bound. -/
theorem lessorLb_le (γl : GName) {m : Nat} (m' : Nat) (h : m' ≤ m) :
    lessorLb (GF := GF) γl m ⊢ lessorLb γl m' := by
  unfold lessorLb
  iintro ⟨%γr, %hs, #Hp, #Hlb, %Hm⟩
  iexists γr, hs; iframe Hp Hlb; ipureintro; omega

/-- **A reader takes a lower bound of the history** (the current one: the history's last index). -/
theorem lessorLb_get (γl : GName) (E : CoPset) (hE : ↑lessorRdN ⊆ E) :
    lessorRdInv (GF := GF) γl ⊢ |={E}=> ∃ m : Nat, lessorLb γl m := by
  unfold lessorRdInv lessorLb
  iintro ⟨%γr, #Hp, #Hinv⟩
  iinv Hinv with Hi Hclose
  iunfold lessorRdBody at Hi
  icases Hi with ⟨%hs, %Sm, >Ha, HS, >%Hok, Hids⟩
  ihave #Hlb := monoListLbOwn_get γr.1 _ hs $$ Ha
  imod Hclose $$ [Ha HS Hids] with -
  · inext; iunfold lessorRdBody; iexists hs, Sm; iframe Ha HS Hids; ipureintro; exact Hok
  imodintro
  iexists hs.length - 1, γr, hs
  iframe Hp Hlb
  ipureintro
  have : hs ≠ [] := Hok.2.1
  have : 0 < hs.length := List.length_pos_iff.2 this
  omega

/-- **A lease found at an index no earlier than `m` raises the bound** to that index. -/
theorem leaseLiveFrom_lb (γl : GName) (m : Nat) (id : w64) (l : Loc) :
    leaseLiveFrom (GF := GF) γl m id l ⊢ ∃ m' : Nat, ⌜m ≤ m'⌝ ∗ lessorLb γl m' ∗
      leaseLiveFrom γl m' id l := by
  unfold leaseLiveFrom lessorAt lessorLb monoListIdxOwn
  iintro #⟨%i, %σ, %Hi, %γr, #Hp, %hs, %Hhs, #Hlb⟩
  iexists i
  isplitr
  · ipureintro; exact Hi.1
  isplitr
  · iexists γr, hs; iframe Hp Hlb; ipureintro
    exact (List.getElem?_eq_some_iff.1 Hhs).1
  iexists i, σ
  isplitr
  · ipureintro; exact ⟨Nat.le_refl i, Hi.2⟩
  iexists γr; iframe Hp; iexists hs; iframe Hlb; ipureintro; exact Hhs

/-- **The keys a reader read are short** (every key of a snapshot's item map is). -/
theorem leaseKeysFrom_short (γl : GName) (m : Nat) (id : w64) (l : Loc) (ks : List GoString) :
    leaseKeysFrom (GF := GF) γl m id l ks ⊢ ⌜∀ k ∈ ks, k.length < 2 ^ 63 - 1⌝ := by
  unfold leaseKeysFrom
  iintro ⟨%i, %σ, %H, -⟩
  ipureintro
  intro k hk
  have h := H.2.2.2 ⟨k⟩ id ((H.2.2.1 k).1 hk)
  simp only at h
  omega

/-- **The lease owner's half of the item set of the lease `l`** (of id `id`), which is what the
item map `I` attaches to `id` (unit T3, L2b). -/
def leaseItemsOwn (l : Loc) (I : GMap LeaseItem w64) (id : w64) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own (1 : Qp).half} sm ∗
    sm ↦${DFrac.own (1 : Qp).half} S ∗ ⌜itemsFor I id S⌝)

def leasePoolN : Namespace := nroot .@ "lease_pool"

/-- A lease of the map (persistent): not nil, its lock guarding its item set, the lessor's
reader-side invariant, and (Part B) a thread pool of its lock's reader slots, from which a reader
borrows one with its thread token (`threadPool`, Perennial's `ThreadPool.lean`): `Grant` gives it
every slot but the owner's (`closerAt`), `actualMaxReaders - 1 = 2^30 - 2` of them, enough when at
most `2^30 - 1` threads are live (`threadBound GF ≤ 2^30 - 1`, the premise under which the pool
exists: `threadPool.init` needs `threadBound ≤ n + 1`; found by Part B's Probe). -/
def isLeaseObj (γl : GName) (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ sync.isRWMutexGuard (lsF go!"mu" l) (leaseItems γl l) ∗ lessorRdInv γl ∗
    □ (⌜threadBound GF ≤ 2 ^ 30 - 1⌝ → ∃ γp : GName,
      threadPool.isThreadPool leasePoolN γp (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l))))

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
after releasing the lock); every lease of the map `isLeaseObj`; (2026-10-13, unit 9) the apply-side fields
(`lessorExtra`); and (lease-keys Part B, 2026-10-31) a share `q/4` of the lessor's history
(`monoListAuthOwn γr.1`, the readers' model: `lessorRdBody` holds `1/4`, `leaseClosers` `1/2`), whose
last snapshot is the map `M` with the item map `I`: a writer under the lock with the owner's half
(`Grant`, `Revoke`, `Recover`) appends to it. -/
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
map `I` attaches to it; the owner's half of the item map `I`, every lease of which is live, (Q4 (b), 2026-10-31) every key of which is short; and
(lease-keys Part B, 2026-10-31) half of the lessor's history, whose last snapshot is `(C, I)` (`C`
is `lessorMu`'s map `M`: the two agree through `γcl`'s elements, and with `lessorMu`'s share the last
snapshots are equal), and half of the item-sets map's authority (`γr.2`, the item set of each
`*Lease` ever in the history; the other half is `lessorRdBody`'s). Exclusive, so outside `le.mu`'s
fractional invariant. -/
def leaseClosers (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName) (C : GMap w64 Loc) (im : Loc), lessorPinG γl lp γga γcl ∗
    ⌜∀ id : w64, id ∈ L ↔ (C.lookup id).isSome⌝ ∗
    lF go!"itemMap" lp ↦{DFrac.own (1 : Qp).half} im ∗ im ↦${DFrac.own (1 : Qp).half} I ∗
    ⌜∀ (it : LeaseItem) (id : w64), I.lookup it = some id → id ∈ L⌝ ∗ ⌜itemKeysShort I⌝ ∗
    ([∗map] id ↦ l ∈ C, closerAt γl γcl I id l) ∗
    (∃ (γr : LessorRdNames) (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)),
      lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗ ⌜hs.getLast? = some (C, I)⌝ ∗
      ghostMapAuth γr.2 (1 : Qp).half Sm))

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

/-- **The owner holds a lower bound of the history** (its index `0`: the history is never
empty). -/
theorem leaseOwn_lb (γl : GName) (L : List w64) (I : GMap LeaseItem w64) :
    leaseOwn (GF := GF) γl L I ⊢ leaseOwn γl L I ∗ lessorLb γl 0 := by
  unfold leaseOwn leaseClosers
  iintro ⟨Hf, %lp, %γga, %γcl, %C, %im, #Hp, %HC, Him, HI, %HIL, %HIS, Hcs, %γr, %hs, %Sm, #Hpr,
    Ha, %Hlast, HSm⟩
  ihave #Hlb := monoListLbOwn_get γr.1 _ hs $$ Ha
  isplitl [Hf Him HI Hcs Ha HSm]
  · iframe Hf
    iexists lp, γga, γcl, C, im
    iframe Hp Him HI Hcs
    isplitr; · ipureintro; exact HC
    isplitr; · ipureintro; exact HIL
    isplitr; · ipureintro; exact HIS
    iexists γr, hs, Sm; iframe Hpr Ha HSm; ipureintro; exact Hlast
  iunfold lessorLb
  iexists γr, hs; iframe Hpr Hlb
  ipureintro
  cases hs with
  | nil => simp at Hlast
  | cons _ _ => simp

/-! ### One spec for the owner and the readers (Part B, 2026-10-31)

`Lookup` and `Lease.Keys` are called by the lease owner (the apply thread) and by readers (the
server's API layer); each has one spec, which takes the caller's view: the owner's resource, or
nothing more than a reader's (Part A's `LeaseView` pattern). -/

/-- **The owner's view before `Lookup(id)`**: the owner's resource at `(L, I)`, or nothing (a
reader). -/
def lookupView (γl : GName) : Option (List w64 × GMap LeaseItem w64) → IProp GF
  | none => iprop(True)
  | some (L, I) => leaseOwn γl L I

theorem lookupView_none (γl : GName) : lookupView (GF := GF) γl none = iprop(True) := rfl
theorem lookupView_some (γl : GName) (L : List w64) (I : GMap LeaseItem w64) :
    lookupView (GF := GF) γl (some (L, I)) = leaseOwn γl L I := rfl

/-- **The owner's view after `Lookup(id)` returned `l`**: `nil` exactly when `id` is not live, and
the owner's resource as it was or opened at `l` (`leaseOwnOpen`); nothing for a reader. -/
def lookupViewAfter (γl : GName) (id : w64) (l : Loc) :
    Option (List w64 × GMap LeaseItem w64) → IProp GF
  | none => iprop(True)
  | some (L, I) => iprop(⌜l = null ↔ id ∉ L⌝ ∗ ((⌜l = null⌝ ∗ leaseOwn γl L I) ∨ leaseOwnOpen γl L I id l))

theorem lookupViewAfter_none (γl : GName) (id : w64) (l : Loc) :
    lookupViewAfter (GF := GF) γl id l none = iprop(True) := rfl
theorem lookupViewAfter_some (γl : GName) (id : w64) (l : Loc) (L : List w64) (I : GMap LeaseItem w64) :
    lookupViewAfter (GF := GF) γl id l (some (L, I)) =
      iprop(⌜l = null ↔ id ∉ L⌝ ∗ ((⌜l = null⌝ ∗ leaseOwn γl L I) ∨ leaseOwnOpen γl L I id l)) := rfl

/-- **Who calls `l.Keys()`**: the owner, at its item map `I`; or a reader with a lower bound `m` of
the history. -/
inductive KeysBy where
  | owner (I : GMap LeaseItem w64)
  | reader (m : Nat)

/-- **What `l.Keys()` of the lease `l` of `id` takes**: the owner's half of the item set and a
reader slot of `l.mu`; or, for a reader, `l` the lease of `id` at an index no earlier than `m`, and a
thread token, with which it borrows a slot from `l`'s pool (at most `2^30 - 1` live threads). -/
def keysPre (γl : GName) (l : Loc) (id : w64) : KeysBy → IProp GF
  | .owner I => iprop(leaseItemsOwn l I id ∗ sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l))
  | .reader m => iprop(leaseLiveFrom γl m id l ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝)

/-- **What `l.Keys()` returned `ks` says**: for the owner, exactly the keys `I` attaches to `id`;
for a reader, the keys of `l` at an index no earlier than `m` (`leaseKeysFrom`). -/
def keysPost (γl : GName) (l : Loc) (id : w64) (ks : List GoString) : KeysBy → IProp GF
  | .owner I => iprop(⌜∀ k : GoString, k ∈ ks ↔ I.lookup (LeaseItem.mk k) = some id⌝)
  | .reader m => leaseKeysFrom γl m id l ks

theorem keysPre_owner (γl : GName) (l : Loc) (id : w64) (I : GMap LeaseItem w64) :
    keysPre (GF := GF) γl l id (.owner I) =
      iprop(leaseItemsOwn l I id ∗ sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l)) := rfl
theorem keysPre_reader (γl : GName) (l : Loc) (id : w64) (m : Nat) :
    keysPre (GF := GF) γl l id (.reader m) =
      iprop(leaseLiveFrom γl m id l ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝) := rfl
theorem keysPost_owner (γl : GName) (l : Loc) (id : w64) (ks : List GoString) (I : GMap LeaseItem w64) :
    keysPost (GF := GF) γl l id ks (.owner I) =
      iprop(⌜∀ k : GoString, k ∈ ks ↔ I.lookup (LeaseItem.mk k) = some id⌝) := rfl
theorem keysPost_reader (γl : GName) (l : Loc) (id : w64) (ks : List GoString) (m : Nat) :
    keysPost (GF := GF) γl l id ks (.reader m) = leaseKeysFrom γl m id l ks := rfl

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

/-- **A `w64` field owned whole is not also read-only** (a local workaround: Perennial's typed
points-to has value agreement but no fraction validity, `notes/perennial-changes.md`): through its
first byte's heap points-to. -/
theorem w64_own_discard_false (l : Loc) (v w : w64) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ∗ typedPointsto l w DFrac.discard ⊢ False := by
  have first : ∀ (x : w64) (dq : DFrac), ∃ b : w8,
      typedPointsto (GF := GF) l x dq ⊢ heapPointsto l dq (LitV (LitByte b)) := fun x dq => by
    cases h : natBytes 8 x.toNat with
    | nil => have := natBytes_length 8 x.toNat; rw [h] at this; simp at this
    | cons b bs =>
      refine ⟨b, (typedPointsto_split l x dq).trans ?_⟩
      rw [typedPointstoDef_w64, h]
      exact sep_elim_left
  obtain ⟨b1, k1⟩ := first v (DFrac.own 1)
  obtain ⟨b2, k2⟩ := first w DFrac.discard
  iintro ⟨H1, H2⟩
  ihave H1 := k1 $$ H1
  ihave H2 := k2 $$ H2
  icombine H1 H2 gives %Hc
  have h := DFrac.valid_own_op_discard.1 Hc.1
  exact absurd h (by simp)

/-- **`Grant` registers a new `*Lease`** (Part B, the Probe): its empty item set enters the item
sets' map (with the owner's half of its authority), the whole element for the lease's lock, and its
`ID`, which no other goroutine can have written, becomes read-only. It is in no snapshot of the
history: its `ID` was exclusive, so it was not in the map, which has every lease of the history
(`setsOk`). -/
theorem itemSet_register (γl : GName) (γr : LessorRdNames) (l : Loc) (id : w64)
    (Sm0 : GMap Loc (GMap LeaseItem Unit)) (E : CoPset) (hE : ↑lessorRdN ⊆ E) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ ghostMapAuth γr.2 (1 : Qp).half Sm0 ∗
      lsF go!"ID" l ↦ id ⊢
    |={E}=> ghostMapAuth γr.2 (1 : Qp).half (Sm0.insert l (∅ : GMap LeaseItem Unit)) ∗
      ghostMapElem γr.2 l (DFrac.own 1) (∅ : GMap LeaseItem Unit) ∗
      lsF go!"ID" l ↦□ id := by
  unfold lessorRdInv
  iintro ⟨⟨%γr1, #Hp1, #Hinv⟩, #Hp, Ho, HID⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  subst H1
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs, %Sm, >Ha, >HS, >%Hok, #>Hids⟩
  ihave %HSm := ghostMapAuth_agree γr.2 _ _ Sm0 Sm $$ Ho HS
  subst HSm
  cases Hfresh : Sm0.lookup l with
  | some S =>
    ihave ⟨%id', HID'⟩ := BigSepM.bigSepM_lookup Hfresh $$ Hids
    iexfalso
    iapply w64_own_discard_false _ id id' $$ [$HID $HID']
  | none =>
  ihave Hfull := (ghostMapAuth_halves γr.2 Sm0).2 $$ [$Ho $HS]
  imod ghost_map_insert l (∅ : GMap LeaseItem Unit) Hfresh $$ Hfull with ⟨Hfull, He⟩
  icases (ghostMapAuth_halves γr.2 _).1 $$ Hfull with ⟨Ho, HS⟩
  ipersist HID
  have Hok' : setsOk hs (Sm0.insert l ∅) ∧ histOk hs := by
    refine ⟨⟨fun i σ id' l' hi hl' => ?_, fun l' S hS => ?_⟩, Hok.2⟩
    · have h := Hok.1.1 i σ id' l' hi hl'
      rw [GMap.lookup_insert_eq_iff]
      split
      · rfl
      · exact h
    · rw [GMap.lookup_insert_eq_iff] at hS
      split at hS
      · rename_i hll
        subst hll
        cases hS
        left
        refine ⟨fun i σ id' hi hl => ?_, rfl⟩
        have h := Hok.1.1 i σ id' l hi hl
        rw [Hfresh] at h
        exact Bool.false_ne_true h
      · exact Hok.1.2 l' S hS
  imod Hclose $$ [Ha HS] with -
  · inext; iunfold lessorRdBody; iexists hs, Sm0.insert l ∅; iframe Ha HS
    isplitr
    · ipureintro; exact Hok'
    iapply (BigSepM.bigSepM_insert (Φ := fun l _ => iprop(∃ id : w64, lsF go!"ID" l ↦□ id))
      (show Iris.Std.PartialMap.get? Sm0 l = none from Hfresh)).2
    isplitr
    · iexists id; iexact HID
    iexact Hids
  imodintro
  iframe
  iexact HID

/-- **A reader's item set is its lease's keys in the history** (Part B; `Keys()` from a reader):
the element `S` of the item sets' map of a lease `l` of `id` at an index `≥ m` is what the item map
attaches to `id` at an index `≥ m` where the lease map has `l` (the last one that has it: `setsOk`,
the same id there: `oneIdPerLease`), every key of it short. -/
theorem itemSet_keysFrom (γl : GName) (γr : LessorRdNames) (l : Loc) (dq : DFrac)
    (S : GMap LeaseItem Unit) (m : Nat) (id : w64) (E : CoPset) (hE : ↑lessorRdN ⊆ E) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ leaseLiveFrom γl m id l ∗
      ghostMapElem γr.2 l dq S ⊢
    |={E}=> ghostMapElem γr.2 l dq S ∗ ∃ (i : Nat) (σ : LSnap),
      ⌜m ≤ i ∧ σ.1.lookup id = some l ∧ itemsFor σ.2 id S ∧ itemKeysShort σ.2⌝ ∗
      lessorAt γl i σ := by
  unfold lessorRdInv leaseLiveFrom lessorAt
  iintro ⟨⟨%γr1, #Hp1, #Hinv⟩, #Hp, #⟨%i, %σ, %Hi, %γr2, #Hp2, #Hidx⟩, He⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  ihave %H2 := lessorPinR_agree γl γr γr2 $$ [$Hp $Hp2]
  subst H1; subst H2
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs, %Sm, >Ha, >HS, >%Hok, Hids⟩
  ihave %HSm := ghost_map_lookup $$ HS He
  ihave %Hhs := mono_list_auth_idx_lookup γr.1 _ hs i σ $$ Ha Hidx
  ihave #Hlb := monoListLbOwn_get γr.1 _ hs $$ Ha
  rcases Hok.1.2 l S HSm with ⟨Hnever, -⟩ | ⟨id', j, τ, Hlast, Hj, Hit⟩
  · exact absurd Hi.2 (Hnever i σ id Hhs)
  obtain ⟨⟨τ', Hj', Hτ'⟩, Hlater⟩ := Hlast
  rw [Hj] at Hj'
  cases Hj'
  have Hid : id = id' := Hok.2.2.1 i j σ τ id id' l Hhs Hj Hi.2 Hτ'
  subst Hid
  have Hij : i ≤ j := by
    refine Nat.le_of_not_lt fun hlt => ?_
    exact Hlater i σ hlt Hhs Hi.2
  have Hshort : itemKeysShort τ.2 := Hok.2.2.2 τ (List.mem_of_getElem? Hj)
  ihave #Hidx' := monoListIdxOwn_get j τ Hj $$ Hlb
  imod Hclose $$ [Ha HS Hids] with -
  · inext; iunfold lessorRdBody; iexists hs, Sm; iframe Ha HS Hids; ipureintro; exact Hok
  imodintro
  iframe He
  iexists j, τ
  isplitr
  · ipureintro; exact ⟨Nat.le_trans Hi.1 Hij, Hτ', Hit, Hshort⟩
  iexists γr; iframe Hp Hidx'

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
