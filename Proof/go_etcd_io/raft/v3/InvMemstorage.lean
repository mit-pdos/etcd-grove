/-
Port of `election_proof/inv_memstorage.v` (at feb5c73d4): `MemoryStorage`'s
representation predicate, the ownership predicate its `isStorageWith` instance
(`memstorage_instance.v`, `MemstorageInstance.lean`) is stated against.

### The ghost protocol of the pending append (2026-10-10)

Until 2026-10-10 the lock's invariant held half of a ghost variable of the storage's
state and `ownMemoryStorage ms σ` the other half: the owner (raft) knew the contents
exactly, and nobody else could change them. Now the application may append a batch
(`MemoryStorage.Append`, under the lock) while raft keeps reading (`StorState.pend`,
`InvStorage.lean`), so three ghost names, `MemStorNames`:

- `hist`, a `mono_list` of the states the owner has **sanctioned**, its authority held
  by the owner (`memView`): when idle, its last element is the state; when a batch is
  pending, its last element is the state once the batch is appended (`storAbsorb σ`).
  The hand-out law appends to it, without the lock.
- `done`, a `mono_list` of the states the storage has **been in**: the lock's invariant
  holds half of its authority, and the physical contents are its last element; the
  other half is the *writer's*: the owner's when idle, the application's while it
  appends (`memAppendTok`, then `memAppendedTok`). The invariant also holds a lower
  bound of `hist` at `done`: the storage has only been in sanctioned states.
- `ep`, a ghost variable of the current hand-out `(σ, H)` (the owner's state with the
  batch, and `done` at the hand-out), halved between the owner and the token, so that
  the absorb law knows the receipt is of this hand-out.

Raft, reading under the lock while a batch `p` is pending, holds `hist`'s authority at
`H ++ [storAbsorb σ]` and a lower bound of `done` at `H`; the invariant holds `done`'s
half at some `D` and a lower bound of `hist` at `D`. So `H <+: D <+: H ++ [_]`: the
contents are `H`'s last (`σ` without the batch) or the appended state, which agree
below the batch (`MemView`, `memView_agree`). `Append` (with the lock and the token)
moves `done` to `H ++ [storAbsorb σ]`; the absorb law (without the lock) gives the
writer's half back to the owner, at `hist`.

### raft v3.7 (stage R3 of the retarget, 2026-10-15)

`ms.ents` is a `[]*pb.Entry`: the storage's entries are read-only log entries
(`entsRO es (dummy :: σ.ents)`, `InvPbLog.lean`), the dummy at index 0 a fresh entry made by
`NewMemoryStorage` (`[]*pb.Entry{{}}`, `storage.go:122`), `ApplySnapshot` (235) or `Compact`
(284) and frozen like the others; `Append` keeps the caller's pointers (they are `entRO`
already). `hardState` holds a pointer to a read-only hard state or `nil` (`hsOpt`), replaced
wholesale by `SetHardState`. `snapshot` holds a pointer to the storage's own snapshot, owned
(`ownSnapM ... 1`): `Snapshot()` writes the field (`ms.snapshot = EnsureSnapshot(ms.snapshot)`,
213) and clones the object, `CreateSnapshot` writes the object's metadata in place (255-261),
`ApplySnapshot` stores a clone, and the unlocked `InitialState` reads both (and may write the
conf state's `AutoLeave`, `EnsureConfState`, 132, then freezes it: D7, the snapshot's conf state
`csOptA`'s third case from then on). Every one of them is called by the storage's
owner (raft through `isStorage`'s `Snapshot`, the application with `ownMemoryStorage` for the
others, `InitialState` at construction), so the field and the object were **`ownMemoryStorage`'s,
not the lock's** from the retarget to D17d (until the retarget the lock held half of a snapshot
value and `memStorMeta` the other half). Since D17d (2026-10-18) they are under the lock again, in
an invariant the keys open (`memSnapInv`, "The snapshot under the lock" below), so that the
application, holding its token (`memSnapTok`), can call `Snapshot()` while raft owns the storage
(etcd's `run`). `memStorMeta` keeps half of `hardState` and the unlocked counter.

### The application's compaction and the floor (D19i part 1, 2026-10-18)

The application (etcd's apply loop) compacts the storage (`Compact`) and replaces its snapshot
(`CreateSnapshot`) under the lock, while raft owns it, up to the floor raft published
(`StorState.fl`, `isStorageWith`'s `Hfloor`). So the lock's fields are the contents *cut* at a
boundary `c` (`memCut`), which the lock records (half a ghost value `cb`, the other half the
application's `memSnapTok`; its index a monotone counter `bd`, whose lower bounds are `storCut`),
and the storage's snapshot `S` may be newer than the contents' (a quarter of its ghost value is now
the lock's, the owner's moved there): the lock relates both to the contents (`memCutInv`) -- the
cut at an entry of the contents, within the floor unless it is the contents' own; the snapshot at
or above the cut, the contents' own or one the application took at an entry of the contents within
the floor. "Within the floor" is a lower bound of the owner's history (`memFlLb`): the history's
states carry their floor, which never goes down and each state holds (`HistOk`); raising the floor
records a state in `hist` without the lock, so `done` may lag behind `hist` by such raises
(`RaiseOnly`); during a pending batch the token holds half of `hist`'s authority, so no raise
happens then, and an append never rewrites what the floor covers (`PendAbove`). The application's
witness of the floor (`memFloorTok`) also tells it the storage holds entries up to the floor
(`memFloorTok_last`): the contents since the witness only raised the floor, or are past it.

Lean notes: Rocq's tuple `(prev, ents, ss)` in the ghost variable is the record
`StorState` (`InvStorage.lean`), as everywhere a storage's state is passed. `ghost_var γ (1/2) v` is `ghostVar γ (1 : Qp).half v`,
`is_Mutex` is `sync.isMutex`, `is_pkg_init raft` is `isPkgInit pkg_id.go_etcd_io.raft.v3`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorage

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- What raft's view `σ` of the storage knows of its contents `σp` (2026-10-10): the
boundary and the snapshot are the same, and the entries are `σ`'s or, with a batch
pending, `σ`'s with the batch appended; with nothing pending, exactly `σ`'s (D19i part 1: the
contents may lag behind the view's floor). -/
def MemView (σ σp : StorState) : Prop :=
  σp.prev = σ.prev ∧ (σp.ss = σ.ss ∧ σp.scs = σ.scs ∧ σp.sal = σ.sal ∧ σp.sdat = σ.sdat) ∧
  (σp.ents = σ.ents ∨ (σ.pend ≠ [] ∧ σp.ents = storApp σ σ.pend)) ∧
  (σ.pend = [] → σp.ents = σ.ents)

/-- A new storage (`NewMemoryStorage`): nothing stored, no snapshot, nothing pending. -/
def memStorEmpty : StorState :=
  { prev := entryID.mk (W64 0) (W64 0), ents := [], ss := entryID.mk (W64 0) (W64 0),
    pend := [] }

/-- The storage once `ApplySnapshot(snap)` succeeded (2026-10-12): the boundary is the
snapshot's id, nothing stored after it, the snapshot is `snap` (2026-10-15, stage S: with the
lists behind its `ConfState`), nothing pending. (Since the v3.7 retarget, stage R3, `snap` is the
snapshot's record and the lists its conf state's.) -/
def memStorApplied (snap : SnapshotM) : StorState :=
  { prev := snapId snap, ents := [], ss := snapId snap, pend := [],
    scs := snap.Metadata'.ConfState'.lists, sal := snap.Metadata'.ConfState'.AutoLeave',
    sdat := snap.Data' }

/-- The storage once `Compact(ci)` succeeded (2026-10-12): the boundary is `ci` at the
term `t` (its entry's), the stored entries those after it. -/
def memStorCompacted (σ : StorState) (ci t : w64) : StorState :=
  { σ with prev := entryID.mk t ci,
           ents := σ.ents.drop (uint.Z ci - uint.Z σ.prev.index').toNat }

/-- The conf state of the storage's snapshot at `σ`, as `σ` records it (`scs`, `sal`). -/
def storCS (σ : StorState) : ConfStateM :=
  ConfStateM.mk σ.scs.voters σ.scs.learners σ.scs.outgoing σ.scs.learnersNext σ.sal

/-- The snapshot `CreateSnapshot(i, cs, data)` leaves (2026-10-12): metadata at `i` and the term
`t` of `i`, its `ConfState` replaced by `*cs` when given (`oc`), else the storage's (`storCS σ`),
its data the bytes `bs` of `data`. (Since the v3.7 retarget, stage R3, a record built from the
storage's state: `CreateSnapshot` writes the storage's own snapshot in place.) -/
def memSnapCreated (σ : StorState) (i t : w64) (oc : Option ConfStateM) (bs : List w8) :
    SnapshotM :=
  SnapshotM.mk bs (SnapshotMetadataM.mk (oc.getD (storCS σ)) i t)

/-- What `CreateSnapshot` stores of the `ConfState` it is given (2026-10-14, B8): exactly
`*cs`; with `cs = nil`, the previous snapshot's. So an obligation the application states on the
`ConfState` it passes (A3, `SnapObl`, `SnapConf.lean`) holds of the stored one. -/
theorem memSnapCreated_confState (σ : StorState) (i t : w64) (c : ConfStateM) (bs : List w8) :
    (memSnapCreated σ i t (some c) bs).Metadata'.ConfState' = c := rfl

/-- The created snapshot's id: the index given, the term of that index. -/
theorem memSnapCreated_snapId (σ : StorState) (i t : w64) (oc : Option ConfStateM)
    (bs : List w8) : snapId (memSnapCreated σ i t oc bs) = entryID.mk t i := rfl

/-- (D22 J3) The storage's state with the snapshot `CreateSnapshot(i)` makes at the term `t`
(`memSnapCreated`): what its proof's linearization point names (the record written out in the
spec, `MemoryStorage.CreateSnapshot.spec`, is this, `rfl`). -/
def memStorCreated (σ : StorState) (i t : w64) (oc : Option ConfStateM) (bs : List w8) :
    StorState :=
  { σ with ss := entryID.mk t i,
           scs := (memSnapCreated σ i t oc bs).Metadata'.ConfState'.lists,
           sal := (memSnapCreated σ i t oc bs).Metadata'.ConfState'.AutoLeave',
           sdat := bs }

/-- `storApp` agrees with the stored entries below the batch. -/
theorem storApp_take (σ : StorState) (p : List EntryM) (m : Nat)
    (Hm : ∀ e0, p.head? = some e0 → (m : Int) ≤ uint.Z e0.Index' - uint.Z σ.prev.index' - 1)
    (Hlen : m ≤ σ.ents.length) :
    (storApp σ p).take m = σ.ents.take m := by
  cases p with
  | nil => rfl
  | cons e0 rest =>
    have := Hm e0 rfl
    simp only [storApp]
    rw [List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take,
      Nat.min_eq_left (by omega)]

theorem storApp_length_ge (σ : StorState) (p : List EntryM) (m : Nat)
    (Hm : ∀ e0, p.head? = some e0 → (m : Int) ≤ uint.Z e0.Index' - uint.Z σ.prev.index' - 1)
    (Hlen : m ≤ σ.ents.length) : m ≤ (storApp σ p).length := by
  have H := congrArg List.length (storApp_take σ p m Hm Hlen)
  simp only [List.length_take] at H
  omega

/-- `Term(i0)` below the batch reads the same in both contents. -/
theorem memView_term (σ σp : StorState) (H : MemView σ σp) (i0 : w64)
    (Hr : uint.Z σ.prev.index' ≤ uint.Z i0 ∧
      uint.Z i0 ≤ uint.Z σ.prev.index' + (σ.ents.length : Int))
    (Hb : PendFrom σ (uint.Z i0 + 1)) :
    (uint.Z σp.prev.index' ≤ uint.Z i0 ∧
      uint.Z i0 ≤ uint.Z σp.prev.index' + (σp.ents.length : Int)) ∧
    termAt σp.prev σp.ents i0 = termAt σ.prev σ.ents i0 := by
  obtain ⟨Hp, -, He, -⟩ := H
  have Hm : ∀ e0, σ.pend.head? = some e0 →
      ((uint.Z i0 - uint.Z σ.prev.index').toNat : Int) ≤
        uint.Z e0.Index' - uint.Z σ.prev.index' - 1 := by
    intro e0 He0; have := Hb e0 He0; omega
  have Hlen : (uint.Z i0 - uint.Z σ.prev.index').toNat ≤ σ.ents.length := by omega
  have Htk := storApp_take σ σ.pend _ Hm Hlen
  have Hge := storApp_length_ge σ σ.pend _ Hm Hlen
  rw [Hp]
  rcases He with He | ⟨-, He⟩ <;> rw [He]
  · exact ⟨Hr, rfl⟩
  refine ⟨⟨Hr.1, by omega⟩, ?_⟩
  unfold termAt
  by_cases Hi : uint.Z i0 = uint.Z σ.prev.index'
  · simp only [Hi, ↓reduceIte]
  · simp only [Hi, ↓reduceIte]
    have Hk : (uint.Z i0 - uint.Z σ.prev.index' - 1).toNat <
        (uint.Z i0 - uint.Z σ.prev.index').toNat := by omega
    rw [← List.getElem?_take_of_lt Hk, Htk, List.getElem?_take_of_lt Hk]

/-- `Entries(lo, hi)` below the batch reads the same in both contents. -/
theorem memView_entries (σ σp : StorState) (H : MemView σ σp) (lo hi : w64)
    (Hr : uint.Z σ.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
      uint.Z hi ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1)
    (Hb : PendFrom σ (uint.Z hi)) :
    (uint.Z σp.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
      uint.Z hi ≤ uint.Z σp.prev.index' + (σp.ents.length : Int) + 1) ∧
    σp.ents.take (uint.Z hi - uint.Z σp.prev.index' - 1).toNat =
      σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat ∧
    σp.prev = σ.prev := by
  obtain ⟨Hp, -, He, -⟩ := H
  have Hm : ∀ e0, σ.pend.head? = some e0 →
      ((uint.Z hi - uint.Z σ.prev.index' - 1).toNat : Int) ≤
        uint.Z e0.Index' - uint.Z σ.prev.index' - 1 := by
    intro e0 He0; have := Hb e0 He0; omega
  have Hlen : (uint.Z hi - uint.Z σ.prev.index' - 1).toNat ≤ σ.ents.length := by omega
  have Htk := storApp_take σ σ.pend _ Hm Hlen
  have Hge := storApp_length_ge σ σ.pend _ Hm Hlen
  rw [Hp]
  rcases He with He | ⟨-, He⟩ <;> rw [He]
  · exact ⟨Hr, rfl, rfl⟩
  exact ⟨⟨Hr.1, Hr.2.1, by omega⟩, Htk, rfl⟩

/-! ### The application's compaction and the floor (D19i part 1, 2026-10-18) -/

/-- Two states with the same data: equal but for the floor. -/
def DataEq (a b : StorState) : Prop :=
  a.prev = b.prev ∧ a.ents = b.ents ∧ a.ss = b.ss ∧ a.scs = b.scs ∧ a.sal = b.sal ∧
    a.pend = b.pend ∧ a.sdat = b.sdat

theorem DataEq.refl (a : StorState) : DataEq a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem DataEq.symm {a b : StorState} (h : DataEq a b) : DataEq b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.symm⟩

theorem DataEq.trans {a b c : StorState} (h1 : DataEq a b) (h2 : DataEq b c) : DataEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.1.trans h2.2.2.2.2.1, h1.2.2.2.2.2.1.trans h2.2.2.2.2.2.1,
    h1.2.2.2.2.2.2.trans h2.2.2.2.2.2.2⟩

theorem DataEq.fl (a : StorState) (x : w64) : DataEq { a with fl := x } a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A state's last index. -/
def stLast (σ : StorState) : Int := uint.Z σ.prev.index' + (σ.ents.length : Int)

theorem DataEq.stLast {a b : StorState} (h : DataEq a b) : stLast a = stLast b := by
  unfold EtcdGrove.stLast; rw [h.1, h.2.1]

/-- The owner's history of states (`hist`, and so `done`): the floors never go down, each state
holds its floor (at most its last index), records nothing pending, and numbers its entries by
their positions (`PlogWf`; the application's `Compact` reads its new boundary from the entry). -/
def HistOk (L : List StorState) : Prop :=
  L.Pairwise (fun a b => uint.Z a.fl ≤ uint.Z b.fl) ∧
  ∀ b ∈ L, uint.Z b.fl ≤ stLast b ∧ b.pend = [] ∧ PlogWf b.prev b.ents

/-- An append numbered consecutively, starting within the entries, keeps them numbered by their
positions. -/
theorem PlogWf_storApp (σ : StorState) (p : List EntryM) (H : PlogWf σ.prev σ.ents)
    (Hp : ∀ e0, p.head? = some e0 → uint.Z σ.prev.index' < uint.Z e0.Index' ∧
      uint.Z e0.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 ∧
      ∀ (k : Nat) (e : EntryM), p[k]? = some e → uint.Z e.Index' = uint.Z e0.Index' + (k : Int)) :
    PlogWf σ.prev (storApp σ p) := by
  cases p with
  | nil => exact H
  | cons e0 rest =>
    obtain ⟨h1, h2, h3⟩ := Hp e0 rfl
    intro k e hk
    simp only [storApp] at hk
    have hlen : ((σ.ents.take (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat).length : Int) =
        uint.Z e0.Index' - uint.Z σ.prev.index' - 1 := by
      rw [List.length_take]; omega
    by_cases hkm : k < (σ.ents.take (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat).length
    · rw [List.getElem?_append_left hkm, List.getElem?_take_of_lt (by omega)] at hk
      exact H k e hk
    · rw [List.getElem?_append_right (by omega)] at hk
      have := h3 _ e hk
      push_cast at this ⊢
      omega

theorem HistOk.prefix {L1 L2 : List StorState} (h : L1 <+: L2) (H : HistOk L2) : HistOk L1 :=
  ⟨H.1.sublist h.sublist, fun b hb => H.2 b (h.subset hb)⟩

/-- Every state of a history is at or below its last's floor. -/
theorem HistOk.le_last {L : List StorState} {w : StorState} (H : HistOk L)
    (hw : L.getLast? = some w) : ∀ a ∈ L, uint.Z a.fl ≤ uint.Z w.fl := by
  intro a ha
  obtain ⟨L', rfl⟩ : ∃ L', L = L' ++ [w] := by
    rw [List.getLast?_eq_some_iff] at hw; exact hw
  rcases List.mem_append.1 ha with ha | ha
  · exact (List.pairwise_append.1 H.1).2.2 a ha w (List.mem_singleton_self w)
  · rw [List.mem_singleton] at ha; subst ha; exact Int.le_refl _

/-- Of two histories, one a prefix of the other, the shorter's last floor is at most the
longer's. -/
theorem HistOk.last_mono {L1 L2 : List StorState} {a b : StorState} (h : L1 <+: L2)
    (H : HistOk L2) (ha : L1.getLast? = some a) (hb : L2.getLast? = some b) :
    uint.Z a.fl ≤ uint.Z b.fl :=
  H.le_last hb a (h.subset (List.mem_of_getLast? ha))

theorem HistOk.snoc {L : List StorState} {x : StorState} (H : HistOk L)
    (hle : ∀ w, L.getLast? = some w → uint.Z w.fl ≤ uint.Z x.fl)
    (hx : uint.Z x.fl ≤ stLast x) (hp : x.pend = []) (hi : PlogWf x.prev x.ents) :
    HistOk (L ++ [x]) := by
  refine ⟨List.pairwise_append.2 ⟨H.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩, ?_⟩
  · rw [List.mem_singleton] at hb; subst hb
    cases hL : L.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hL; subst hL; simp at ha
    | some w => exact Int.le_trans (H.le_last hL a ha) (hle w hL)
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact H.2 b hb
    · rw [List.mem_singleton] at hb; subst hb; exact ⟨hx, hp, hi⟩

/-- The states after `D` only raise the floor: each has the data of `D`'s last. -/
def RaiseOnly (D R : List StorState) : Prop :=
  ∀ w ∈ R, ∃ a, D.getLast? = some a ∧ DataEq w a

theorem RaiseOnly.nil (D : List StorState) : RaiseOnly D [] := fun _ h => by simp at h

/-- Of a history `L = D ++ R` with `R` raise-only, every state from `D`'s last on has its data. -/
theorem RaiseOnly.last {D L : List StorState} {a w : StorState} (hD : D <+: L)
    (hR : RaiseOnly D (L.drop D.length)) (ha : D.getLast? = some a) (hw : L.getLast? = some w) :
    DataEq w a := by
  obtain ⟨R, rfl⟩ := hD
  rw [List.drop_left] at hR
  cases R with
  | nil => rw [List.append_nil, ha] at hw; cases hw; exact DataEq.refl _
  | cons r R' =>
    have hw' : (r :: R').getLast? = some w := by
      rw [List.getLast?_append] at hw
      cases h : (r :: R').getLast? with
      | none => simp at h
      | some v => rw [h] at hw; simpa using hw
    obtain ⟨a', ha', hd⟩ := hR w (List.mem_of_getLast? hw')
    rw [ha] at ha'; cases ha'; exact hd

/-- The storage cut at the boundary `c` (`Compact`): `c` the dummy, the entries after it. -/
def memCut (σ : StorState) (c : entryID) : StorState :=
  { σ with prev := c, ents := σ.ents.drop (uint.Z c.index' - uint.Z σ.prev.index').toNat }

/-- A boundary the cut may have: an entry of the state, at or above its own boundary. -/
def CutOk (σ : StorState) (c : entryID) : Prop :=
  uint.Z σ.prev.index' ≤ uint.Z c.index' ∧ uint.Z c.index' ≤ stLast σ ∧
  termAt σ.prev σ.ents c.index' = some c.term'

theorem memCut_self (σ : StorState) : memCut σ σ.prev = σ := by
  simp [memCut]

theorem CutOk.self (σ : StorState) : CutOk σ σ.prev := by
  refine ⟨Int.le_refl _, ?_, ?_⟩
  · unfold EtcdGrove.stLast; have := Nat.zero_le σ.ents.length; omega
  · simp [termAt]

theorem memCut_stLast {σ : StorState} {c : entryID} (h : CutOk σ c) :
    stLast (memCut σ c) = stLast σ := by
  obtain ⟨h1, h2, -⟩ := h
  unfold EtcdGrove.stLast at h2 ⊢
  simp only [memCut, List.length_drop]
  omega

/-- Above the cut the cut state answers `Term` as the state. -/
theorem termAt_memCut {σ : StorState} {c : entryID} (h : CutOk σ c) (i : w64)
    (hi : uint.Z c.index' ≤ uint.Z i) :
    termAt c (σ.ents.drop (uint.Z c.index' - uint.Z σ.prev.index').toNat) i =
      termAt σ.prev σ.ents i := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases he : uint.Z i = uint.Z c.index'
  · have hi' : i = c.index' := by word
    subst hi'
    unfold termAt
    simp only [↓reduceIte]
    exact h3.symm
  unfold termAt
  rw [if_neg he]
  by_cases hp : uint.Z i = uint.Z σ.prev.index'
  · exfalso; omega
  rw [if_neg hp, List.getElem?_drop]
  congr 2
  omega

/-- ... and its entries from `lo` (above the cut) are the state's. -/
theorem memCut_drop {σ : StorState} {c : entryID} (h : CutOk σ c) (lo hi : w64)
    (hlo : uint.Z c.index' + 1 ≤ uint.Z lo) (hhi : uint.Z lo < uint.Z hi) :
    ((σ.ents.drop (uint.Z c.index' - uint.Z σ.prev.index').toNat).take
        (uint.Z hi - uint.Z c.index' - 1).toNat).drop (uint.Z lo - uint.Z c.index' - 1).toNat =
      (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat := by
  obtain ⟨h1, -, -⟩ := h
  rw [List.take_drop, List.drop_drop]
  have e1 : (uint.Z c.index' - uint.Z σ.prev.index').toNat + (uint.Z hi - uint.Z c.index' - 1).toNat
      = (uint.Z hi - uint.Z σ.prev.index' - 1).toNat := by omega
  have e2 : (uint.Z c.index' - uint.Z σ.prev.index').toNat + (uint.Z lo - uint.Z c.index' - 1).toNat
      = (uint.Z lo - uint.Z σ.prev.index' - 1).toNat := by omega
  rw [e1, e2]

/-- Appending above the cut commutes with the cut. -/
theorem storApp_memCut {σ : StorState} {c : entryID} (h : CutOk σ c) (p : List EntryM)
    (hp : ∀ e0, p.head? = some e0 → uint.Z c.index' < uint.Z e0.Index') :
    storApp (memCut σ c) p =
      (storApp σ p).drop (uint.Z c.index' - uint.Z σ.prev.index').toNat := by
  obtain ⟨h1, h2, -⟩ := h
  cases p with
  | nil => rfl
  | cons e0 rest =>
    have he := hp e0 rfl
    simp only [storApp, memCut]
    rw [List.drop_append_of_le_length (by rw [List.length_take]; unfold EtcdGrove.stLast at h2; omega),
      List.drop_take]
    congr 2
    omega

theorem CutOk.app {σ : StorState} {c : entryID} (h : CutOk σ c) (p : List EntryM)
    (hp : ∀ e0, p.head? = some e0 → uint.Z c.index' < uint.Z e0.Index')
    (hok : ∀ e0, p.head? = some e0 →
      uint.Z e0.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1) :
    CutOk { σ with ents := storApp σ p, pend := [] } c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · unfold EtcdGrove.stLast at h2 ⊢
    cases p with
    | nil => simpa [storApp] using h2
    | cons e0 rest =>
      have := hp e0 rfl
      have := hok e0 rfl
      simp only [storApp, List.length_append, List.length_take, List.length_cons]
      omega
  · cases p with
    | nil => simpa [storApp] using h3
    | cons e0 rest =>
      have he := hp e0 rfl
      have hk := hok e0 rfl
      unfold termAt at h3 ⊢
      split
      · rename_i hc; rw [if_pos hc] at h3; exact h3
      · rename_i hc
        simp only at hc
        rw [if_neg hc] at h3
        simp only [storApp]
        rw [List.getElem?_append_left (by
          rw [List.length_take]
          have : (uint.Z c.index' - uint.Z σ.prev.index' - 1).toNat < σ.ents.length := by
            cases hg : σ.ents[(uint.Z c.index' - uint.Z σ.prev.index' - 1).toNat]? with
            | none => rw [hg] at h3; cases h3
            | some _ => exact (List.getElem?_eq_some_iff.1 hg).1
          omega),
          List.getElem?_take_of_lt (by omega)]
        exact h3

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- (2026-10-16, stage R6b) `EntryM`'s countability is `Protocol/Ghost.lean`'s
-- `raftpbEntry_countable`; a second instance here made two `ghostVar`s over `List EntryM` differ
-- in importers of both.

instance storState_countable : Pos.Countable StorState :=
  .ofInjective (fun σ => Pos.Countable.encode
      (((((((σ.prev, σ.ents), σ.ss), σ.pend),
        (((σ.scs.voters, σ.scs.learners), σ.scs.outgoing), σ.scs.learnersNext)), σ.sal), σ.sdat),
        σ.fl))
    (fun ⟨_, _, _, _, ⟨_, _, _, _⟩, _, _, _⟩ ⟨_, _, _, _, ⟨_, _, _, _⟩, _, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩⟩, rfl⟩, rfl⟩, rfl⟩ := h
      rfl)

/-- (D22 S-b′2, 2026-10-20) For the certificate registry (`MemStorNames.cert`). -/
instance snapTrip_countable : Pos.Countable SnapTrip :=
  .ofInjective (fun k => Pos.Countable.encode
      (((k.sid, (((k.cl.voters, k.cl.learners), k.cl.outgoing), k.cl.learnersNext)), k.al), k.dat))
    (fun ⟨_, ⟨_, _, _, _⟩, _, _⟩ ⟨_, ⟨_, _, _, _⟩, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨⟨rfl, ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩⟩, rfl⟩, rfl⟩ := h
      rfl)

/-- (D22 S-b′2) An entry of the certificate registry: a snapshot, and whether the entry
certifies it **at any term** (`true`: every snapshot at its index with its lists and `AutoLeave`,
whatever its term; what `CreateSnapshot`, which reads the term from the storage, needs) or at its
own (`false`). -/
abbrev CertKey := SnapTrip × Bool

/-- What a registry entry certifies. -/
def certCovers (e : CertKey) (k : SnapTrip) : Prop :=
  if e.2 then e.1.sid.index' = k.sid.index' ∧ e.1.cl = k.cl ∧ e.1.al = k.al ∧ e.1.dat = k.dat
  else e.1 = k

/-- The ghost names of a `MemoryStorage` (2026-10-10; until then one `GName`, of the
ghost variable of its state): see the file header. -/
structure MemStorNames where
  hist : GName
  done : GName
  ep : GName
  /-- (D17d, 2026-10-18) the snapshot's ghost value (`snapPart` of the state): half at home in
  `memSnapInv`, a quarter the lock's (D19i part 1; until then the owner's), a quarter the
  application's (`memSnapTok`). -/
  sn : GName
  /-- (D17d) where the snapshot is (`memSnapInv`): `0` home, `k ≠ 0` out against `memSnapKeys k`. -/
  sw : GName
  /-- (D17d) the keys: the lock's (`memstorageFields`), the owner's, the application's. -/
  lk : GName
  ok : GName
  ak : GName
  /-- (D19i part 1) the storage's true boundary (the entry the fields are cut at): half the lock's,
  half the application's (`memSnapTok`). -/
  cb : GName
  /-- (D19i part 1) the true boundary's index, a monotone counter: the lock's authority, the
  `storCut` facts its lower bounds. -/
  bd : GName
  /-- (2026-10-19, D21 M3) the **cap**: the true boundary never passes it (`memCutInv`'s
  `Hccap`), so neither does any `storCut` fact (`memStorCut`); `Compact` and `ApplySnapshot` take
  it as a premise. Chosen at `NewMemoryStorage`; `2 ^ 64` (or more) is no cap. -/
  cap : Int
  /-- (D22 S-b′2, 2026-10-20) the **certificate registry**: a mono list of entries (`CertKey`)
  certifying snapshots for this storage (`memStorCert`, its persistent lower bounds). Its
  authority is `NewMemoryStorage`'s (`memCertAuth`), which the application puts in the invariant
  tying each element to raft's certificate (`memCertInv`, `MemstorageInstance.lean`); the
  snapshot's home (`memSnapHome`) keeps the current non-empty snapshot's, which
  `CreateSnapshot`/`ApplySnapshot` take of the new one and raft's `Snapshot` hands out. -/
  cert : GName

/-- The snapshot's part of a storage state (D17d, 2026-10-18): what the snapshot's ghost value
records (its id and conf state), the rest fixed. -/
def snapPart (σ : StorState) : StorState :=
  { prev := entryID.mk (W64 0) (W64 0), ents := [], ss := σ.ss, pend := [], scs := σ.scs,
    sal := σ.sal, sdat := σ.sdat }

theorem snapPart_inj {σ σ' : StorState} (h : snapPart σ = snapPart σ') :
    σ.ss = σ'.ss ∧ σ.scs = σ'.scs ∧ σ.sal = σ'.sal ∧ σ.sdat = σ'.sdat := by
  simp only [snapPart, StorState.mk.injEq] at h
  exact ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- A key (D17d): an exclusive token. -/
def memKey (γ : GName) : IProp GF := ghostVar γ 1 ()

theorem memKey_excl (γ : GName) : ⊢ memKey (GF := GF) γ -∗ memKey γ -∗ False := by
  iintro H1 H2
  iunfold memKey at H1 H2
  icases ghostVar_valid_2 γ () 1 () 1 $$ H1 H2 with %H
  exfalso
  obtain ⟨H, -⟩ := H
  grind

/-- The quarter of the snapshot's ghost value the lock and the application each hold. -/
abbrev memQ : Qp := (1 : Qp).half.half

/-- What the lock protects, at a given abstract state, *without* the ghost link: the
fields other than the mutex and the snapshot, and everything hanging off them. This is what the
private helpers `lastIndex`/firstIndex` are specified on -- they are called with the
lock held -- and what a public method holds between `Lock` and `Unlock`. The entries'
capacity is owned (2026-10-10): `Append` appends in place when the batch continues
the log.

Since 2026-10-12 (for `InitialState`, which reads `hardState` and increments
`callStats.initialState` *without* the lock) the lock holds half of `hardState`, the other half
being `memStorMeta`'s, and the counters of `callStats` but `initialState`, which is
`memStorMeta`'s. Since the v3.7 retarget (stage R3) the entries are read-only log entries
(`entsRO`, the dummy at index 0 among them), `hardState` a pointer (its object read-only,
`memStorMeta`'s `hsOpt`), and the snapshot is not the lock's at all (`ownMemoryStorage`'s). -/
def memstorageFields (ms : Loc) (σ : StorState) : IProp GF :=
  iprop(∃ (hp : Loc) (es : GoSlice) (dummy : EntryM) (nfi nli nen nte nsn : w64),
  "HhardState" ∷ ms.[MemoryStorage, go!"hardState"] ↦{DFrac.own (1 : Qp).half} hp ∗
  "Hents_f" ∷ ms.[MemoryStorage, go!"ents"] ↦ es ∗
  "Hents" ∷ entsRO es (dummy :: σ.ents) ∗
  "Hents_cap" ∷ ownSliceCap Loc es (DFrac.own 1) ∗
  "%Hdummy" ∷ ⌜dummy.Index' = σ.prev.index' ∧ dummy.Term' = σ.prev.term'⌝ ∗
  "Hcs_firstIndex" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"firstIndex"] ↦ nfi ∗
  "Hcs_lastIndex" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"lastIndex"] ↦ nli ∗
  "Hcs_entries" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"entries"] ↦ nen ∗
  "Hcs_term" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"term"] ↦ nte ∗
  "Hcs_snapshot" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"snapshot"] ↦ nsn)

/-- The fields read only the boundary and the entries. -/
theorem memstorageFields_congr (ms : Loc) (σ σ' : StorState) (h1 : σ'.prev = σ.prev)
    (h2 : σ'.ents = σ.ents) :
    memstorageFields (GF := GF) ms σ ⊢ memstorageFields ms σ' := by
  unfold memstorageFields
  rw [h1, h2]

/-- An append keeps the contents' terms below the batch. -/
theorem termAt_storApp_below (σ : StorState) (p : List EntryM) (i : w64)
    (Hpo : ∀ e0, p.head? = some e0 → uint.Z i < uint.Z e0.Index' ∧
      uint.Z e0.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1)
    (Hge : uint.Z σ.prev.index' ≤ uint.Z i) :
    termAt σ.prev (storApp σ p) i = termAt σ.prev σ.ents i := by
  cases p with
  | nil => rfl
  | cons e0 rest =>
    obtain ⟨h1, h2⟩ := Hpo e0 rfl
    unfold termAt
    split
    · rfl
    · simp only [storApp]
      rw [List.getElem?_append_left (by rw [List.length_take]; omega),
        List.getElem?_take_of_lt (by omega)]

/-- The storage's own snapshot at `σ` (stage R3): the `snapshot` field and the object it points
to, owned, its record's id, conf-state lists and `AutoLeave` the ones `σ` records (`ss`, `scs`,
`sal`; the data bytes are not in `σ`). Part of `ownMemoryStorage`, not of the lock's invariant
(see the file header). -/
def memSnapOwn (ms : Loc) (σ : StorState) : IProp GF :=
  iprop(∃ (sp : Loc) (sv : SnapshotM),
  "Hsnapshot" ∷ ms.[MemoryStorage, go!"snapshot"] ↦ sp ∗
  "Hsnap" ∷ ownSnapM sp (DFrac.own 1) sv ∗
  "%Hsnap_id" ∷ ⌜snapId sv = σ.ss ∧ sv.Metadata'.ConfState'.lists = σ.scs ∧
    sv.Metadata'.ConfState'.AutoLeave' = σ.sal ∧ sv.Data' = σ.sdat⌝)

/-- `memSnapOwn` reads only the snapshot's part of the state. -/
theorem memSnapOwn_congr (ms : Loc) (σ σ' : StorState) (h1 : σ'.ss = σ.ss)
    (h2 : σ'.scs = σ.scs) (h3 : σ'.sal = σ.sal) (h4 : σ'.sdat = σ.sdat) :
    memSnapOwn (GF := GF) ms σ ⊢ memSnapOwn ms σ' := by
  unfold memSnapOwn
  rw [h1, h2, h3, h4]

/-! ### The snapshot under the lock, lent before the node starts (D17d, 2026-10-18)

The storage's snapshot (`memSnapOwn`) is read and written under `ms.Mutex` by `Snapshot`,
`ApplySnapshot` and `CreateSnapshot`, and read (and its conf state's `AutoLeave` set) *without*
the lock by `InitialState` (`issues/raft-memorystorage-initialstate-unlocked.md`), which `newRaft`
calls once, before `StartNode`/`RestartNode` start the node's goroutine. So the snapshot cannot be
the lock's invariant's: it lives in an Iris invariant (`memSnapInv`) from which a *key* takes it
out -- the lock's key `lk` with the owner's `ok` (raft's `Snapshot`, and `ApplySnapshot`/
`CreateSnapshot`) or with the application's `ak` (the application's `Snapshot`), or, without the
lock, the owner's and the application's keys together (`InitialState`: "the token lends the
snapshot"). Taking it out deposits the keys used, and any two key sets overlap
(`memSnapKeys_excl`), so whoever holds a key set finds the snapshot at home. Its ghost value
(`snapPart`: id and conf state) is split between home (half), the lock (a quarter; until D19i part 1 the
owner's, `memSnapShare`)
and the application (`memSnapTok`, a quarter): `Snapshot` reads it, the writers (holding both
quarters) change it. -/

/-- The key sets that take the snapshot out (D17d): `1` the lock's and the owner's, `2` the lock's
and the application's, `3` the owner's and the application's (no lock: `InitialState`). -/
def memSnapKeys (γs : MemStorNames) (k : Nat) : IProp GF :=
  iprop((⌜k = 1⌝ ∗ memKey γs.lk ∗ memKey γs.ok) ∨ (⌜k = 2⌝ ∗ memKey γs.lk ∗ memKey γs.ak) ∨
    (⌜k = 3⌝ ∗ memKey γs.ok ∗ memKey γs.ak))

instance memSnapKeys_timeless (γs : MemStorNames) (k : Nat) :
    Timeless (memSnapKeys (GF := GF) γs k) := by
  unfold memSnapKeys memKey; infer_instance

/-- Any two key sets share a key. -/
theorem memSnapKeys_excl (γs : MemStorNames) (k j : Nat) :
    ⊢ memSnapKeys (GF := GF) γs k -∗ memSnapKeys γs j -∗ False := by
  iintro H1 H2
  iunfold memSnapKeys at H1 H2
  icases H1 with (⟨-, Ha, Hb⟩ | ⟨-, Ha, Hb⟩ | ⟨-, Ha, Hb⟩) <;>
  icases H2 with (⟨-, Hc, Hd⟩ | ⟨-, Hc, Hd⟩ | ⟨-, Hc, Hd⟩)
  all_goals first
    | iapply memKey_excl $$ Ha Hc
    | iapply memKey_excl $$ Ha Hd
    | iapply memKey_excl $$ Hb Hc
    | iapply memKey_excl $$ Hb Hd

/-- (D22 S-b′2, 2026-10-20) The snapshot `k` is in the storage's certificate registry
(persistent): an entry certifies it (`certCovers`). -/
def memStorCert (γs : MemStorNames) (k : SnapTrip) : IProp GF :=
  iprop(∃ L : List CertKey, monoListLbOwn γs.cert L ∗ ⌜∃ e ∈ L, certCovers e k⌝)

instance memStorCert_persistent (γs : MemStorNames) (k : SnapTrip) :
    Persistent (memStorCert (GF := GF) γs k) := by
  unfold memStorCert; infer_instance

omit [StorageModel GF] package_sem in
/-- An entry of the registry gives its certificate. -/
theorem memStorCert_of_lb (γs : MemStorNames) (L : List CertKey) (e : CertKey) (k : SnapTrip)
    (he : e ∈ L) (hc : certCovers e k) :
    monoListLbOwn (GF := GF) γs.cert L ⊢ memStorCert γs k := by
  iintro #H
  iunfold memStorCert
  iexists L
  iframe H
  ipureintro; exact ⟨e, he, hc⟩

/-- The registry's authority, empty (`NewMemoryStorage`'s): the application puts it in the
invariant that ties the registry to raft's certificates (`memCertInv`, `MemstorageInstance.lean`). -/
def memCertAuth (γs : MemStorNames) : IProp GF :=
  monoListAuthOwn γs.cert 1 ([] : List CertKey)

/-- The snapshot of the state `σ`, as the registry records it. -/
def StorState.trip (σ : StorState) : SnapTrip := ⟨σ.ss, σ.scs, σ.sal, σ.sdat⟩

/-- (D22 S-b′2) The state's snapshot is empty or certified (persistent). -/
def memSnapCertOk (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(⌜σ.ss.index' = W64 0⌝ ∨ memStorCert γs σ.trip)

instance memSnapCertOk_persistent (γs : MemStorNames) (σ : StorState) :
    Persistent (memSnapCertOk (GF := GF) γs σ) := by
  unfold memSnapCertOk; infer_instance

omit [StorageModel GF] package_sem in
/-- `memSnapCertOk` reads only the snapshot's part of the state. -/
theorem memSnapCertOk_congr (γs : MemStorNames) (σ σ' : StorState) (h1 : σ'.ss = σ.ss)
    (h2 : σ'.scs = σ.scs) (h3 : σ'.sal = σ.sal) (h4 : σ'.sdat = σ.sdat) :
    memSnapCertOk (GF := GF) γs σ ⊢ memSnapCertOk γs σ' := by
  unfold memSnapCertOk StorState.trip
  rw [h1, h2, h3, h4]

omit [StorageModel GF] package_sem in
/-- A snapshot record whose id, lists and `AutoLeave` are the state's: its certificate is the
state's. -/
theorem memSnapCertOk_sv (γs : MemStorNames) (σ : StorState) (sv : SnapshotM)
    (h : snapId sv = σ.ss ∧ sv.Metadata'.ConfState'.lists = σ.scs ∧
      sv.Metadata'.ConfState'.AutoLeave' = σ.sal ∧ sv.Data' = σ.sdat) :
    memSnapCertOk (GF := GF) γs σ ⊢
      ⌜sv.Metadata'.Index' = W64 0⌝ ∨ memStorCert γs (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  have ht : snapTrip sv sv.Metadata'.ConfState'.lists = σ.trip := by
    simp only [snapTrip, StorState.trip, h.1, h.2.1, h.2.2.1, h.2.2.2]
  have hi : sv.Metadata'.Index' = σ.ss.index' := by rw [← h.1]; rfl
  rw [ht, hi]
  unfold memSnapCertOk
  exact .rfl

omit [StorageModel GF] package_sem in
/-- ... and conversely: a certificate of the snapshot record certifies the state. -/
theorem memSnapCertOk_of_sv (γs : MemStorNames) (σ : StorState) (sv : SnapshotM)
    (h : snapId sv = σ.ss ∧ sv.Metadata'.ConfState'.lists = σ.scs ∧
      sv.Metadata'.ConfState'.AutoLeave' = σ.sal ∧ sv.Data' = σ.sdat) :
    memStorCert (GF := GF) γs (snapTrip sv sv.Metadata'.ConfState'.lists) ⊢
      memSnapCertOk γs σ := by
  have ht : snapTrip sv sv.Metadata'.ConfState'.lists = σ.trip := by
    simp only [snapTrip, StorState.trip, h.1, h.2.1, h.2.2.1, h.2.2.2]
  rw [ht]
  unfold memSnapCertOk
  iintro #H
  iright; iexact H

/-- The snapshot at home: the storage's own snapshot at some state, with half its ghost value,
and (D22 S-b′2) its certificate if it is not empty. -/
def memSnapHome (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(∃ (σp : StorState), memSnapOwn ms σp ∗ ghostVar γs.sn (1 : Qp).half (snapPart σp) ∗
    memSnapCertOk γs σp)

/-- The snapshot's invariant (D17d): at home (`w = 0`, both halves of `sw`), or out against the key
set `w` (half of `sw` here, the other half the taker's receipt). -/
def memSnapInv (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(∃ (w : Nat), ghostVar γs.sw (1 : Qp).half w ∗
    ((⌜w = 0⌝ ∗ ghostVar γs.sw (1 : Qp).half (0 : Nat) ∗ memSnapHome ms γs) ∨ memSnapKeys γs w))

/-- The namespace of the snapshots' invariants. -/
def memSnapN : Namespace := nroot.@"raft_memsnap"

/-- The owner's share of the snapshot (D17d; part of `ownMemoryStorage`; until D17d the snapshot
itself, `memSnapOwn`): the invariant and the owner's key. (Until D19i part 1 also a quarter of the
ghost value, now the lock's: the application may replace the snapshot under the lock.) -/
def memSnapShare (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(inv memSnapN (memSnapInv ms γs) ∗ memKey γs.ok)

/-- **Take the snapshot out** with the key set `k`: the snapshot at home, under a later (the next
program step strips it: the snapshot's predicates hold invariants, not timeless), and the receipt. -/
theorem memSnap_take (ms : Loc) (γs : MemStorNames) (k : Nat) (E : CoPset) (HE : ↑memSnapN ⊆ E) :
    ⊢ inv memSnapN (memSnapInv (GF := GF) ms γs) -∗ memSnapKeys γs k ={E}=∗
      ▷ memSnapHome ms γs ∗ ghostVar γs.sw (1 : Qp).half k := by
  iintro #Hinv Hk
  iinv Hinv with Hi Hclose
  iunfold memSnapInv at Hi
  icases Hi with ⟨%w, >Hw, Hi⟩
  icases Hi with (⟨>%Hw0, >Hw', Hh⟩ | >Hk')
  · subst Hw0
    imod ghostVar_update_halves k γs.sw 0 0 $$ Hw Hw' with ⟨Hw, Hw'⟩
    imod Hclose $$ [Hw Hk] with -
    · inext
      iunfold memSnapInv
      iexists k
      iframe Hw
      iright; iexact Hk
    imodintro
    iframe
  · iexfalso
    iapply memSnapKeys_excl γs k w $$ Hk Hk'

/-- **Put the snapshot back** with the receipt of the key set `k`: the keys come back. -/
theorem memSnap_put (ms : Loc) (γs : MemStorNames) (k : Nat) (σ : StorState) (E : CoPset)
    (HE : ↑memSnapN ⊆ E) :
    ⊢ inv memSnapN (memSnapInv (GF := GF) ms γs) -∗ ghostVar γs.sw (1 : Qp).half k -∗
      memSnapOwn ms σ -∗ ghostVar γs.sn (1 : Qp).half (snapPart σ) -∗ memSnapCertOk γs σ ={E}=∗
      memSnapKeys γs k := by
  iintro #Hinv Hr Hown Hsn #Hcert
  iinv Hinv with Hi Hclose
  iunfold memSnapInv at Hi
  icases Hi with ⟨%w, >Hw, Hi⟩
  icases Hi with (⟨>%Hw0, >Hw', -⟩ | >Hk)
  · subst Hw0
    icombine Hw Hw' as Hw
    icases ghostVar_valid_2 γs.sw (0 : Nat) _ k _ $$ Hw Hr with %H
    exfalso
    obtain ⟨H, -⟩ := H
    grind
  · icases ghostVar_agree γs.sw w _ k _ $$ Hw Hr with %Hwk
    subst Hwk
    imod ghostVar_update_halves (0 : Nat) γs.sw w w $$ Hw Hr with ⟨Hw, Hw'⟩
    imod Hclose $$ [Hw Hw' Hown Hsn] with -
    · inext
      iunfold memSnapInv
      iexists (0 : Nat)
      iframe Hw
      ileft
      iframe Hw'
      isplitr
      · ipureintro; rfl
      iunfold memSnapHome
      iexists σ
      iframe
      iexact Hcert
    imodintro
    iexact Hk

/-- The ghost value: the owner's and the application's quarters and home's half, all three
together, move to the snapshot `σ'` (`ApplySnapshot`, `CreateSnapshot`). -/
theorem memSnap_update (γs : MemStorNames) (a b c σ' : StorState) :
    ⊢ ghostVar (GF := GF) γs.sn memQ a -∗ ghostVar γs.sn memQ b -∗
      ghostVar γs.sn (1 : Qp).half c ==∗
      ghostVar γs.sn memQ (snapPart σ') ∗ ghostVar γs.sn memQ (snapPart σ') ∗
      ghostVar γs.sn (1 : Qp).half (snapPart σ') := by
  iintro Ha Hb Hc
  icases ghostVar_agree γs.sn a _ b _ $$ Ha Hb with %Hab
  subst Hab
  icombine Ha Hb as Hab
  imod ghostVar_update_halves (snapPart σ') γs.sn a c $$ Hab Hc with ⟨Hab, Hc⟩
  ihave Hab : ghostVar γs.sn (memQ + memQ) (snapPart σ') $$ [Hab]
  · rw [Qp.half_add_half]; iexact Hab
  icases ghostVar_split γs.sn _ memQ memQ $$ Hab with ⟨Ha, Hb⟩
  imodintro
  iframe

/-- (D19i part 1) The floor is at least `x`: some recorded history of the owner's ends at a state
whose floor is. Persistent; what the lock keeps of the application's cut and snapshot, and what
the owner reads back against its own history (`memFlLb_view`). -/
def memFlLb (γs : MemStorNames) (x : w64) : IProp GF :=
  iprop(∃ L : List StorState, monoListLbOwn γs.hist L ∗
    ⌜HistOk L ∧ ∃ w, L.getLast? = some w ∧ uint.Z x ≤ uint.Z w.fl⌝)

instance memFlLb_persistent (γs : MemStorNames) (x : w64) :
    Persistent (memFlLb (GF := GF) γs x) := by
  unfold memFlLb; infer_instance

/-- The ghost part of the lock's invariant: the contents `σp` are the last state
`done` records, at half of its authority, and every state it records is sanctioned (a prefix of
`hist`, a history: `HistOk`); and (D17d) the lock's key to the snapshot (`memSnapInv`). -/
def memInvGhost (γs : MemStorNames) (σp : StorState) : IProp GF :=
  iprop(∃ (D : List StorState),
    monoListAuthOwn γs.done (1 : Qp).half D ∗ monoListLbOwn γs.hist D ∗
    ⌜D.getLast? = some σp ∧ HistOk D⌝ ∗ memKey γs.lk)

/-- (D19i part 1) What the lock knows of the application's compaction and snapshot: the boundary
`c` the fields are cut at (half its ghost value, its index the counter `bd`), an entry of the
contents, within the floor unless it is the contents' own; the storage's snapshot `S` (a quarter
of its ghost value), at or above the boundary, and either the contents' own or one the
application took, at an entry of the contents at or below the floor. -/
def memCutInv (γs : MemStorNames) (σp : StorState) (c : entryID) : IProp GF :=
  iprop(∃ (S : StorState),
    "Hcb" ∷ ghostVar γs.cb (1 : Qp).half c ∗
    "Hbd" ∷ monoNatAuthOwn γs.bd 1 (uint.Z c.index').toNat ∗
    "#Hcfl" ∷ (⌜c = σp.prev⌝ ∨ memFlLb γs c.index') ∗
    "Hsq" ∷ ghostVar γs.sn memQ (snapPart S) ∗
    "%Hcok" ∷ ⌜CutOk σp c ∧ uint.Z c.index' ≤ uint.Z S.ss.index'⌝ ∗
    "%Hccap" ∷ ⌜uint.Z c.index' ≤ γs.cap⌝ ∗
    "#Hsrel" ∷ (⌜S.ss = σp.ss ∧ S.scs = σp.scs ∧ S.sal = σp.sal ∧ S.sdat = σp.sdat⌝ ∨
      (⌜uint.Z σp.ss.index' < uint.Z S.ss.index' ∧ uint.Z σp.prev.index' ≤ uint.Z S.ss.index' ∧
          termAt σp.prev σp.ents S.ss.index' = some S.ss.term'⌝ ∗ memFlLb γs S.ss.index')))

/-- The lock's invariant: the contents, their ghost record, the fields at them cut at the
application's boundary (D19i part 1), and their bound (2026-10-10: the contents may be ahead of
the owner's view, so the bound the private helpers need is the invariant's). -/
def memstorageInv (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(∃ (σp : StorState) (c : entryID),
  "Hgs" ∷ memInvGhost γs σp ∗
  "Hfields" ∷ memstorageFields ms (memCut σp c) ∗
  "%Hpb" ∷ ⌜uint.Z σp.prev.index' + (σp.ents.length : Int) < 2^61⌝ ∗
  "Hcut" ∷ memCutInv γs σp c)

/-- The lock's key, out of the lock's ghost state and back (D17d). -/
theorem memInvGhost_key (γs : MemStorNames) (σp : StorState) :
    ⊢ memInvGhost (GF := GF) γs σp -∗ memKey γs.lk ∗ (memKey γs.lk -∗ memInvGhost γs σp) := by
  iintro Hg
  iunfold memInvGhost at Hg
  icases Hg with ⟨%D, Hd, #Hlb, %HD, Hlk⟩
  iframe Hlk
  iintro Hlk
  iunfold memInvGhost
  iexists D
  iframe Hd Hlb Hlk
  ipureintro; exact HD

/-- **The application's snapshot token** (D17d, 2026-10-18): the application's key and a quarter
of the snapshot's ghost value, at `σ` (its snapshot part, `snapPart σ`), and (D19i part 1) half
the storage's boundary, `σ.prev`. It is `NewMemoryStorage`'s, and what `ApplySnapshot`/
`CreateSnapshot`/`Compact` (which change the snapshot or the boundary), `InitialState` (which reads
the snapshot without the lock) and the application's `Snapshot` take. -/
def memSnapTok (ms : Loc) (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  "#Hsinv" ∷ inv memSnapN (memSnapInv ms γs) ∗
  "Hak" ∷ memKey γs.ak ∗
  "Hsv" ∷ ghostVar γs.sn memQ (snapPart σ) ∗
  "Hcbt" ∷ ghostVar γs.cb (1 : Qp).half σ.prev)

/-! ### The token split for the logically atomic specs (D22 J3, 2026-10-26)

`ApplySnapshot` (raft's goroutine, etcd's `raftNode.start`) and `CreateSnapshot`/`Compact` (the
apply job) overlap in Go (`notes/j3-overlap-test/`), so the token's ghost part is shared, in an
invariant of the application's (D22 J4), and the three methods are logically atomic over it
(`MemoryStorage.<M>.spec`): `memSnapTok = memSnapRO ∗ memKey γs.ak ∗ memSnapTokG`
(`memSnapTok_split`). The application's key `ak` is not in the shared part: `CreateSnapshot` takes
the snapshot out of `memSnapInv` with it (`memSnapKeys` 2) for the whole critical section, which a
logically atomic access (one instant) cannot lend; only the apply job calls `CreateSnapshot`, so
it keeps the key (decision in `notes/decisions.md`, "D22 J3"). -/

/-- The token's persistent part (D22 J3): the package, the storage's lock, the snapshot's
invariant. -/
def memSnapRO (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
    sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
    inv memSnapN (memSnapInv ms γs))

instance memSnapRO_persistent (ms : Loc) (γs : MemStorNames) :
    Persistent (memSnapRO (GF := GF) ms γs) := by
  unfold memSnapRO; infer_instance

/-- The token's shared ghost part (D22 J3): a quarter of the snapshot's ghost value (its part of
`σ`, `snapPart σ`) and half of the boundary's, `σ.prev`. What the logically atomic
`ApplySnapshot`/`CreateSnapshot`/`Compact` change, at their linearization points. -/
def memSnapTokG (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(ghostVar γs.sn memQ (snapPart σ) ∗ ghostVar γs.cb (1 : Qp).half σ.prev)

instance memSnapTokG_timeless (γs : MemStorNames) (σ : StorState) :
    Timeless (memSnapTokG (GF := GF) γs σ) := by
  unfold memSnapTokG; infer_instance

omit [StorageModel GF] package_sem in
/-- The ghost part reads only the snapshot's part and the boundary. -/
theorem memSnapTokG_congr (γs : MemStorNames) (σ σ' : StorState) (h1 : snapPart σ' = snapPart σ)
    (h2 : σ'.prev = σ.prev) :
    memSnapTokG (GF := GF) γs σ ⊢ memSnapTokG γs σ' := by
  unfold memSnapTokG
  rw [h1, h2]

/-- (D22 J3) `CreateSnapshot`'s `cs` argument: `nil` (`oc = none`, the previous `ConfState` kept)
or a `ConfState` at any fraction. Named so that its precondition and its postcondition mention the
same term (two `match`es elaborate to two auxiliary functions, which the proof mode does not
unify). -/
def memCsArg (cs : Loc) (dq : DFrac) (oc : Option ConfStateM) : IProp GF :=
  match oc with
  | none => iprop(⌜cs = null⌝)
  | some c => ownCSM cs dq c

/-- **The token split** (D22 J3). -/
theorem memSnapTok_split (ms : Loc) (γs : MemStorNames) (σ : StorState) :
    memSnapTok (GF := GF) ms γs σ ⊣⊢ memSnapRO ms γs ∗ memKey γs.ak ∗ memSnapTokG γs σ := by
  unfold memSnapTok memSnapRO memSnapTokG
  simp only [named]
  constructor
  · iintro ⟨#H1, #H2, #H3, H4, H5, H6⟩
    iframe H4 H5 H6
    isplitl []; · iexact H1
    isplitl []; · iexact H2
    iexact H3
  · iintro ⟨⟨#H1, #H2, #H3⟩, H4, H5, H6⟩
    iframe H4 H5 H6
    isplitl []; · iexact H1
    isplitl []; · iexact H2
    iexact H3

/-- The owner's ghost view at `σ` (2026-10-10; D19i part 1): the history `hist` it has
sanctioned (`HistOk`), and either nothing pending -- all of `hist`'s authority, ending at `σ`, the
writer's half of `done` at a prefix `D` of it that only lacks floor raises, and all of `ep` -- or a
batch pending -- half of `hist`'s authority (the token has the other), ending at the appended
state, a lower bound of `done` at the hand-out's `D`, and half of `ep`. -/
def memView (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(∃ (hist : List StorState),
    ⌜HistOk hist⌝ ∗
    ((monoListAuthOwn γs.hist 1 hist ∗ ⌜σ.pend = [] ∧ hist.getLast? = some σ⌝ ∗
        (∃ (D : List StorState), monoListAuthOwn γs.done (1 : Qp).half D ∗
          ⌜D <+: hist ∧ D ≠ [] ∧ RaiseOnly D (hist.drop D.length)⌝) ∗
        ∃ (v : StorState × List StorState × List StorState), ghostVar γs.ep 1 v) ∨
     (monoListAuthOwn γs.hist (1 : Qp).half hist ∗
      ∃ (H D : List StorState),
        ⌜σ.pend ≠ [] ∧ hist = H ++ [storAbsorb σ] ∧
          H.getLast? = some { σ with pend := [] } ∧ PendAbove σ σ.pend ∧
          D <+: H ∧ D ≠ [] ∧ RaiseOnly D (H.drop D.length) ∧ PendOk σ σ.pend⌝ ∗
        monoListLbOwn γs.done D ∗ ghostVar γs.ep (1 : Qp).half (σ, H, D))))

/-- A `MemoryStorage` at `ms` with the ghost names `γs`, whose owner sees it at `σ`.
Indexed by its names (2026-10-10), so that a token (`memAppendTok`, `memAppendedTok`)
is of this storage. Until 2026-10-10 it also asked `σ.ss.index' ≠ 0` (`isStorage`'s
`Snapshot` promises a non-empty snapshot); a new storage has none
(`NewMemoryStorage`), so the instance (`MemstorageInstance.lean`) adds it instead. Since the
v3.7 retarget (stage R3) it owns the storage's snapshot (`memSnapOwn`); since D17d its key to it.
(D19i part 1) `σ` is the owner's view, its floor `σ.fl` the one the owner has published. -/
def ownMemoryStorage (ms : Loc) (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  "Hview" ∷ memView γs σ ∗
  "Hsn" ∷ memSnapShare ms γs ∗
  "%Hbounded" ∷ ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝)

/-- The rest of a `MemoryStorage` (2026-10-12): its hard state `hs`, which `InitialState`
reads without the lock, and the `initialState` counter it increments without it. The other half
of `hardState` is the lock's (`memstorageFields`), so `SetHardState`, which writes it under the
lock, needs this. Separate from `ownMemoryStorage`, which the storage's owner (raft, through
`isStorage`) holds: the application keeps this one, and `SetHardState` (which `Ready` handling
calls while raft runs) needs nothing else. Since the v3.7 retarget (stage R3) the field holds a
pointer, `nil` or to a read-only hard state (`hsOpt`), and the snapshot is `ownMemoryStorage`'s
(until then this held half of the snapshot value). -/
def memStorMeta (ms : Loc) (γs : MemStorNames) (hs : HardStateM) : IProp GF :=
  iprop(∃ (n : w64) (hp : Loc),
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  "HhardState" ∷ ms.[MemoryStorage, go!"hardState"] ↦{DFrac.own (1 : Qp).half} hp ∗
  "#Hhs" ∷ hsOpt hp hs ∗
  "Hcs_initialState" ∷
    (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"initialState"] ↦ n)

/-- The application's right to append `p` to the storage at `σ` (2026-10-10; D19i part 1): the
writer's half of `done` at the hand-out's `D`, half of `hist`'s authority past the appended
state, and `ep`'s other half. -/
def memAppendTok (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) :
    IProp GF :=
  iprop(
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  ∃ (H D : List StorState),
  "Hdone" ∷ monoListAuthOwn γs.done (1 : Qp).half D ∗
  "Hhist" ∷ monoListAuthOwn γs.hist (1 : Qp).half (H ++ [storAbsorb { σ with pend := p }]) ∗
  "Hep" ∷ ghostVar γs.ep (1 : Qp).half ({ σ with pend := p }, H, D) ∗
  "%Htok" ∷ ⌜H.getLast? = some σ ∧ σ.pend = [] ∧ PendOk σ p ∧ PendAbove σ p ∧
    D <+: H ∧ D ≠ [] ∧ RaiseOnly D (H.drop D.length) ∧
    HistOk (H ++ [storAbsorb { σ with pend := p }])⌝)

/-- The receipt: the writer's half of `done` and half of `hist`, both past the appended state,
`ep`'s half, and the appended state's bound (`Append`'s premise). -/
def memAppendedTok (_ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) :
    IProp GF :=
  iprop(∃ (H D : List StorState),
  "Hdone" ∷ monoListAuthOwn γs.done (1 : Qp).half (H ++ [storAbsorb { σ with pend := p }]) ∗
  "Hhist" ∷ monoListAuthOwn γs.hist (1 : Qp).half (H ++ [storAbsorb { σ with pend := p }]) ∗
  "Hep" ∷ ghostVar γs.ep (1 : Qp).half ({ σ with pend := p }, H, D) ∗
  "%Hbnd" ∷ ⌜uint.Z σ.prev.index' + ((storApp σ p).length : Int) < 2^61⌝)

/-- (D19i part 1) **The floor's witness** for the application (`isStorageWith`'s `FW`): the floor
the owner published is at least `x` (`memFlLb`), and the storage then held entries up to `x`,
which it keeps (the history from `done`'s `D` on only raised the floor). What `Compact` and
`CreateSnapshot` take. -/
def memFloorTok (ms : Loc) (γs : MemStorNames) (x : w64) : IProp GF :=
  iprop(
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  ∃ (D L : List StorState),
    "#Hdlb" ∷ monoListLbOwn γs.done D ∗
    "#Hhlb" ∷ monoListLbOwn γs.hist L ∗
    "%Hfw" ∷ ⌜D <+: L ∧ D ≠ [] ∧ RaiseOnly D (L.drop D.length) ∧ HistOk L ∧
      ∃ w, L.getLast? = some w ∧ uint.Z x ≤ uint.Z w.fl⌝)

instance memFloorTok_persistent (ms : Loc) (γs : MemStorNames) (x : w64) :
    Persistent (memFloorTok (GF := GF) ms γs x) := by
  unfold memFloorTok; infer_instance

theorem memFloorTok_flLb (ms : Loc) (γs : MemStorNames) (x : w64) :
    memFloorTok (GF := GF) ms γs x ⊢ memFlLb γs x := by
  iintro H
  iunfold memFloorTok at H
  icases H with ⟨-, -, %D, %L, -, #Hhlb, %Hfw⟩
  iunfold memFlLb
  iexists L
  iframe Hhlb
  ipureintro
  exact ⟨Hfw.2.2.2.1, Hfw.2.2.2.2⟩

theorem memFlLb_le (γs : MemStorNames) (x y : w64) (h : uint.Z y ≤ uint.Z x) :
    memFlLb (GF := GF) γs x ⊢ memFlLb γs y := by
  iintro H
  iunfold memFlLb at H
  iunfold memFlLb
  icases H with ⟨%L, #Hl, %HL⟩
  iexists L
  iframe Hl
  ipureintro
  obtain ⟨Hok, w, hw, hx⟩ := HL
  exact ⟨Hok, w, hw, Int.le_trans h hx⟩

theorem monoAuth_agree_keep (γ : GName) (q1 q2 : Qp) (l1 l2 : List StorState) :
    (monoListAuthOwn γ q1 l1 ∗ monoListAuthOwn γ q2 l2 : IProp GF) ⊢
      (monoListAuthOwn γ q1 l1 ∗ monoListAuthOwn γ q2 l2) ∗ ⌜l1 = l2⌝ :=
  persistent_entails_left (by
    iintro ⟨H1, H2⟩
    icases monoListAuthOwn_agree γ q1 q2 l1 l2 $$ H1 H2 with %H
    ipureintro; exact H.2)

theorem monoAuthLb_keep (γ : GName) (q : Qp) (l1 l2 : List StorState) :
    (monoListAuthOwn γ q l1 ∗ monoListLbOwn γ l2 : IProp GF) ⊢
      (monoListAuthOwn γ q l1 ∗ monoListLbOwn γ l2) ∗ ⌜l2 <+: l1⌝ :=
  persistent_entails_left (by
    iintro ⟨H1, H2⟩
    icases mono_list_auth_lb_valid γ q l1 l2 $$ H1 H2 with %H
    ipureintro; exact H.2)

/-- A whole `mono_list` authority is two halves. -/
theorem monoAuth_halves (γ : GName) (l : List StorState) :
    (monoListAuthOwn γ 1 l : IProp GF) ⊣⊢
      monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (monoListAuthOwn_fractional γ l).fractional _ _

/-- The two halves of a `mono_list` authority (`done`: the invariant's and the writer's;
`hist`: the owner's and the token's, D19i part 1) together move to a longer list. -/
theorem monoHalves_update (γ : GName) (H H' : List StorState) (h : H <+: H') :
    ⊢ monoListAuthOwn (GF := GF) γ (1 : Qp).half H -∗
      monoListAuthOwn γ (1 : Qp).half H ==∗
      monoListAuthOwn γ (1 : Qp).half H' ∗ monoListAuthOwn γ (1 : Qp).half H' := by
  iintro H1 H2
  ihave Hf := (monoAuth_halves γ H).2 $$ [H1 H2]
  · iframe H1 H2
  imod monoListAuthOwn_update H' h $$ Hf with ⟨Hf, -⟩
  icases (monoAuth_halves γ H').1 $$ Hf with ⟨H1, H2⟩
  imodintro
  iframe H1 H2

/-- The contents the lock holds have the data of `D`'s last whenever `done` is between `D` and a
history that only raised the floor after it. -/
theorem raiseOnly_between {D Dc L : List StorState} {a b : StorState} (h1 : D <+: Dc)
    (h2 : Dc <+: L) (hR : RaiseOnly D (L.drop D.length)) (ha : D.getLast? = some a)
    (hb : Dc.getLast? = some b) : DataEq b a := by
  have hR' : RaiseOnly D (Dc.drop D.length) := by
    intro w hw
    apply hR w
    obtain ⟨T, rfl⟩ := h2
    rw [List.drop_append_of_le_length h1.length_le]
    exact List.mem_append_left _ hw
  exact RaiseOnly.last h1 hR' ha hb

/-- The owner, with nothing pending, moves the storage to a new state `σ'` (nothing pending, its
floor at least the owner's, which it holds) under the lock (2026-10-12; since D19i part 1 only
`ApplySnapshot`): the contents are the owner's state's data, and `hist` and `done` (both halves:
the owner's writer half and the invariant's) record `σ'`. -/
theorem memView_set (γs : MemStorNames) (σ σp σ' : StorState) (Hidle : σ.pend = [])
    (H' : σ'.pend = []) (Hfl : uint.Z σ.fl ≤ uint.Z σ'.fl) (Hfl' : uint.Z σ'.fl ≤ stLast σ')
    (Hidx' : PlogWf σ'.prev σ'.ents) :
    ⊢ memView (GF := GF) γs σ -∗ memInvGhost γs σp ==∗
      ⌜DataEq σp σ⌝ ∗ memView γs σ' ∗ memInvGhost γs σ' := by
  iintro Hv Hg
  unfold memView memInvGhost
  icases Hv with ⟨%hist, %Hok, Hv⟩
  icases Hg with ⟨%Dc, Hd, #Hlbc, %HD, Hlk⟩
  icases Hv with (⟨Hh, %Hid, ⟨%D, Hw, %HDh⟩, %v, Hep⟩ | ⟨Hh, %H, %D, %Hpd, -, -⟩)
  rotate_left
  · exact absurd Hidle Hpd.1
  icases monoAuth_agree_keep γs.done _ _ D Dc $$ [$Hw $Hd] with ⟨⟨Hw, Hd⟩, %Heq⟩
  subst Heq
  obtain ⟨Hpre, Hne, HR⟩ := HDh
  obtain ⟨a, ha⟩ : ∃ a, D.getLast? = some a := by
    cases hD : D.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hD; exact absurd hD Hne
    | some a => exact ⟨a, rfl⟩
  have Hσp : DataEq σp σ := by
    rw [HD.1] at ha
    cases ha
    exact (RaiseOnly.last Hpre HR HD.1 Hid.2).symm
  imod monoHalves_update γs.done D (hist ++ [σ']) (Hpre.trans (List.prefix_append _ _))
    $$ Hw Hd with ⟨Hw, Hd⟩
  imod monoListAuthOwn_update_app [σ'] $$ Hh with ⟨Hh, #Hlbh⟩
  have Hok' : HistOk (hist ++ [σ']) :=
    Hok.snoc (fun w hw => by rw [Hid.2] at hw; cases hw; exact Hfl) Hfl' H' Hidx'
  imodintro
  isplitr
  · ipureintro; exact Hσp
  isplitl [Hh Hw Hep]
  · iexists hist ++ [σ']
    isplitr
    · ipureintro; exact Hok'
    ileft
    iframe Hh
    isplitr
    · ipureintro; exact ⟨H', by simp⟩
    isplitl [Hw]
    · iexists hist ++ [σ']
      iframe Hw
      ipureintro
      refine ⟨List.prefix_refl _, by simp, ?_⟩
      rw [List.drop_length]; exact RaiseOnly.nil _
    iexists v
    iexact Hep
  iexists hist ++ [σ']
  iframe Hd Hlbh Hlk
  ipureintro; exact ⟨by simp, Hok'⟩

/-- Raft's view and the lock's ghost state agree (`MemView`), without consuming
either. -/
theorem memView_agree (γs : MemStorNames) (σ σp : StorState) :
    ⊢ memView (GF := GF) γs σ -∗ memInvGhost γs σp -∗
      ⌜MemView σ σp⌝ ∗ memView γs σ ∗ memInvGhost γs σp := by
  iintro Hv Hg
  unfold memView memInvGhost
  icases Hv with ⟨%hist, %Hok, Hv⟩
  icases Hg with ⟨%Dc, Hd, #Hlb, %HD, Hlk⟩
  icases Hv with (⟨Hh, %Hidle, ⟨%D, Hw, %HDh⟩, Hep⟩ | ⟨Hh, %H, %D, %Hpd, #HlbD, Hep⟩)
  · icases monoAuth_agree_keep γs.done _ _ D Dc $$ [$Hw $Hd] with ⟨⟨Hw, Hd⟩, %Heq⟩
    subst Heq
    obtain ⟨Hpre, Hne, HR⟩ := HDh
    have Hd := RaiseOnly.last Hpre HR HD.1 Hidle.2
    isplitr
    · ipureintro
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := Hd
      exact ⟨h1.symm, ⟨h3.symm, h4.symm, h5.symm, h7.symm⟩, .inl h2.symm, fun _ => h2.symm⟩
    isplitl [Hh Hw Hep]
    · iexists hist
      isplitr
      · ipureintro; exact Hok
      ileft
      iframe Hh Hep
      isplitr
      · ipureintro; exact Hidle
      iexists D
      iframe Hw
      ipureintro; exact ⟨Hpre, Hne, HR⟩
    iexists D
    iframe Hd Hlb Hlk
    ipureintro; exact HD
  · icases monoAuthLb_keep γs.done _ Dc D $$ [$Hd $HlbD] with ⟨⟨Hd, -⟩, %H1⟩
    icases monoAuthLb_keep γs.hist _ hist Dc $$ [$Hh $Hlb] with ⟨⟨Hh, -⟩, %H2⟩
    obtain ⟨Hne, rfl, Hlast, Hab, HDH, HDne, HR, Hpo⟩ := Hpd
    isplitr
    · ipureintro
      -- `Dc` is between `D` and `H ++ [_]`: within `H` (raises only), or all of it
      have HHd : DataEq { σ with pend := [] } σp ∨ σp = storAbsorb σ := by
        by_cases hlen : Dc.length ≤ H.length
        · left
          have H2' : Dc <+: H := by
            rw [List.prefix_iff_eq_take] at H2
            rw [H2, List.take_append_of_le_length hlen]
            exact List.take_prefix _ _
          obtain ⟨a, ha⟩ : ∃ a, D.getLast? = some a := by
            cases hD : D.getLast? with
            | none => rw [List.getLast?_eq_none_iff] at hD; exact absurd hD HDne
            | some a => exact ⟨a, rfl⟩
          have h1 := raiseOnly_between H1 H2' HR ha HD.1
          have h2 := RaiseOnly.last HDH HR ha Hlast
          exact h2.trans h1.symm
        · right
          have : Dc = H ++ [storAbsorb σ] := by
            obtain ⟨T, hT⟩ := H2
            have hl := congrArg List.length hT
            simp only [List.length_append, List.length_singleton] at hl
            have hT0 : T = [] := by
              apply List.eq_nil_of_length_eq_zero; omega
            subst hT0
            simpa using hT
          subst this
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at HD
          exact (Option.some.inj HD.1).symm
      rcases HHd with h | h
      · obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := h
        exact ⟨h1.symm, ⟨h3.symm, h4.symm, h5.symm, h7.symm⟩, .inl h2.symm, fun hp => absurd hp Hne⟩
      · subst h
        exact ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, .inr ⟨Hne, rfl⟩, fun hp => absurd hp Hne⟩
    isplitl [Hh Hep]
    · iexists H ++ [storAbsorb σ]
      isplitr
      · ipureintro; exact Hok
      iright
      iframe Hh
      iexists H, D
      iframe HlbD Hep
      ipureintro; exact ⟨Hne, rfl, Hlast, Hab, HDH, HDne, HR, Hpo⟩
    iexists Dc
    iframe Hd Hlb Hlk
    ipureintro; exact HD

/-- (D19i part 1) What the owner's view says of a pending batch: it starts above the floor, within
the view's entries (`PendAbove`, `PendOk`). -/
theorem memView_pend (γs : MemStorNames) (σ : StorState) :
    ⊢ memView (GF := GF) γs σ -∗
      ⌜PendAbove σ σ.pend ∧ (σ.pend ≠ [] → PendOk σ σ.pend)⌝ ∗ memView γs σ := by
  iintro Hv
  unfold memView
  icases Hv with ⟨%hist, %Hok, Hv⟩
  icases Hv with (⟨Hh, %Hidle, HD, Hep⟩ | ⟨Hh, %H, %D, %Hpd, #HlbD, Hep⟩)
  · isplitr
    · ipureintro
      refine ⟨fun e0 he => (by rw [Hidle.1] at he; cases he), fun h => absurd Hidle.1 h⟩
    iexists hist
    isplitr
    · ipureintro; exact Hok
    ileft
    iframe Hh HD Hep
    ipureintro; exact Hidle
  · isplitr
    · ipureintro; exact ⟨Hpd.2.2.2.1, fun _ => Hpd.2.2.2.2.2.2.2⟩
    iexists hist
    isplitr
    · ipureintro; exact Hok
    iright
    iframe Hh
    iexists H, D
    iframe HlbD Hep
    ipureintro; exact Hpd

/-- (D19i part 1) An entry of the contents at or below the floor is the view's: below a pending
batch, which starts above the floor, the contents agree with the view. -/
theorem memView_termAt_below (σ σ0 : StorState) (H : MemView σ σ0) (Hab : PendAbove σ σ.pend)
    (Hpo : σ.pend ≠ [] → PendOk σ σ.pend) (i t : w64)
    (Ht : termAt σ0.prev σ0.ents i = some t) (Hi : uint.Z i ≤ uint.Z σ.fl)
    (Hge : uint.Z σ.prev.index' ≤ uint.Z i) :
    termAt σ.prev σ.ents i = some t := by
  obtain ⟨Hp, -, He, -⟩ := H
  rw [Hp] at Ht
  rcases He with He | ⟨Hne, He⟩
  · rw [He] at Ht; exact Ht
  rw [He] at Ht
  obtain ⟨-, Hh0⟩ := Hpo Hne
  cases hp : σ.pend with
  | nil => exact absurd hp Hne
  | cons e0 rest =>
    have h1 := Hab e0 (by rw [hp]; rfl)
    have h2 := (Hh0 e0 (by rw [hp]; rfl)).2
    rw [hp] at Ht
    unfold termAt at Ht ⊢
    split
    · rename_i hc; rw [if_pos hc] at Ht; exact Ht
    · rename_i hc
      rw [if_neg hc] at Ht
      simp only [storApp] at Ht
      by_cases hk : (uint.Z i - uint.Z σ.prev.index' - 1).toNat <
          (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat
      · rw [List.getElem?_append_left (by rw [List.length_take]; omega),
          List.getElem?_take_of_lt hk] at Ht
        exact Ht
      · exfalso; omega

/-- (D19i part 1) The owner reads a floor witness against its own history: the published floor,
`σ.fl`, is at least it. -/
theorem memFlLb_view (γs : MemStorNames) (σ : StorState) (x : w64) :
    ⊢ memView (GF := GF) γs σ -∗ memFlLb γs x -∗ ⌜uint.Z x ≤ uint.Z σ.fl⌝ ∗ memView γs σ := by
  iintro Hv #Hx
  iunfold memFlLb at Hx
  icases Hx with ⟨%L, #HL, %HLok⟩
  obtain ⟨-, w, hw, hx⟩ := HLok
  unfold memView
  icases Hv with ⟨%hist, %Hok, Hv⟩
  icases Hv with (⟨Hh, %Hidle, HD, Hep⟩ | ⟨Hh, %H, %D, %Hpd, #HlbD, Hep⟩)
  · icases monoAuthLb_keep γs.hist _ hist L $$ [$Hh $HL] with ⟨⟨Hh, -⟩, %Hpre⟩
    isplitr
    · ipureintro
      have := Hok.last_mono Hpre hw Hidle.2
      omega
    iexists hist
    isplitr
    · ipureintro; exact Hok
    ileft
    iframe Hh HD Hep
    ipureintro; exact Hidle
  · icases monoAuthLb_keep γs.hist _ hist L $$ [$Hh $HL] with ⟨⟨Hh, -⟩, %Hpre⟩
    isplitr
    · ipureintro
      obtain ⟨-, rfl, -, -⟩ := Hpd
      have := Hok.last_mono Hpre hw
        (show (H ++ [storAbsorb σ]).getLast? = some (storAbsorb σ) by simp)
      simp only [storAbsorb] at this
      omega
    iexists hist
    isplitr
    · ipureintro; exact Hok
    iright
    iframe Hh
    iexists H, D
    iframe HlbD Hep
    ipureintro; exact Hpd

/-- (D19i part 1) The lock holds the entries up to a floor witness's `x`: the history only raised
the floor since the witness's `D`, or the contents are past the witness, at a floor at least
`x`, which every state holds. -/
theorem memFloorTok_last (ms : Loc) (γs : MemStorNames) (σp : StorState) (x : w64) :
    ⊢ memFloorTok (GF := GF) ms γs x -∗ memInvGhost γs σp -∗
      ⌜uint.Z x ≤ stLast σp⌝ ∗ memInvGhost γs σp := by
  iintro #Hfw Hg
  iunfold memFloorTok at Hfw
  icases Hfw with ⟨-, -, %D, %L, #Hdlb, #Hhlb, %Hf⟩
  obtain ⟨HDL, HDne, HR, HLok, w, hw, hx⟩ := Hf
  unfold memInvGhost
  icases Hg with ⟨%Dc, Hd, #Hlb, %HD, Hlk⟩
  icases monoAuthLb_keep γs.done _ Dc D $$ [$Hd $Hdlb] with ⟨⟨Hd, -⟩, %H1⟩
  icases mono_list_lb_valid γs.hist L Dc $$ Hhlb Hlb with %H2
  isplitr
  · ipureintro
    have Hwl := (HLok.2 w (List.mem_of_getLast? hw)).1
    rcases H2 with H2 | H2
    · -- past the witness: its floor
      have := HD.2.last_mono H2 hw HD.1
      have := (HD.2.2 σp (List.mem_of_getLast? HD.1)).1
      omega
    · -- between `D` and the witness: raises only, the witness's data
      obtain ⟨a, ha⟩ : ∃ a, D.getLast? = some a := by
        cases hD : D.getLast? with
        | none => rw [List.getLast?_eq_none_iff] at hD; exact absurd hD HDne
        | some a => exact ⟨a, rfl⟩
      have h1 := raiseOnly_between H1 H2 HR ha HD.1
      have h2 := RaiseOnly.last HDL HR ha hw
      rw [h1.stLast, ← h2.stLast]
      omega
  iexists Dc
  iframe Hd Hlb Hlk
  ipureintro; exact HD

/-- (D19i part 1) The storage's boundary has reached `n` (`storCut` of the instance): a lower
bound of the lock's counter `bd`. -/
def memStorCut (γs : MemStorNames) (n : Int) : IProp GF :=
  iprop(monoNatLbOwn γs.bd n.toNat ∗ ⌜n ≤ γs.cap⌝)

instance memStorCut_persistent (γs : MemStorNames) (n : Int) :
    Persistent (memStorCut (GF := GF) γs n) := by
  unfold memStorCut; infer_instance

/-- (D19i part 1) What the owner, reading under the lock, knows of the contents and their cut:
the contents agree with its view (`MemView`), the cut is an entry of them, its own boundary or
within the published floor, and the storage is compacted up to it (`memStorCut`). -/
theorem memCut_view (γs : MemStorNames) (σ σ0 : StorState) (c : entryID) :
    ⊢ memView (GF := GF) γs σ -∗ memInvGhost γs σ0 -∗ memCutInv γs σ0 c -∗
      ⌜MemView σ σ0 ∧ CutOk σ0 c ∧ (c = σ0.prev ∨ uint.Z c.index' ≤ uint.Z σ.fl)⌝ ∗
      memStorCut γs (uint.Z c.index') ∗
      memView γs σ ∗ memInvGhost γs σ0 ∗ memCutInv γs σ0 c := by
  iintro Hv Hg Hc
  icases memView_agree γs σ σ0 $$ Hv Hg with ⟨%Hvw, Hv, Hg⟩
  iunfold memCutInv at Hc
  iNamed Hc
  ihave #Hlb := monoNatLbOwn_get γs.bd _ _ $$ Hbd
  ihave %Hfl : ⌜c = σ0.prev ∨ uint.Z c.index' ≤ uint.Z σ.fl⌝ $$ [Hv]
  · icases Hcfl with (%Hc | #Hc)
    · ipureintro; left; exact Hc
    · icases memFlLb_view γs σ c.index' $$ Hv Hc with ⟨%H, -⟩
      ipureintro; right; exact H
  isplitr
  · ipureintro; exact ⟨Hvw, Hcok.1, Hfl⟩
  isplitr
  · iunfold memStorCut; iframe Hlb; ipureintro; exact Hccap
  iframe Hv Hg
  iunfold memCutInv
  iexists S
  iframe Hcb Hbd Hcfl Hsq Hsrel
  ipureintro; exact ⟨Hcok, Hccap⟩

/-- (D21 M3) A cut fact below a smaller index. -/
theorem memStorCut_mono (γs : MemStorNames) (n m : Int) (h : m ≤ n) (h0 : 0 ≤ m) :
    ⊢ memStorCut (GF := GF) γs n -∗ memStorCut γs m := by
  iintro H
  iunfold memStorCut at H
  icases H with ⟨#Hlb, %Hc⟩
  iunfold memStorCut
  isplitr
  · iapply monoNatLbOwn_le (GF := GF) m.toNat (by omega) $$ Hlb
  · ipureintro; omega

omit [StorageModel GF] package_sem in
/-- (D21 M3) A cut fact is within the cap. -/
theorem memStorCut_cap (γs : MemStorNames) (n : Int) :
    ⊢ memStorCut (GF := GF) γs n -∗ ⌜n ≤ γs.cap⌝ := by
  iintro H
  iunfold memStorCut at H
  icases H with ⟨-, %Hc⟩; ipureintro; exact Hc

/-- The package initializer, read out of `ownMemoryStorage` without consuming it: the
methods take the lock, which needs `isPkgInit sync`; `isStorage`'s method triples have
no such premise. -/
theorem ownMemoryStorage_init (ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownMemoryStorage ms γs σ := by
  iintro H
  iunfold ownMemoryStorage at H
  iNamed H
  isplitr
  · iexact Hinit
  unfold ownMemoryStorage
  simp only [named]
  iframe Hinit Hmu Hview Hsn
  ipureintro; exact Hbounded

theorem ownMemoryStorage_bounded (ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ -∗
      ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝ ∗
      ownMemoryStorage ms γs σ := by
  iintro H
  iunfold ownMemoryStorage at H
  iNamed H
  isplitr
  · ipureintro; exact Hbounded
  unfold ownMemoryStorage
  simp only [named]
  iframe Hinit Hmu Hview Hsn
  ipureintro; exact Hbounded

/-- The hand-out law for a `MemoryStorage` (`isStorageWith`'s `Hhandout`): `hist` grows by the
appended state and its authority splits with the token (D19i part 1), the writer's half of `done`
and half of `ep` (at the new hand-out) go to the token. No lock: the invariant only holds a lower
bound of `hist`. -/
theorem memStorage_handout (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (p : List EntryM) (Hpo : σ.pend = [] ∧ PendOk σ p ∧ PendAbove σ p) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ ==∗
      ownMemoryStorage ms γs { σ with pend := p } ∗ memAppendTok ms γs σ p := by
  iintro Hown
  iunfold ownMemoryStorage at Hown
  iNamed Hown
  unfold memView
  icases Hview with ⟨%hist, %Hok, Hv⟩
  icases Hv with (⟨Hh, %Hidle, ⟨%D, Hw, %HDh⟩, %v, Hep⟩ | ⟨-, %H, %D, %Hpd, -, -⟩)
  rotate_left
  · exact absurd Hpo.1 Hpd.1
  ihave #HlbD := monoListLbOwn_get γs.done _ D $$ Hw
  have Hσ : ({ { σ with pend := p } with pend := [] } : StorState) = σ := by
    rw [← Hpo.1]
  have Hok' : HistOk (hist ++ [storAbsorb { σ with pend := p }]) := by
    refine Hok.snoc (fun w hw => by rw [Hidle.2] at hw; cases hw; exact Int.le_refl _) ?_ rfl ?_
    rotate_left
    · exact PlogWf_storApp σ p (Hok.2 σ (List.mem_of_getLast? Hidle.2)).2.2 Hpo.2.1.2
    obtain ⟨Hne, Hh0⟩ := Hpo.2.1
    cases hp : p with
    | nil => exact absurd hp Hne
    | cons e0 rest =>
      have H1 := Hpo.2.2 e0 (by rw [hp]; rfl)
      have H2 := Hh0 e0 (by rw [hp]; rfl)
      simp only [EtcdGrove.stLast, storAbsorb, storApp, List.length_append, List.length_take,
        List.length_cons]
      omega
  imod monoListAuthOwn_update_app [storAbsorb { σ with pend := p }] $$ Hh with ⟨Hh, -⟩
  icases (monoAuth_halves γs.hist _).1 $$ Hh with ⟨Hh1, Hh2⟩
  imod ghostVar_update ({ σ with pend := p }, hist, D) γs.ep v $$ Hep with Hep
  icases ghostVar_split γs.ep _ (1 : Qp).half (1 : Qp).half $$ [Hep] with ⟨Hep1, Hep2⟩
  · rw [Qp.half_add_half]; iexact Hep
  imodintro
  isplitl [Hh1 Hep1 Hsn]
  · unfold ownMemoryStorage memView
    simp only [named]
    iframe Hinit Hmu Hsn
    isplitl [Hh1 Hep1]
    · iexists hist ++ [storAbsorb { σ with pend := p }]
      isplitr
      · ipureintro; exact Hok'
      iright
      iframe Hh1
      iexists hist, D
      iframe HlbD Hep1
      ipureintro
      refine ⟨Hpo.2.1.1, rfl, by rw [Hσ]; exact Hidle.2, Hpo.2.2, HDh.1, HDh.2.1, HDh.2.2, ?_⟩
      obtain ⟨Hne, Hh0⟩ := Hpo.2.1
      exact ⟨Hne, fun e0 he => by simpa using Hh0 e0 he⟩
    ipureintro; exact Hbounded
  unfold memAppendTok
  simp only [named]
  iframe Hinit Hmu
  iexists hist, D
  iframe Hw Hh2 Hep2
  ipureintro
  exact ⟨Hidle.2, Hpo.1, Hpo.2.1, Hpo.2.2, HDh.1, HDh.2.1, HDh.2.2, Hok'⟩

/-- The absorb law for a `MemoryStorage` (`isStorageWith`'s `Habsorb`): the receipt's
half of `ep` agrees with the owner's (so it is of this hand-out), and its halves of `done` and
`hist` come back: `hist`'s authority is whole again, the writer's half of `done` at it. -/
theorem memStorage_absorb (ms : Loc) (γs : MemStorNames) (σ1 σ : StorState)
    (p : List EntryM) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ1 -∗ memAppendedTok ms γs σ p ==∗
      ⌜σ1 = { σ with pend := p }⌝ ∗ ownMemoryStorage ms γs (storAbsorb σ1) := by
  iintro Hown Ht
  iunfold ownMemoryStorage at Hown
  iNamed Hown
  iunfold memAppendedTok at Ht
  icases Ht with ⟨%Ht, %Dt, Hdone, Hhist, Hept, %Hbnd⟩
  unfold memView
  icases Hview with ⟨%hist, %Hok, Hv⟩
  icases Hv with (⟨-, -, -, %v, Hep⟩ | ⟨Hh, %H, %D, %Hpd, -, Hep⟩)
  · -- idle: the owner holds all of `ep`, so there is no receipt
    icases ghostVar_valid_2 γs.ep _ _ _ _ $$ Hep Hept with %Hq
    obtain ⟨Hq, -⟩ := Hq
    exfalso
    grind
  icases ghostVar_agree γs.ep _ _ _ _ $$ Hep Hept with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨Hσ1, rfl, rfl⟩ := Heq
  obtain ⟨Hne, rfl, Hlast, -, -, -, -, -⟩ := Hpd
  icombine Hep Hept as Hep
  subst Hσ1
  imodintro
  isplitr
  · ipureintro; rfl
  unfold ownMemoryStorage memView
  simp only [named]
  iframe Hinit Hmu Hsn
  isplitl [Hh Hhist Hdone Hep]
  · iexists H ++ [storAbsorb { σ with pend := p }]
    isplitr
    · ipureintro; exact Hok
    ileft
    isplitl [Hh Hhist]
    · iapply (monoAuth_halves γs.hist _).2
      iframe Hh Hhist
    isplitr
    · ipureintro; exact ⟨rfl, by simp⟩
    isplitl [Hdone]
    · iexists H ++ [storAbsorb { σ with pend := p }]
      iframe Hdone
      ipureintro
      refine ⟨List.prefix_refl _, by simp, ?_⟩
      rw [List.drop_length]; exact RaiseOnly.nil _
    iexists _
    iexact Hep
  ipureintro
  simp only [storAbsorb, storApp_pend]
  exact Hbnd

/-- (D19i part 1) **The floor law** for a `MemoryStorage` (`isStorageWith`'s `Hfloor`): with
nothing pending, the owner records the state at the new floor in `hist` (no lock: `done` lags by
floor raises), and hands out the witness. -/
theorem memStorage_floor (ms : Loc) (γs : MemStorNames) (σ : StorState) (x : w64)
    (Hx : σ.pend = [] ∧ uint.Z σ.fl ≤ uint.Z x ∧
      uint.Z x ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ ==∗
      ownMemoryStorage ms γs { σ with fl := x } ∗ memFloorTok ms γs x := by
  iintro Hown
  iunfold ownMemoryStorage at Hown
  iNamed Hown
  unfold memView
  icases Hview with ⟨%hist, %Hok, Hv⟩
  icases Hv with (⟨Hh, %Hidle, ⟨%D, Hw, %HDh⟩, %v, Hep⟩ | ⟨-, %H, %D, %Hpd, -, -⟩)
  rotate_left
  · exact absurd Hx.1 Hpd.1
  obtain ⟨HDpre, HDne, HR⟩ := HDh
  ihave #HlbD := monoListLbOwn_get γs.done _ D $$ Hw
  have Hok' : HistOk (hist ++ [{ σ with fl := x }]) :=
    Hok.snoc (fun w hw => by rw [Hidle.2] at hw; cases hw; exact Hx.2.1)
      (by simp only [EtcdGrove.stLast]; exact Hx.2.2) Hidle.1
      (Hok.2 σ (List.mem_of_getLast? Hidle.2)).2.2
  have HR' : RaiseOnly D ((hist ++ [{ σ with fl := x }]).drop D.length) := by
    rw [List.drop_append_of_le_length HDpre.length_le]
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact HR w hw
    · rw [List.mem_singleton] at hw
      subst hw
      obtain ⟨a, ha⟩ : ∃ a, D.getLast? = some a := by
        cases hD : D.getLast? with
        | none => rw [List.getLast?_eq_none_iff] at hD; exact absurd hD HDne
        | some a => exact ⟨a, rfl⟩
      exact ⟨a, ha, (DataEq.fl σ x).trans (RaiseOnly.last HDpre HR ha Hidle.2)⟩
  imod monoListAuthOwn_update_app [{ σ with fl := x }] $$ Hh with ⟨Hh, #Hlbh⟩
  imodintro
  isplitl [Hh Hw Hep Hsn]
  · unfold ownMemoryStorage memView
    simp only [named]
    iframe Hinit Hmu Hsn
    isplitl [Hh Hw Hep]
    · iexists hist ++ [{ σ with fl := x }]
      isplitr
      · ipureintro; exact Hok'
      ileft
      iframe Hh
      isplitr
      · ipureintro; exact ⟨Hidle.1, by simp⟩
      isplitl [Hw]
      · iexists D
        iframe Hw
        ipureintro
        exact ⟨HDpre.trans (List.prefix_append _ _), HDne, HR'⟩
      iexists v
      iexact Hep
    ipureintro; exact Hbounded
  unfold memFloorTok
  simp only [named]
  iframe Hinit Hmu
  iexists D, hist ++ [{ σ with fl := x }]
  iframe HlbD Hlbh
  ipureintro
  exact ⟨HDpre.trans (List.prefix_append _ _), HDne, HR', Hok', { σ with fl := x },
    by simp, Int.le_refl _⟩

end proof

end EtcdGrove
end Perennial

proj_simps Perennial.EtcdGrove.memStorApplied Perennial.EtcdGrove.memStorCompacted Perennial.EtcdGrove.memSnapCreated Perennial.EtcdGrove.storCS Perennial.EtcdGrove.memCut
