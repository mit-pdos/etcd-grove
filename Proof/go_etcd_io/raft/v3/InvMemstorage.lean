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

Lean notes: Rocq's tuple `(prev, ents, ss)` in the ghost variable is the record
`StorState` (`InvStorage.lean`), as everywhere a storage's state is passed. `ghost_var γ (1/2) v` is `ghostVar γ (1 : Qp).half v`,
`is_Mutex` is `sync.isMutex`, `is_pkg_init raft` is `isPkgInit pkg_id.go_etcd_io.raft.v3`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorage

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- What raft's view `σ` of the storage knows of its contents `σp` (2026-10-10): the
boundary and the snapshot are the same, and the entries are `σ`'s or, with a batch
pending, `σ`'s with the batch appended; with nothing pending, exactly `σ`. -/
def MemView (σ σp : StorState) : Prop :=
  σp.prev = σ.prev ∧ σp.ss = σ.ss ∧
  (σp.ents = σ.ents ∨ (σ.pend ≠ [] ∧ σp.ents = storApp σ σ.pend)) ∧
  (σ.pend = [] → σp = σ)

/-- A new storage (`NewMemoryStorage`): nothing stored, no snapshot, nothing pending. -/
def memStorEmpty : StorState :=
  { prev := entryID.mk (W64 0) (W64 0), ents := [], ss := entryID.mk (W64 0) (W64 0),
    pend := [] }

/-- A list between `H` and `H ++ [x]` in the prefix order is one of the two. -/
theorem prefix_between {A : Type _} (H D : List A) (x : A) (H1 : H <+: D)
    (H2 : D <+: H ++ [x]) : D = H ∨ D = H ++ [x] := by
  have L1 := H1.length_le
  have L2 := H2.length_le
  simp only [List.length_append, List.length_singleton] at L2
  by_cases h : D.length = H.length
  · exact .inl (H1.eq_of_length h.symm).symm
  · exact .inr (H2.eq_of_length (by simp; omega))

/-- `storApp` agrees with the stored entries below the batch. -/
theorem storApp_take (σ : StorState) (p : List raftpb.Entry) (m : Nat)
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

theorem storApp_length_ge (σ : StorState) (p : List raftpb.Entry) (m : Nat)
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

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

instance storState_countable : Pos.Countable StorState :=
  .ofInjective (fun σ => Pos.Countable.encode (((σ.prev, σ.ents), σ.ss), σ.pend))
    (fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
      rfl)

/-- The ghost names of a `MemoryStorage` (2026-10-10; until then one `GName`, of the
ghost variable of its state): see the file header. -/
structure MemStorNames where
  hist : GName
  done : GName
  ep : GName

/-- What the lock protects, at a given abstract state, *without* the ghost link: the
five fields other than the mutex, and everything hanging off them. This is what the
private helpers `lastIndex`/firstIndex` are specified on -- they are called with the
lock held -- and what a public method holds between `Lock` and `Unlock`. The entries'
capacity is owned (2026-10-10): `Append` appends in place when the batch continues
the log. -/
def memstorageFields (ms : Loc) (σ : StorState) : IProp GF :=
  iprop(∃ (hs : raftpb.HardState) (snap : raftpb.Snapshot) (es : GoSlice)
    (dummy : raftpb.Entry) (cs : inMemStorageCallStats) (voters : List w64),
  "HhardState" ∷ ms.[MemoryStorage, go!"hardState"] ↦ hs ∗
  "Hsnapshot" ∷ ms.[MemoryStorage, go!"snapshot"] ↦ snap ∗
  "%Hsnap_id" ∷ ⌜snapId snap = σ.ss⌝ ∗
  "Hvoters" ∷ snap.Metadata'.ConfState'.Voters' ↦*□ voters ∗
  "Hents_f" ∷ ms.[MemoryStorage, go!"ents"] ↦ es ∗
  "Hents" ∷ es ↦*□ (dummy :: σ.ents) ∗
  "Hents_cap" ∷ ownSliceCap raftpb.Entry es (DFrac.own 1) ∗
  "%Hdummy" ∷ ⌜dummy.Index' = σ.prev.index' ∧ dummy.Term' = σ.prev.term'⌝ ∗
  "HcallStats" ∷ ms.[MemoryStorage, go!"callStats"] ↦ cs)

/-- The ghost part of the lock's invariant: the contents `σp` are the last state
`done` records, at half of its authority, and every state it records is sanctioned. -/
def memInvGhost (γs : MemStorNames) (σp : StorState) : IProp GF :=
  iprop(∃ (D : List StorState),
    monoListAuthOwn γs.done (1 : Qp).half D ∗ monoListLbOwn γs.hist D ∗
    ⌜D.getLast? = some σp⌝)

/-- The lock's invariant: the contents, their ghost record, the fields at them, and
their bound (2026-10-10: the contents may be ahead of the owner's view, so the bound
the private helpers need is the invariant's). -/
def memstorageInv (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(∃ (σp : StorState),
  "Hgs" ∷ memInvGhost γs σp ∗
  "Hfields" ∷ memstorageFields ms σp ∗
  "%Hpb" ∷ ⌜uint.Z σp.prev.index' + (σp.ents.length : Int) < 2^61⌝)

/-- The owner's ghost view at `σ` (2026-10-10): `hist`'s authority, and either nothing
pending -- the writer's half of `done`, at `hist`, and all of `ep` -- or a batch
pending -- a lower bound of `done` at the hand-out and half of `ep`. -/
def memView (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(∃ (hist : List StorState),
    monoListAuthOwn γs.hist 1 hist ∗
    ((⌜σ.pend = [] ∧ hist.getLast? = some σ⌝ ∗
        monoListAuthOwn γs.done (1 : Qp).half hist ∗
        ∃ (v : StorState × List StorState), ghostVar γs.ep 1 v) ∨
     (∃ (H : List StorState),
        ⌜σ.pend ≠ [] ∧ hist = H ++ [storAbsorb σ] ∧
          H.getLast? = some { σ with pend := [] }⌝ ∗
        monoListLbOwn γs.done H ∗ ghostVar γs.ep (1 : Qp).half (σ, H))))

/-- A `MemoryStorage` at `ms` with the ghost names `γs`, whose owner sees it at `σ`.
Indexed by its names (2026-10-10), so that a token (`memAppendTok`, `memAppendedTok`)
is of this storage. Until 2026-10-10 it also asked `σ.ss.index' ≠ 0` (`isStorage`'s
`Snapshot` promises a non-empty snapshot); a new storage has none
(`NewMemoryStorage`), so the instance (`MemstorageInstance.lean`) adds it instead. -/
def ownMemoryStorage (ms : Loc) (γs : MemStorNames) (σ : StorState) : IProp GF :=
  iprop(
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  "Hview" ∷ memView γs σ ∗
  "%Hbounded" ∷ ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝)

/-- The application's right to append `p` to the storage at `σ` (2026-10-10): the
writer's half of `done` at the hand-out `H`, `hist` past the appended state, and
`ep`'s other half. -/
def memAppendTok (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List raftpb.Entry) :
    IProp GF :=
  iprop(
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  ∃ (H : List StorState),
  "Hdone" ∷ monoListAuthOwn γs.done (1 : Qp).half H ∗
  "#Hhist" ∷ monoListLbOwn γs.hist (H ++ [storAbsorb { σ with pend := p }]) ∗
  "Hep" ∷ ghostVar γs.ep (1 : Qp).half ({ σ with pend := p }, H) ∗
  "%Htok" ∷ ⌜H.getLast? = some σ ∧ σ.pend = [] ∧ PendOk σ p⌝)

/-- The receipt: the writer's half of `done` past the appended state, `ep`'s half, and
the appended state's bound (`Append`'s premise). -/
def memAppendedTok (_ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List raftpb.Entry) :
    IProp GF :=
  iprop(∃ (H : List StorState),
  "Hdone" ∷ monoListAuthOwn γs.done (1 : Qp).half (H ++ [storAbsorb { σ with pend := p }]) ∗
  "Hep" ∷ ghostVar γs.ep (1 : Qp).half ({ σ with pend := p }, H) ∗
  "%Hbnd" ∷ ⌜uint.Z σ.prev.index' + ((storApp σ p).length : Int) < 2^61⌝)

theorem monoAuth_agree_keep (γ : GName) (q1 q2 : Qp) (l1 l2 : List StorState) :
    (monoListAuthOwn γ q1 l1 ∗ monoListAuthOwn γ q2 l2 : IProp GF) ⊢
      (monoListAuthOwn γ q1 l1 ∗ monoListAuthOwn γ q2 l2) ∗ ⌜l1 = l2⌝ :=
  persistent_entails_left (by
    iintro ⟨H1, H2⟩
    icases monoListAuthOwn_agree γ q1 q2 l1 l2 $$ H1 H2 with %H
    ipureintro; exact H.2)

private theorem monoAuthLb_keep (γ : GName) (q : Qp) (l1 l2 : List StorState) :
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

/-- `Append`'s ghost step: the two halves of `done` (the invariant's and the writer's)
together record one more state. -/
theorem memDone_append (γs : MemStorNames) (H : List StorState) (x : StorState) :
    ⊢ monoListAuthOwn (GF := GF) γs.done (1 : Qp).half H -∗
      monoListAuthOwn γs.done (1 : Qp).half H ==∗
      monoListAuthOwn γs.done (1 : Qp).half (H ++ [x]) ∗
      monoListAuthOwn γs.done (1 : Qp).half (H ++ [x]) := by
  iintro H1 H2
  ihave Hf := (monoAuth_halves γs.done H).2 $$ [H1 H2]
  · iframe H1 H2
  imod monoListAuthOwn_update_app [x] $$ Hf with ⟨Hf, -⟩
  icases (monoAuth_halves γs.done (H ++ [x])).1 $$ Hf with ⟨H1, H2⟩
  imodintro
  iframe H1 H2

/-- Raft's view and the lock's ghost state agree (`MemView`), without consuming
either. -/
theorem memView_agree (γs : MemStorNames) (σ σp : StorState) :
    ⊢ memView (GF := GF) γs σ -∗ memInvGhost γs σp -∗
      ⌜MemView σ σp⌝ ∗ memView γs σ ∗ memInvGhost γs σp := by
  iintro Hv Hg
  unfold memView memInvGhost
  icases Hv with ⟨%hist, Hh, Hv⟩
  icases Hg with ⟨%D, Hd, #Hlb, %HD⟩
  icases Hv with (⟨%Hidle, Hw, Hep⟩ | ⟨%H, %Hpd, #HlbH, Hep⟩)
  · icases monoAuth_agree_keep γs.done _ _ hist D $$ [$Hw $Hd] with ⟨⟨Hw, Hd⟩, %Heq⟩
    subst Heq
    have Hσ : σp = σ := by rw [Hidle.2] at HD; injection HD with h; exact h.symm
    subst Hσ
    isplitr
    · ipureintro
      exact ⟨rfl, rfl, .inl rfl, fun _ => rfl⟩
    isplitl [Hh Hw Hep]
    · iexists hist
      iframe Hh
      ileft
      iframe Hw Hep
      ipureintro; exact Hidle
    iexists hist
    iframe Hd Hlb
    ipureintro; exact HD
  · icases monoAuthLb_keep γs.done _ D H $$ [$Hd $HlbH] with ⟨⟨Hd, -⟩, %H1⟩
    icases monoAuthLb_keep γs.hist _ hist D $$ [$Hh $Hlb] with ⟨⟨Hh, -⟩, %H2⟩
    obtain ⟨Hne, rfl, Hlast⟩ := Hpd
    isplitr
    · ipureintro
      rcases prefix_between H D _ H1 H2 with rfl | rfl
      · rw [Hlast] at HD
        injection HD with h
        subst h
        exact ⟨rfl, rfl, .inl rfl, fun h => absurd h Hne⟩
      · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at HD
        injection HD with h
        subst h
        exact ⟨rfl, rfl, .inr ⟨Hne, rfl⟩, fun h => absurd h Hne⟩
    isplitl [Hh Hep]
    · iexists H ++ [storAbsorb σ]
      iframe Hh
      iright
      iexists H
      iframe HlbH Hep
      ipureintro; exact ⟨Hne, rfl, Hlast⟩
    iexists D
    iframe Hd Hlb
    ipureintro; exact HD

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
  iframe Hinit Hmu Hview
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
  iframe Hinit Hmu Hview
  ipureintro; exact Hbounded

/-- The hand-out law for a `MemoryStorage` (`isStorageWith`'s `Hhandout`): `hist`
grows by the appended state, the writer's half of `done` and half of `ep` (at the new
hand-out) go to the token. No lock: the invariant only holds a lower bound of
`hist`. -/
theorem memStorage_handout (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (p : List raftpb.Entry) (Hpo : σ.pend = [] ∧ PendOk σ p) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ ==∗
      ownMemoryStorage ms γs { σ with pend := p } ∗ memAppendTok ms γs σ p := by
  iintro H
  iunfold ownMemoryStorage at H
  iNamed H
  unfold memView
  icases Hview with ⟨%hist, Hh, Hv⟩
  icases Hv with (⟨%Hidle, Hw, %v, Hep⟩ | ⟨%H, %Hpd, -, -⟩)
  rotate_left
  · exact absurd Hpo.1 Hpd.1
  ihave #HlbD := monoListLbOwn_get γs.done _ hist $$ Hw
  imod monoListAuthOwn_update_app [storAbsorb { σ with pend := p }] $$ Hh with ⟨Hh, #Hlbh⟩
  imod ghostVar_update ({ σ with pend := p }, hist) γs.ep v $$ Hep with Hep
  icases ghostVar_split γs.ep _ (1 : Qp).half (1 : Qp).half $$ [Hep] with ⟨Hep1, Hep2⟩
  · rw [Qp.half_add_half]; iexact Hep
  imodintro
  have Hσ : ({ { σ with pend := p } with pend := [] } : StorState) = σ := by
    rw [← Hpo.1]
  isplitl [Hh Hep1]
  · unfold ownMemoryStorage memView
    simp only [named]
    iframe Hinit Hmu
    isplitl
    · iexists hist ++ [storAbsorb { σ with pend := p }]
      iframe Hh
      iright
      iexists hist
      iframe HlbD Hep1
      ipureintro
      exact ⟨Hpo.2.1, rfl, by rw [Hσ]; exact Hidle.2⟩
    ipureintro; exact Hbounded
  unfold memAppendTok
  simp only [named]
  iframe Hinit Hmu
  iexists hist
  iframe Hw Hlbh Hep2
  ipureintro
  exact ⟨Hidle.2, Hpo.1, Hpo.2⟩

/-- The absorb law for a `MemoryStorage` (`isStorageWith`'s `Habsorb`): the receipt's
half of `ep` agrees with the owner's (so it is of this hand-out), and its half of `done`
is the writer's again, at `hist`. -/
theorem memStorage_absorb (ms : Loc) (γs : MemStorNames) (σ1 σ : StorState)
    (p : List raftpb.Entry) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ1 -∗ memAppendedTok ms γs σ p ==∗
      ⌜σ1 = { σ with pend := p }⌝ ∗ ownMemoryStorage ms γs (storAbsorb σ1) := by
  iintro H Ht
  iunfold ownMemoryStorage at H
  iNamed H
  iunfold memAppendedTok at Ht
  icases Ht with ⟨%Ht, Hdone, Hept, %Hbnd⟩
  unfold memView
  icases Hview with ⟨%hist, Hh, Hv⟩
  icases Hv with (⟨%Hidle, Hw, %v, Hep⟩ | ⟨%H, %Hpd, #HlbH, Hep⟩)
  · -- idle: the owner holds all of `ep`, so there is no receipt
    icases ghostVar_valid_2 γs.ep _ _ _ _ $$ Hep Hept with %Hq
    obtain ⟨Hq, -⟩ := Hq
    exfalso
    grind
  icases ghostVar_agree γs.ep _ _ _ _ $$ Hep Hept with %Heq
  injection Heq with Hσ1 HH
  subst HH
  obtain ⟨Hne, rfl, Hlast⟩ := Hpd
  icombine Hep Hept as Hep
  imodintro
  isplitr
  · ipureintro; exact Hσ1
  subst Hσ1
  unfold ownMemoryStorage memView
  simp only [named]
  iframe Hinit Hmu
  isplitl
  · iexists H ++ [storAbsorb { σ with pend := p }]
    iframe Hh
    ileft
    iframe Hdone
    isplitr
    · ipureintro
      exact ⟨rfl, by simp⟩
    iexists _
    iexact Hep
  ipureintro
  simp only [storAbsorb, storApp_pend]
  exact Hbnd

end proof

end EtcdGrove
end Perennial
