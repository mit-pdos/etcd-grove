/-
Port of `election_proof/memstorage_instance.v` (at feb5c73d4).

### `MemoryStorage` meets the `Storage` contract

`isStorageWith (ownMemoryStorage ms) st` for `st` the interface value holding
`ms : *MemoryStorage` -- the contract `InvStorage.lean` states of a client-supplied
`Storage`, against raft's own implementation of it.

This is not in `InvMemstorage.lean`, where the predicate lives, because it is built from
the five method collections, which import that file; it is a file of its own, below the
links (`Link.lean`), with no triple of its own to state (the Hoare statements are
`isStorageWith`'s, and the proofs are the collections').

Lean notes: the method clauses of `isStorageWith` call `methods i.ty go!"M" i.v`, and the
collections' specs call `ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"M"`; for
`i = interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms` the two are the same term
up to unfolding, so `wp_apply` of the collection's result closes each clause directly (as
Perennial's `sync.Mutex_is_Locker` does).
### The `StorageModel` instance for `*MemoryStorage` (2026-10-16, stage R7a)

`isStorageWith` above is the contract against `ownMemoryStorage ms γs` itself; raft's node
specs take it against the class's `ownStorage st` (`isStorage st`), so an application whose
`Storage` is a bare `*MemoryStorage` (etcd's server: `raft.NewMemoryStorage()` passed as
`Config.Storage`) needs an instance of `StorageModel` whose `ownStorage (memStorIface ms) σ`
is `ownMemoryStorage ms γs σ`. The instance (`memStorageModel`) recovers a storage's ghost
names from its pointer through a **registry**, a ghost map from the pointer to the names
(`memStorReg ms γs`, persistent), given by the class `MemStorReg` (its name, allocated by the
application before the run: `ghost_map_alloc_empty`). The registry's authority is the
application's, not an invariant's: registering a storage (`memStorReg_register`) needs its
pointer absent from the map, which the application knows of the map it holds (nothing
physical of a `MemoryStorage` is left over for an invariant to keep, as the register's registry
keeps half of its own struct's field; `Proof/github_com/mit_pdos/etcd_grove/examples/register/
Defs.lean`). A wrong registration is harmless: `ownStorage` then cannot be established for
that storage (its real names disagree).

`ownStorage` carries the snapshot premise `σ.ss.index' ≠ 0` of `is_Storage_MemoryStorage`
(the contract's `Snapshot` clause promises a non-empty snapshot, which a bare `MemoryStorage`
returns only once it has one): a storage is a `Storage` from the moment it holds a snapshot
(`ApplySnapshot`, `CreateSnapshot`). The conversions (`memOwnStorage_at`/`_intro`,
`memAppendRight_at`, `memAppendReceipt_intro`) go between the class's predicates and
`ownMemoryStorage`/`memAppendTok`/`memAppendedTok` under `memStorReg ms γs`;
`memStorage_isStorage` is the contract and `memStorage_Append` the application's `Append` in
the contract's terms (`appendRight` in, `appendReceipt` out), under `MemoryStorage.Append`'s
own premise: the batch's last index at most `2^61`.
-/
module

public import Proof.go_etcd_io.raft.v3.Link

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `MemoryStorage` with a snapshot meets the contract (raft v3.7, stage R3: the `Snapshot`
clause's fresh owned clone is the method's own result), with its own hand-out and
receipt (`memAppendTok`, `memAppendedTok`, `InvMemstorage.lean`). The snapshot premise
(`ss.index ≠ 0`, until 2026-10-10 a conjunct of `ownMemoryStorage`) is the contract's
`Snapshot` clause, which promises a non-empty snapshot: a new storage
(`NewMemoryStorage`) has none, and raft's `maybeSendSnapshot` panics on an empty one.
It is reached only after a storage query failed, which `ErrCompacted` does only once the
storage has compacted -- but also after an `ErrUnavailable` for a peer's `Next` past the
log, which nothing proved here bounds (notes/decisions.md, "Storage: a pending append,
for node.go"). Both laws keep `ss`. -/
theorem is_Storage_MemoryStorage (ms : Loc) (γs : MemStorNames) :
    ⊢ isStorageWith (GF := GF) (fun σ => iprop(ownMemoryStorage ms γs σ ∗ ⌜σ.ss.index' ≠ W64 0⌝))
        (memAppendTok ms γs) (memAppendedTok ms γs)
        (interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms) := by
  unfold isStorageWith
  simp only []
  iexists (interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, %Hpn⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_LastIndex $$ [$Hown] as %li ⟨%Hli, Hown⟩
    · ipureintro; exact Hpn
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hli, Hss⟩
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨Hown, %Hss⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_FirstIndex $$ [$Hown] as %fi ⟨%Hfi, Hown⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hfi, Hss⟩
  isplitr
  · iintro %σ %i0
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, %Hr, %Hpf⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Term $$ [$Hown] as %t ⟨%Ht, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨Ht, Hss⟩
  isplitr
  · iintro %σ %lo %hi %maxSize
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, %Hr, %Hpf⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Entries $$ [$Hown] as %s %es ⟨Hs, %Hp, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hp, Hss⟩
  isplitr
  · imodintro
    iintro %σ ⟨Hown, %Hss⟩
    icases ownMemoryStorage_bounded $$ Hown with ⟨%Hb, Hown⟩
    iframe
    ipureintro; exact ⟨Hb, Hss⟩
  isplitr
  · iintro %σ %esu
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, #Hesu⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Snapshot $$ [$Hown $Hesu] as %snap %err ⟨Hown, Hr⟩
    iapply HΦ
    iframe Hown
    isplitr
    · ipureintro; exact Hss
    icases Hr with (%Herr | ⟨%Herr, %sv, Hv, %Hsv⟩)
    · ileft; ipureintro; exact Herr
    iright
    isplitr
    · ipureintro; exact Herr
    iexists sv
    iframe Hv
    ipureintro
    refine ⟨Hsv.1, ?_, Hsv.2.1, Hsv.2.2⟩
    have H := congrArg entryID.index' Hsv.1
    simp only [snapId] at H
    rw [H]; exact Hss
  isplitr
  · imodintro
    iintro %σ %p ⟨Hown, %Hss⟩ %Hpo
    imod memStorage_handout ms γs σ p Hpo $$ Hown with ⟨Hown, Htok⟩
    imodintro
    iframe
    ipureintro; exact Hss
  imodintro
  iintro %σ1 %σ %p ⟨Hown, %Hss⟩ Ht
  imod memStorage_absorb ms γs σ1 σ p $$ Hown Ht with ⟨%Heq, Hown⟩
  imodintro
  iframe
  ipureintro; exact ⟨Heq, Hss⟩

end proof

/-! ## The `StorageModel` instance for `*MemoryStorage` (2026-10-16, stage R7a) -/

set_option linter.unusedSectionVars false

/-- The registry's ghost name: a class, so that `memStorageModel` can be an instance. The
application allocates it before the run (`ghost_map_alloc_empty` at `GMap Loc MemStorNamesRec`)
and holds its authority (`memStorRegAuth`). -/
class MemStorReg (GF : BundledGFunctors) where
  memStorRegName : GName

/-- A storage's names, as the registry records them. -/
abbrev MemStorNamesRec := GName × GName × GName

def MemStorNames.tuple (γs : MemStorNames) : MemStorNamesRec := (γs.hist, γs.done, γs.ep)

theorem MemStorNames.rec_inj (γs1 γs2 : MemStorNames) (h : γs1.tuple = γs2.tuple) : γs1 = γs2 := by
  cases γs1; cases γs2
  simp only [MemStorNames.tuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [MemStorReg GF]

/-- The registry's authority: the storages registered so far, with their names. -/
def memStorRegAuth (M : GMap Loc MemStorNamesRec) : IProp GF :=
  ghostMapAuth (MemStorReg.memStorRegName (GF := GF)) 1 M

/-- The `MemoryStorage` `ms` has the names `γs` (persistent). -/
def memStorReg (ms : Loc) (γs : MemStorNames) : IProp GF :=
  ms ↪[MemStorReg.memStorRegName (GF := GF)]□ γs.tuple

instance memStorReg_persistent (ms : Loc) (γs : MemStorNames) :
    Persistent (memStorReg (GF := GF) ms γs) := by
  unfold memStorReg; infer_instance

theorem memStorReg_agree (ms : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ memStorReg (GF := GF) ms γs1 -∗ memStorReg ms γs2 -∗ ⌜γs1 = γs2⌝ := by
  unfold memStorReg
  iintro #H1 #H2
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact MemStorNames.rec_inj _ _ H

/-- A storage joins the registry: its pointer absent so far (the application knows the map it
holds), it is recorded with its names, for good. -/
theorem memStorReg_register (M : GMap Loc MemStorNamesRec) (ms : Loc) (γs : MemStorNames)
    (HM : M.lookup ms = none) :
    ⊢ memStorRegAuth (GF := GF) M ==∗ memStorRegAuth (M.insert ms γs.tuple) ∗ memStorReg ms γs := by
  unfold memStorRegAuth memStorReg
  iintro H
  imod ghost_map_insert_persist ms γs.tuple HM $$ H with ⟨H, #Hf⟩
  imodintro
  iframe H Hf

/-- The raft `Storage` interface value holding the `*MemoryStorage` `ms`. -/
def memStorIface (ms : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms

include sem in
theorem memStorIface_inj (ms1 ms2 : Loc) : memStorIface ms1 = memStorIface ms2 → ms1 = ms2 := by
  intro h
  simp only [memStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The storage behind the interface value `st`: a registered `MemoryStorage`, owned at `σ`,
holding a snapshot (`is_Storage_MemoryStorage`'s premise). -/
def memOwnStorage (st : Storage) (σ : StorState) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    ownMemoryStorage ms γs σ ∗ ⌜σ.ss.index' ≠ W64 0⌝)

/-- The right to append `p` to the storage `st` at `σ`: the `MemoryStorage`'s, of its names. -/
def memStorAppendTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memAppendTok ms γs σ p)

/-- The receipt of the append. -/
def memStorAppendedTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memAppendedTok ms γs σ p)

/-- The storage model of an application whose `Storage`s are bare `MemoryStorage`s. -/
instance memStorageModel : StorageModel GF where
  ownStorage := memOwnStorage
  appendTok := memStorAppendTok
  appendedTok := memStorAppendedTok

/-! ### The conversions, under the registry's record -/

theorem memOwnStorage_at (ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ memStorReg (GF := GF) ms γs -∗ ownStorage (memStorIface ms) σ -∗
      ownMemoryStorage ms γs σ ∗ ⌜σ.ss.index' ≠ W64 0⌝ := by
  iintro #Hreg Hown
  ihave Hown : memOwnStorage (memStorIface ms) σ $$ [Hown]
  · iexact Hown
  unfold memOwnStorage
  icases Hown with ⟨%ms', %γs', %Hst, #Hreg', Hown, %Hss⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iframe Hown
  ipureintro; exact Hss

theorem memOwnStorage_intro (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (Hss : σ.ss.index' ≠ W64 0) :
    ⊢ memStorReg (GF := GF) ms γs -∗ ownMemoryStorage ms γs σ -∗ ownStorage (memStorIface ms) σ := by
  iintro #Hreg Hown
  ihave H : memOwnStorage (memStorIface ms) σ $$ [Hown]
  · unfold memOwnStorage
    iexists ms, γs
    iframe Hreg Hown
    ipureintro; exact ⟨rfl, Hss⟩
  iexact H

theorem memStorAppendTok_at (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ appendTok (memStorIface ms) σ p -∗ memAppendTok ms γs σ p := by
  iintro #Hreg Ht
  ihave Ht : memStorAppendTok (memStorIface ms) σ p $$ [Ht]
  · iexact Ht
  unfold memStorAppendTok
  icases Ht with ⟨%ms', %γs', %Hst, #Hreg', Ht⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iexact Ht

theorem memStorAppendTok_intro (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memAppendTok ms γs σ p -∗ appendTok (memStorIface ms) σ p := by
  iintro #Hreg Ht
  ihave H : memStorAppendTok (memStorIface ms) σ p $$ [Ht]
  · unfold memStorAppendTok
    iexists ms, γs
    iframe Hreg Ht
    ipureintro; rfl
  iexact H

theorem memStorAppendedTok_at (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ appendedTok (memStorIface ms) σ p -∗
      memAppendedTok ms γs σ p := by
  iintro #Hreg Ht
  ihave Ht : memStorAppendedTok (memStorIface ms) σ p $$ [Ht]
  · iexact Ht
  unfold memStorAppendedTok
  icases Ht with ⟨%ms', %γs', %Hst, #Hreg', Ht⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iexact Ht

theorem memStorAppendedTok_intro (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memAppendedTok ms γs σ p -∗
      appendedTok (memStorIface ms) σ p := by
  iintro #Hreg Ht
  ihave H : memStorAppendedTok (memStorIface ms) σ p $$ [Ht]
  · unfold memStorAppendedTok
    iexists ms, γs
    iframe Hreg Ht
    ipureintro; rfl
  iexact H

/-- What a `Ready` hands out for its entries (`appendRight`, `InvStorage.lean`), at the
`MemoryStorage`: nothing for no entries, otherwise `MemoryStorage.Append`'s token. -/
theorem memAppendRight_at (ms : Loc) (γs : MemStorNames) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ appendRight (memStorIface ms) p -∗
      ⌜p = []⌝ ∨ ∃ σ, memAppendTok ms γs σ p := by
  iintro #Hreg Hr
  unfold appendRight
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iapply memStorAppendTok_at ms γs σ p $$ Hreg Ht

theorem memAppendRight_intro (ms : Loc) (γs : MemStorNames) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ (⌜p = []⌝ ∨ ∃ σ, memAppendTok ms γs σ p) -∗
      appendRight (memStorIface ms) p := by
  iintro #Hreg Hr
  unfold appendRight
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iapply memStorAppendTok_intro ms γs σ p $$ Hreg Ht

/-- ... and the receipt the application gives back (`appendReceipt`). -/
theorem memAppendReceipt_intro (ms : Loc) (γs : MemStorNames) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ (⌜p = []⌝ ∨ ∃ σ, memAppendedTok ms γs σ p) -∗
      appendReceipt (memStorIface ms) p := by
  iintro #Hreg Hr
  unfold appendReceipt
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iapply memStorAppendedTok_intro ms γs σ p $$ Hreg Ht

theorem memAppendReceipt_at (ms : Loc) (γs : MemStorNames) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ appendReceipt (memStorIface ms) p -∗
      ⌜p = []⌝ ∨ ∃ σ, memAppendedTok ms γs σ p := by
  iintro #Hreg Hr
  unfold appendReceipt
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iapply memStorAppendedTok_at ms γs σ p $$ Hreg Ht

/-! ### The contract and the application's `Append` -/

/-- **A registered `MemoryStorage` is a raft `Storage`** (the contract `RestartNode` takes):
`is_Storage_MemoryStorage` through the conversions. -/
theorem memStorage_isStorage (ms : Loc) (γs : MemStorNames) :
    ⊢ memStorReg (GF := GF) ms γs -∗ isStorage (memStorIface ms) := by
  iintro #Hreg
  unfold isStorage isStorageWith
  iexists (interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨Hown, %Hpn⟩ HΦ
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_apply MemoryStorage.wp_LastIndex $$ [$Hown] as %li ⟨%Hli, Hown⟩
    · ipureintro; exact Hpn
    iapply HΦ
    ihave Hown := memOwnStorage_intro ms γs σ Hss $$ Hreg Hown
    iframe Hown
    ipureintro; exact Hli
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ Hown HΦ
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_apply MemoryStorage.wp_FirstIndex $$ [$Hown] as %fi ⟨%Hfi, Hown⟩
    iapply HΦ
    ihave Hown := memOwnStorage_intro ms γs σ Hss $$ Hreg Hown
    iframe Hown
    ipureintro; exact Hfi
  isplitr
  · iintro %σ %i0
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf⟩ HΦ
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_apply MemoryStorage.wp_Term $$ [$Hown] as %t ⟨%Ht, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    ihave Hown := memOwnStorage_intro ms γs σ Hss $$ Hreg Hown
    iframe Hown
    ipureintro; exact Ht
  isplitr
  · iintro %σ %lo %hi %maxSize
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf⟩ HΦ
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_apply MemoryStorage.wp_Entries $$ [$Hown] as %sl %es ⟨Hs, %Hp, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    ihave Hown := memOwnStorage_intro ms γs σ Hss $$ Hreg Hown
    iframe Hown Hs
    ipureintro; exact Hp
  isplitr
  · imodintro
    iintro %σ Hown
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    icases ownMemoryStorage_bounded ms γs σ $$ Hown with ⟨%Hb, Hown⟩
    ihave Hown := memOwnStorage_intro ms γs σ Hss $$ Hreg Hown
    iframe Hown
    ipureintro; exact Hb
  isplitr
  · iintro %σ %esu
    imodintro
    iintro %Φ ⟨Hown, #Hesu⟩ HΦ
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_apply MemoryStorage.wp_Snapshot $$ [$Hown $Hesu] as %snap %err ⟨Hown, Hr⟩
    iapply HΦ
    ihave Hown := memOwnStorage_intro ms γs σ Hss $$ Hreg Hown
    iframe Hown
    icases Hr with (%Herr | ⟨%Herr, %sv, Hv, %Hsv⟩)
    · ileft; ipureintro; exact Herr
    iright
    isplitr
    · ipureintro; exact Herr
    iexists sv
    iframe Hv
    ipureintro
    refine ⟨Hsv.1, ?_, Hsv.2.1, Hsv.2.2⟩
    have H := congrArg entryID.index' Hsv.1
    simp only [snapId] at H
    rw [H]; exact Hss
  isplitr
  · imodintro
    iintro %σ %p Hown %Hpo
    ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ $$ Hreg Hown
    imod memStorage_handout ms γs σ p Hpo $$ Hown with ⟨Hown, Htok⟩
    ihave Hown := memOwnStorage_intro ms γs { σ with pend := p } Hss $$ Hreg Hown
    ihave Htok := memStorAppendTok_intro ms γs σ p $$ Hreg Htok
    imodintro
    iframe Hown Htok
  imodintro
  iintro %σ1 %σ %p Hown Ht
  ihave ⟨Hown, %Hss⟩ := memOwnStorage_at ms γs σ1 $$ Hreg Hown
  ihave Ht := memStorAppendedTok_at ms γs σ p $$ Hreg Ht
  imod memStorage_absorb ms γs σ1 σ p $$ Hown Ht with ⟨%Heq, Hown⟩
  ihave Hown := memOwnStorage_intro ms γs (storAbsorb σ1)
    (show (storAbsorb σ1).ss.index' ≠ W64 0 from Hss) $$ Hreg Hown
  imodintro
  iframe Hown
  ipureintro; exact Heq

/-- **The application's `Append`** of the entries a `Ready` handed out, in the contract's terms:
the right in (`appendRight`, `RawNode.Ready`'s), the receipt out (`appendReceipt`, what
`node.Advance` takes back), the slice of read-only entries lent. Under `MemoryStorage.Append`'s
premise, which is the caller's to establish (the register checks it in Go, `fits`; etcd's
server carries it as a premise on the run, `rnLogFits`): the batch's last index is at most
`2^61`, i.e. `e0.Index + |p| ≤ 2^61` for its first entry `e0`. -/
theorem memStorage_Append (ms : Loc) (γs : MemStorNames) (p : List EntryM) (s : GoSlice)
    (dq : DFrac)
    (Hfit : ∀ e0, p.head? = some e0 → uint.Z e0.Index' + (p.length : Int) ≤ 2^61) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        memStorReg ms γs ∗ appendRight (memStorIface ms) p ∗ entsPts s dq p }}
      (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #s))
    {{ RET #interface.nil; appendReceipt (memStorIface ms) p ∗ entsPts s dq p }} := by
  iintro %Φ ⟨#Hinit, #Hreg, Hr, Hs⟩ HΦ
  ihave Hr := memAppendRight_at ms γs p $$ Hreg Hr
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ihave Htok : (⌜p = []⌝ ∨ memAppendTok ms γs memStorEmpty p : IProp GF) $$ []
    · ileft; ipureintro; exact Hp
    wp_apply MemoryStorage.wp_Append ms γs memStorEmpty p s dq Hfit $$ [$Hinit $Htok $Hs]
      as ⟨Hrec, Hs⟩
    iapply HΦ
    iframe Hs
    iapply memAppendReceipt_intro ms γs p $$ Hreg
    ileft; ipureintro; exact Hp
  ihave Htok : (⌜p = []⌝ ∨ memAppendTok ms γs σ p : IProp GF) $$ [Ht]
  · iright; iexact Ht
  wp_apply MemoryStorage.wp_Append ms γs σ p s dq Hfit $$ [$Hinit $Htok $Hs] as ⟨Hrec, Hs⟩
  iapply HΦ
  iframe Hs
  iapply memAppendReceipt_intro ms γs p $$ Hreg
  icases Hrec with (%Hp | Hrec)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iexact Hrec

end model

end EtcdGrove
end Perennial
