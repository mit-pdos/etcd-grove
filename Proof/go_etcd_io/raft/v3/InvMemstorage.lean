/-
Port of `election_proof/inv_memstorage.v` (at feb5c73d4): `MemoryStorage`'s
representation predicate, the ownership predicate its `isStorageWith` instance
(`memstorage_instance.v`, `MemstorageInstance.lean`) is stated against.

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

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

instance storState_countable : Pos.Countable StorState :=
  .ofInjective (fun σ => Pos.Countable.encode ((σ.prev, σ.ents), σ.ss))
    (fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      rfl)

/-- What the lock protects, at a given abstract state, *without* the ghost link: the
five fields other than the mutex, and everything hanging off them. This is what the
private helpers `lastIndex`/`firstIndex` are specified on -- they are called with the
lock held -- and what a public method holds between `Lock` and `Unlock`. -/
def memstorageFields (ms : Loc) (σ : StorState) : IProp GF :=
  iprop(∃ (hs : raftpb.HardState) (snap : raftpb.Snapshot) (es : GoSlice)
    (dummy : raftpb.Entry) (cs : inMemStorageCallStats) (voters : List w64),
  "HhardState" ∷ ms.[MemoryStorage, go!"hardState"] ↦ hs ∗
  "Hsnapshot" ∷ ms.[MemoryStorage, go!"snapshot"] ↦ snap ∗
  "%Hsnap_id" ∷ ⌜snapId snap = σ.ss⌝ ∗
  "Hvoters" ∷ snap.Metadata'.ConfState'.Voters' ↦*□ voters ∗
  "Hents_f" ∷ ms.[MemoryStorage, go!"ents"] ↦ es ∗
  "Hents" ∷ es ↦*□ (dummy :: σ.ents) ∗
  "%Hdummy" ∷ ⌜dummy.Index' = σ.prev.index' ∧ dummy.Term' = σ.prev.term'⌝ ∗
  "HcallStats" ∷ ms.[MemoryStorage, go!"callStats"] ↦ cs)

/-- The lock's invariant: the abstract state, half of the ghost variable that records
it, and the fields at that state. -/
def memstorageInv (ms : Loc) (γ : GName) : IProp GF :=
  iprop(∃ (σ : StorState),
  "Hgs" ∷ ghostVar γ (1 : Qp).half σ ∗
  "Hfields" ∷ memstorageFields ms σ)

def ownMemoryStorage (ms : Loc) (σ : StorState) : IProp GF :=
  iprop(∃ (γ : GName),
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γ) ∗
  "Hgs" ∷ ghostVar γ (1 : Qp).half σ ∗
  "%Hbounded" ∷ ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝ ∗
  "%Hss" ∷ ⌜σ.ss.index' ≠ W64 0⌝)

/-- The two facts `isStorage` wants of an ownership predicate that are not method
specs, read out of `ownMemoryStorage` without consuming it. The package initializer is
in the predicate because the methods take the lock, which needs `isPkgInit sync`;
`isStorage`'s method triples have no such premise. -/
theorem ownMemoryStorage_init (ms : Loc) (σ : StorState) :
    ⊢ ownMemoryStorage (GF := GF) ms σ -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownMemoryStorage ms σ := by
  iintro H
  unfold ownMemoryStorage
  icases H with ⟨%γ, H⟩
  iNamed H
  isplitr
  · iexact Hinit
  iexists γ
  simp only [named]
  iframe Hinit Hmu Hgs
  ipureintro; exact ⟨Hbounded, Hss⟩

theorem ownMemoryStorage_bounded (ms : Loc) (σ : StorState) :
    ⊢ ownMemoryStorage (GF := GF) ms σ -∗
      ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝ ∗
      ownMemoryStorage ms σ := by
  iintro H
  unfold ownMemoryStorage
  icases H with ⟨%γ, H⟩
  iNamed H
  isplitr
  · ipureintro; exact Hbounded
  iexists γ
  simp only [named]
  iframe Hinit Hmu Hgs
  ipureintro; exact ⟨Hbounded, Hss⟩

end proof

end EtcdGrove
end Perennial
