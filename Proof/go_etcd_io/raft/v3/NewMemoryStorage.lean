/- `NewMemoryStorage` (`storage.go:113`), proved 2026-10-10 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.NewMemoryStorage

@[expose] public section

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

/-- The fields at the empty state, the ghost state at its one state, and the mutex
allocated around them. -/
theorem NewMemoryStorage.wp_proof :
    NewMemoryStorage.spec (GF := GF) (hG := hG) := by
  wp_start as #Hinit
  wp_apply wp_slice_make2 (V := raftpb.Entry) (W64 1) as %sl ⟨Hsl, Hsl_cap⟩
  · ipureintro; word
  wp_alloc ms as Hms
  iStructNamed Hms
  imod ownSlice_persist $$ Hsl with #Hsl
  -- the ghost state: `hist` and `done` at the one state, `ep` arbitrary
  imod mono_list_own_alloc (GF := GF) [memStorEmpty] with ⟨%γh, Hh, #Hhlb⟩
  imod mono_list_own_alloc (GF := GF) [memStorEmpty] with ⟨%γd, Hd, -⟩
  icases (monoAuth_halves γd [memStorEmpty]).1 $$ Hd with ⟨Hd1, Hd2⟩
  imod ghostVar_alloc (GF := GF) (memStorEmpty, ([] : List StorState)) with ⟨%γe, He⟩
  imod sync.init_Mutex (memstorageInv ms ⟨γh, γd, γe⟩) ⊤ (ms.[MemoryStorage, go!"Mutex"])
    $$ Mutex [Hd1 hardState snapshot ents callStats Hsl_cap] with #Hmu
  · inext
    unfold memstorageInv
    iexists memStorEmpty
    isplitl [Hd1]
    · unfold memInvGhost
      iexists [memStorEmpty]
      iframe Hd1 Hhlb
      ipureintro; rfl
    isplitl
    · unfold memstorageFields
      iexists zero_val raftpb.HardState, zero_val raftpb.Snapshot, sl, zero_val raftpb.Entry,
        zero_val inMemStorageCallStats, []
      simp only [named]
      iframe
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownSlice_nil
      isplitr
      · rw [show zero_val raftpb.Entry :: memStorEmpty.ents = List.replicate 1 (zero_val raftpb.Entry)
          from rfl]
        iexact Hsl
      ipureintro; exact ⟨rfl, rfl⟩
    ipureintro; simp only [memStorEmpty, List.length_nil]; word
  wp_auto
  iapply HΦ $$ %ms %(⟨γh, γd, γe⟩ : MemStorNames)
  unfold ownMemoryStorage memView
  simp only [named]
  iframe Hpkg Hmu
  isplitl
  · iexists [memStorEmpty]
    iframe Hh
    ileft
    iframe Hd2
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists _
    iexact He
  ipureintro; simp only [memStorEmpty, List.length_nil]; word

end proof

end EtcdGrove
end Perennial
