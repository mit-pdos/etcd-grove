/- `NewMemoryStorage` (`storage.go:113`), proved 2026-10-10 (Lean-first). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMemstorage

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
theorem NewMemoryStorage.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG)) :
    NewMemoryStorage.spec (GF := GF) (hG := hG) := by
  wp_start as #Hinit
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue [])] = 1 := rfl
  simp only [Hsz]
  -- the dummy entry, a fresh zero `*pb.Entry`, frozen
  imod entOwn_of_struct l0 (zero_val raftpb.Entry) (zero_val EntryM) ⊤ rfl rfl $$ [Hl0] with He0
  · iframe Hl0
    isplitl [] <;> try isplitl []
    all_goals iapply cellRO_null
  imod entOwn_freeze $$ He0 with #He0
  wp_auto
  iStructNamed «$r0»
  -- the lock's half of `hardState` and its counters (2026-10-12)
  icases (ptsto_halves _ _).1 $$ hardState with ⟨hardState, HhardState⟩
  iStructNamedPrefix callStats "cs_"
  imod ownSlice_persist $$ Hsl with #Hsl
  -- the ghost state: `hist` and `done` at the one state, `ep` arbitrary
  imod mono_list_own_alloc (GF := GF) [memStorEmpty] with ⟨%γh, Hh, #Hhlb⟩
  imod mono_list_own_alloc (GF := GF) [memStorEmpty] with ⟨%γd, Hd, -⟩
  icases (monoAuth_halves γd [memStorEmpty]).1 $$ Hd with ⟨Hd1, Hd2⟩
  imod ghostVar_alloc (GF := GF) (memStorEmpty, ([] : List StorState)) with ⟨%γe, He⟩
  imod sync.init_Mutex (memstorageInv «$r0_ptr» ⟨γh, γd, γe⟩) ⊤ («$r0_ptr».[MemoryStorage, go!"Mutex"])
    $$ Mutex [Hd1 hardState ents cs_firstIndex cs_lastIndex cs_entries cs_term
      cs_snapshot Hsl_cap] with #Hmu
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
      iexists null, slice.mk slp (W64 1) (W64 1), zero_val EntryM, _, _, _, _, _
      simp only [named]
      iframe
      isplitr
      · iunfold entsRO; iunfold entsPts
        iexists [l0]
        iframe Hsl
        iapply (BigSepL2.bigSepL2_cons).2
        iframe He0
        rw [show memStorEmpty.ents = [] from rfl]
        iapply entsBig_nil
      ipureintro; exact ⟨rfl, rfl⟩
    ipureintro; simp only [memStorEmpty, List.length_nil]; word
  wp_apply wp_EnsureSnapshot null none $$ [] as %sp ⟨Hsp, -⟩
  · simp only [snapOpt]; ipureintro; trivial
  simp only [Option.getD_none]
  ihave Hsp := ownSnapE_weaken $$ Hsp
  iapply HΦ $$ %«$r0_ptr» %(⟨γh, γd, γe⟩ : MemStorNames)
  isplitr [HhardState cs_initialState]
  rotate_left
  · unfold memStorMeta
    iexists _, null
    simp only [named]
    iframe Hpkg Hmu HhardState cs_initialState
    iapply hsOpt_null
  unfold ownMemoryStorage memView memSnapOwn
  simp only [named]
  iframe Hpkg Hmu
  isplitl [Hh Hd2 He]
  · iexists [memStorEmpty]
    iframe Hh
    ileft
    iframe Hd2
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists _
    iexact He
  isplitl
  · iexists sp, _
    iframe snapshot Hsp
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  ipureintro; simp only [memStorEmpty, List.length_nil]; word

end proof

end EtcdGrove
end Perennial
