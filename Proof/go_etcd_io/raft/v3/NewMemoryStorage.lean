/- `NewMemoryStorage` (`storage.go:113`), proved 2026-10-10 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage

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
  imod entOwn_of_struct l0 (zero_val raftpb.Entry) (zero_val EntryM) ⊤ rfl $$ [Hl0] with He0
  · iframe Hl0
    isplitl []; · iapply cellRO_null
    isplitl []; · iapply cellRO_null
    isplitl []; · iapply cellRO_null
    iapply ownSlice_nil
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
  -- (D17d) the snapshot's ghost value, where it is, and the keys
  imod ghostVar_alloc (GF := GF) (snapPart memStorEmpty) with ⟨%γsn, Hsn⟩
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γsw, Hsw⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γlk, Hlk⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γok, Hok⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γak, Hak⟩
  ihave Hlk : memKey (GF := GF) γlk $$ [Hlk]
  · iunfold memKey; iexact Hlk
  ihave Hok : memKey (GF := GF) γok $$ [Hok]
  · iunfold memKey; iexact Hok
  ihave Hak : memKey (GF := GF) γak $$ [Hak]
  · iunfold memKey; iexact Hak
  imod sync.init_Mutex (memstorageInv «$r0_ptr» ⟨γh, γd, γe, γsn, γsw, γlk, γok, γak⟩) ⊤
    («$r0_ptr».[MemoryStorage, go!"Mutex"])
    $$ Mutex [Hd1 Hlk hardState ents cs_firstIndex cs_lastIndex cs_entries cs_term
      cs_snapshot Hsl_cap] with #Hmu
  · inext
    unfold memstorageInv
    iexists memStorEmpty
    isplitl [Hd1 Hlk]
    · unfold memInvGhost
      iexists [memStorEmpty]
      iframe Hd1 Hhlb
      isplitr
      · ipureintro; rfl
      iexact Hlk
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
  iapply wp_fupd
  wp_apply wp_EnsureSnapshot null none $$ [] as %sp ⟨Hsp, -⟩
  · simp only [snapOpt]; ipureintro; trivial
  simp only [Option.getD_none]
  ihave Hsp := ownSnapW_E $$ Hsp
  ihave Hsp := ownSnapE_weaken $$ Hsp
  -- (D17d) the snapshot's invariant, the snapshot at home; the quarters
  ihave Hsw : ghostVar γsw ((1 : Qp).half + (1 : Qp).half) (0 : Nat) $$ [Hsw]
  · rw [Qp.half_add_half]; iexact Hsw
  icases ghostVar_split γsw _ _ _ $$ Hsw with ⟨Hsw1, Hsw2⟩
  ihave Hsn : ghostVar γsn ((1 : Qp).half + (memQ + memQ)) (snapPart memStorEmpty) $$ [Hsn]
  · rw [Qp.half_add_half, Qp.half_add_half]; iexact Hsn
  icases ghostVar_split γsn _ _ _ $$ Hsn with ⟨Hsnh, Hsnq⟩
  icases ghostVar_split γsn _ _ _ $$ Hsnq with ⟨Hsno, Hsna⟩
  imod inv_alloc memSnapN ⊤ (memSnapInv «$r0_ptr» ⟨γh, γd, γe, γsn, γsw, γlk, γok, γak⟩)
    $$ [Hsw1 Hsw2 snapshot Hsp Hsnh] with #Hsinv
  · inext
    iunfold memSnapInv
    iexists (0 : Nat)
    iframe Hsw1
    ileft
    iframe Hsw2
    isplitr
    · ipureintro; rfl
    iunfold memSnapHome
    iexists memStorEmpty
    iframe Hsnh
    iunfold memSnapOwn
    iexists sp, _
    iframe snapshot Hsp
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  imodintro
  iapply HΦ $$ %«$r0_ptr» %(⟨γh, γd, γe, γsn, γsw, γlk, γok, γak⟩ : MemStorNames)
  isplitr [HhardState cs_initialState Hak Hsna]
  rotate_left
  isplitl [HhardState cs_initialState]
  · unfold memStorMeta
    iexists _, null
    simp only [named]
    iframe Hpkg Hmu HhardState cs_initialState
    iapply hsOpt_null
  · unfold memSnapTok
    simp only [named]
    iframe Hpkg Hmu Hsinv Hak Hsna
  unfold ownMemoryStorage memView memSnapShare
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
  iframe Hsinv Hok Hsno
  ipureintro; simp only [memStorEmpty, List.length_nil]; word

end proof

end EtcdGrove
end Perennial
