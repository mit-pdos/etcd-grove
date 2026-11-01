/- `NewMemoryStorage` (`storage.go:113`; U8 v2 step 3): the fields at the dummy alone, the ghost
state of `MemStorNames` (the map `{0 ↦ e₀}` with the dummy frozen, the end at `1`, the compaction
point `0` justified, the empty stored snapshot, the keys), the mutex allocated around them, and the
snapshot `EnsureSnapshot(nil)` makes, the allocation's fuel. -/
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The lock's knowledge at the start: the dummy `0` alone, the map `{0 ↦ e₀}`. -/
theorem memOk_new :
    MemOk (entryID.mk (W64 0) (W64 0)) [] ((∅ : GMap Nat EntryM).insert 0 (zero_val EntryM))
      memSnapEmpty := by
  refine ⟨by simp, fun i hi => ?_, fun i h1 h2 => ?_, by simp [memSnapEmpty], by simp [memSnapEmpty],
    fun j e h => by simp at h⟩
  · simp only [List.length_nil] at hi
    rw [GMap.lookup_insert_ne _ _ (by simp at hi ⊢; omega)]
    exact GMap.lookup_empty _
  · simp at h1 h2; omega

theorem NewMemoryStorage.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG)) :
    NewMemoryStorage.spec (GF := GF) (hG := hG) := by
  wp_start as #Hinit
  wp_auto
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
  -- the lock's half of `hardState` and its counters
  icases (typedPointsto_half_split _ _ 1).1 $$ hardState with ⟨hardState, HhardState⟩
  iStructNamedPrefix callStats "cs_"
  imod ownSlice_persist $$ Hsl with #Hsl
  -- the ghost state
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := EntryM) with ⟨%γlog, Hlog⟩
  imod ghost_map_insert_persist 0 (zero_val EntryM) (GMap.lookup_empty _) $$ Hlog with ⟨Hlog, #Hd0⟩
  imod ghostVar_alloc (GF := GF) (1 : Nat) with ⟨%γen, Hen⟩
  icases (ghostVar_split_half γen 1 (1 : Nat)).1 $$ Hen with ⟨Hen1, Hen2⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γek, Hek⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γlk, Hlk⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γhk, Hhk⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcp, Hcp, -⟩
  imod mono_list_own_alloc (GF := GF) [0] with ⟨%γjc, Hjc, #Hjlb⟩
  imod ghostVar_alloc (GF := GF) memSnapEmpty with ⟨%γsx, Hsx⟩
  icases (ghostVar_split_half γsx 1 memSnapEmpty).1 $$ Hsx with ⟨Hsx2, Hsx3⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γsl, Hsl0, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γpr, Hpr, -⟩
  let γs : MemStorNames := ⟨γlog, γen, γek, γcp, γjc, γsx, γlk, γhk, γsl, γpr⟩
  imod sync.init_Mutex (memstorageInv «$r0_ptr» γs) ⊤ («$r0_ptr».[MemoryStorage, go!"Mutex"])
    $$ Mutex [hardState ents cs_firstIndex cs_lastIndex cs_entries cs_term cs_snapshot Hsl_cap
      Hlog Hen1 Hcp Hsx2 Hsl0 Hlk] with #Hmu
  · inext
    unfold memstorageInv
    iexists entryID.mk (W64 0) (W64 0), [], (∅ : GMap Nat EntryM).insert 0 (zero_val EntryM),
      memSnapEmpty
    simp only [named]
    isplitl [hardState ents cs_firstIndex cs_lastIndex cs_entries cs_term cs_snapshot Hsl_cap]
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
        rw [show (memPhys (entryID.mk (W64 0) (W64 0)) []).ents = [] from rfl]
        iapply entsBig_nil
      ipureintro; exact ⟨rfl, rfl⟩
    have h0 : uint.nat (W64 0) = 0 := rfl
    simp only [h0, List.length_nil, Nat.zero_add, Nat.add_zero]
    iframe Hlog
    isplitl [Hen1]
    · iexact Hen1
    isplitl [Hcp]
    · iexact Hcp
    isplitr
    · iunfold memCompJust
      iexists [0]
      iframe Hjlb
      ipureintro; simp
    isplitl [Hsx2]
    · iexact Hsx2
    isplitl [Hsl0]
    · rw [show uint.nat memSnapEmpty.Metadata'.Index' = 0 from rfl]; iexact Hsl0
    isplitr
    · ileft; ipureintro; trivial
    isplitl [Hlk]
    · iunfold memKey; iexact Hlk
    isplitr
    · iexists zero_val EntryM
      iframe Hd0
      ipureintro; rfl
    isplitr
    · ileft; ipureintro; rfl
    ipureintro; exact memOk_new
  iapply wp_fupd
  wp_apply wp_EnsureSnapshot.1 null none $$ [] as %sp ⟨Hsp, -⟩
  · simp only [snapOpt]; ipureintro; trivial
  ihave Hsp := ownSnapS_W _ _ _ $$ Hsp
  simp only [Option.getD_none]
  ihave Hsp := ownSnapW_E $$ Hsp
  ihave Hsp := ownSnapE_weaken $$ Hsp
  imodintro
  iapply HΦ $$ %«$r0_ptr» %γs
  isplitr
  · iunfold memStorLock; iframe Hpkg Hmu
  isplitr
  · iunfold memLog
    simp only [memLogL]
    iframe Hd0
    ipureintro; right; simp
  isplitl [Hen2 Hek]
  · iunfold memEnd; iunfold memKey; iframe
  isplitl [Hpr]
  · iunfold memSnapNone; iexact Hpr
  isplitl [HhardState cs_initialState]
  · unfold memStorMeta
    iexists _, null
    simp only [named]
    iframe Hpkg Hmu HhardState cs_initialState
    iapply hsOpt_null
  iunfold memStorFresh
  iframe Hjc
  isplitl [Hhk]
  · iunfold memKey; iexact Hhk
  iexists sp
  simp only [memSnapEmpty] at *
  iframe snapshot Hsp Hsx3

end proof

end EtcdGrove
end Perennial
