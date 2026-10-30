/-
Port of election_proof/proof_MemoryStorage__Term.v. U8 v2 step 3 (2026-10-29): over the lock's
invariant; the caller's range is in the lock's map, so `i0` is below the end (no `ErrUnavailable`),
and the map's entry at `i0` is the physical one (the frozen dummy at the compaction point).
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Proof.go_etcd_io.raft.v3.LemmasEnts

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

theorem MemoryStorage.Term.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Term.spec (GF := GF) (hG := hG) := by
  intro ms γs k dq es i0 ec
  wp_start as ⟨#Hlock, Hlogr, %Hrange, #Hec⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the caller's range is in the map: `i0` holds its entry `e`, so it is below the end
  iunfold memLog at Hlogr
  icases Hlogr with ⟨Hlogr, %Hlb⟩
  icases memLogL_auth _ _ _ _ _ _ $$ Hlog_inv Hlogr with %HM
  obtain ⟨Hk, Hi0⟩ := Hrange
  obtain ⟨e, He⟩ : ∃ e, es[uint.nat i0 - k]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have HMi : M.lookup (uint.nat i0) = some e := by
    have := HM _ e He
    rwa [show k + (uint.nat i0 - k) = uint.nat i0 by omega] at this
  have Hi0e : uint.nat i0 < uint.nat p.index' + 1 + ents.length := by
    refine Nat.lt_of_not_le fun h => ?_
    have := Hok_inv.2.1 _ h
    rw [this] at HMi
    cases HMi
  -- the frozen dummy: the map's entry at the compaction point has the dummy's term
  icases Hd0_inv with ⟨%e0, #He0g, %He0t⟩
  icases ghost_map_lookup $$ Hlog_inv He0g with %HMc
  ihave #Hd0_inv : (∃ (e0 : EntryM), (uint.nat p.index') ↪[γs.log]□ e0 ∗ ⌜e0.Term' = p.term'⌝) $$ []
  · iexists e0
    iframe He0g
    ipureintro; exact He0t
  -- the compaction point is compacted
  ihave #Hcomp : memCompacted γs (uint.nat p.index') $$ [Hcp_inv]
  · ihave #Hlb := monoNatLbOwn_get _ _ _ $$ Hcp_inv
    iunfold memCompJust at Hcj_inv
    icases Hcj_inv with ⟨%L, #HL, %HcL⟩
    iunfold memCompacted
    iright
    iframe Hlb
    iexists L
    iframe HL
    ipureintro; exact ⟨_, HcL, Nat.le_refl _⟩
  have Hb := Hok_inv.1
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es', %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es' (dummy :: (memPhys p ents).ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es' (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  simp only [memPhys] at Hd0 Hd1 Hcl
  wp_if_destruct
  · -- below the compaction point: `ErrCompacted`
    have Hlt : uint.Z i0 < uint.Z p.index' := by rw [Hd0] at Hif; word
    try wp_auto
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog_inv Hen_inv Hcp_inv Hsx_inv Hsl_inv Hlk_inv]
    · unfold memstorageInv
      iexists p, ents, M, sv
      simp only [named]
      iframe # ∗
      isplitl
      · unfold memstorageFields
        iexists hp, es', dummy, _, _, _, _, _
        simp only [memPhys]
        iframe # ∗
        ipureintro; exact ⟨Hd0, Hd1⟩
      ipureintro; exact Hok_inv
    iapply HΦ
    isplitl [Hlogr]
    · iunfold memLog
      iframe Hlogr
      ipureintro; exact Hlb
    iright
    isplitl []
    · ipureintro; rfl
    iapply memCompacted_mono γs _ _ (by word) $$ Hcomp
  have Hge : uint.Z p.index' ≤ uint.Z i0 := by rw [Hd0] at Hif; word
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; word
  have Hn : sint.Z (i0 - dummy.Index') = uint.Z i0 - uint.Z p.index' := by
    rw [Hd0]; word
  rw [Hn]
  have Hlt : (uint.Z i0 - uint.Z p.index').toNat < (dummy :: (memPhys p ents).ents).length := by
    simp only [List.length_cons, memPhys]; word
  obtain ⟨e', He'⟩ : ∃ e', (dummy :: (memPhys p ents).ents)[(uint.Z i0 - uint.Z p.index').toNat]? = some e' :=
    ⟨_, List.getElem?_eq_getElem Hlt⟩
  icases entsRO_lookup es' (dummy :: (memPhys p ents).ents) _ e' He' $$ Hents
    with ⟨%ls1, %l1, #Hls1, #He1, %Hl1⟩
  have H1 : 0 ≤ uint.Z i0 - uint.Z p.index' ∧
      uint.Z i0 - uint.Z p.index' < sint.Z es'.len := by
    constructor <;> word
  simp only [H1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index es' (uint.Z i0 - uint.Z p.index') ls1 DFrac.discard l1 (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hl1.1
  wp_apply wp_GetTerm.1 l1 DFrac.discard e' $$ [He1] with -
  · iframe He1
  -- the physical entry's term is the range's
  have Hterm : e.Term' = e'.Term' := by
    by_cases Hi : uint.Z i0 = uint.Z p.index'
    · have H0 : (uint.Z i0 - uint.Z p.index').toNat = 0 := by omega
      rw [H0] at He'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at He'
      subst He'
      have Hin : uint.nat i0 = uint.nat p.index' := by word
      rw [Hin, HMc] at HMi
      cases HMi
      rw [He0t, Hd1]
    · have HS : (uint.Z i0 - uint.Z p.index').toNat =
          (uint.nat i0 - uint.nat p.index' - 1) + 1 := by word
      rw [HS] at He'
      simp only [List.getElem?_cons_succ, memPhys] at He'
      have := Hok_inv.2.2.1 (uint.nat i0) (by word) Hi0e
      rw [HMi, He'] at this
      cases this
      rfl
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog_inv Hen_inv Hcp_inv Hsx_inv Hsl_inv Hlk_inv]
  · unfold memstorageInv
    iexists p, ents, M, sv
    simp only [named]
    iframe # ∗
    isplitl
    · unfold memstorageFields
      iexists hp, es', dummy, _, _, _, _, _
      simp only [memPhys]
      iframe # ∗
      ipureintro; exact ⟨Hd0, Hd1⟩
    ipureintro; exact Hok_inv
  iapply HΦ
  isplitl [Hlogr]
  · iunfold memLog
    iframe Hlogr
    ipureintro; exact Hlb
  ileft
  ipureintro
  refine ⟨rfl, ?_⟩
  rw [He]
  simp only [Option.map_eq_map, Option.map_some, Hterm]

end proof

end EtcdGrove
end Perennial
