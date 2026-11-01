/- `MemoryStorage.Compact` (`storage.go:271`; U8 v2 step 3). At or below the compaction point:
`ErrCompacted`, the lock's compaction point and its registration giving `memCompacted`. Past it, the
caller's frozen entry at `x` is in the map, so below the end (no panic), and is the physical entry
there (`MemOk`), numbered `x`: the new dummy is the caller's frozen entry; the map and the end are
unchanged, the compaction point moves to `x` (registered with `J.B x`). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

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

theorem MemoryStorage.Compact.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Compact.spec (GF := GF) (hG := hG) := by
  have HN : ↑memStorN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  intro ms γs J ci ecomp
  wp_start as ⟨#Hsi, #Hpre, #HB, #Hlbx, #Herr⟩
  iunfold memStorInvP at Hsi
  icases Hsi with ⟨#Hlock, #HB0, #Hjinv⟩
  ihave #Hsi : memStorInvP ms γs J $$ []
  · iunfold memStorInvP; iframe Hlock HB0 Hjinv
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
  icases Hinv with ⟨%p, %ents, %M, %sv0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- `ci` is at most the stored snapshot's index
  ihave %Hxs : ⌜uint.nat ci ≤ uint.nat sv0.Metadata'.Index'⌝ $$ [Hsl_inv]
  · iunfold memSnapLb at Hlbx
    icases Hlbx with ⟨#Hlb, -⟩
    icases monoNatLbOwn_valid _ _ _ _ $$ Hsl_inv Hlb with %H
    ipureintro; exact H.2
  ihave #Hcplb := monoNatLbOwn_get _ _ _ $$ Hcp_inv
  have Hok := Hok_inv
  have Hpb : uint.Z (memPhys p ents).prev.index' + ((memPhys p ents).ents.length : Int) < 2^61 := by
    simp only [memPhys]; have := Hok.1; word
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: (memPhys p ents).ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  have Hd0i : dummy.Index' = p.index' := Hdummy.1
  have Hd0t : dummy.Term' = p.term' := Hdummy.2
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  rw [Hd0i]
  wp_if_destruct
  · -- `ErrCompacted`: nothing changes
    have Hle : uint.nat ci ≤ uint.nat p.index' := by word
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hents Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog_inv Hen_inv Hcp_inv
      Hsx_inv Hsl_inv Hlk_inv]
    · unfold memstorageInv
      iexists p, ents, M, sv0
      simp only [named]
      iframe # ∗
      isplitl
      · unfold memstorageFields
        iexists hp, es, dummy, _, _, _, _, _
        simp only [named]
        iframe # ∗
        ipureintro; exact ⟨Hd0i, Hd0t⟩
      ipureintro; exact Hok_inv
    iapply HΦ
    isplitr
    · ipureintro; right; rfl
    iunfold memCompacted
    iright
    isplitr
    · iapply monoNatLbOwn_le _ Hle $$ Hcplb
    iunfold memCompJust at Hcj_inv
    icases Hcj_inv with ⟨%L, #HL, %HLm⟩
    iexists L
    iframe HL
    ipureintro; exact ⟨_, HLm, Hle⟩
  -- past the compaction point: the caller's frozen entry at `x`
  have Hgt : uint.nat p.index' < uint.nat ci := by word
  icases Hpre with (⟨%e, #Hel⟩ | #Hc)
  rotate_left
  · iexfalso
    iunfold memCompacted at Hc
    icases Hc with (%H | ⟨#Hlb, -⟩)
    · ipureintro; omega
    icases monoNatLbOwn_valid _ _ _ _ $$ Hcp_inv Hlb with %H
    ipureintro; omega
  iunfold memLog at Hel
  icases Hel with ⟨Hel, -⟩
  icases memLogL_lookup γs.log (uint.nat ci) DFrac.discard [e] 0 e rfl $$ Hel with ⟨#Hex, -⟩
  icases ghost_map_lookup $$ Hlog_inv Hex with %HMe
  simp only [Nat.add_zero] at HMe
  have Hlt : uint.nat ci < uint.nat p.index' + 1 + ents.length := by
    rcases Nat.lt_or_ge (uint.nat ci) (uint.nat p.index' + 1 + ents.length) with h | h
    · exact h
    · rw [Hok.2.1 _ h] at HMe; cases HMe
  have HeE : ents[uint.nat ci - uint.nat p.index' - 1]? = some e := by
    rw [← Hok.2.2.1 _ Hgt Hlt]; exact HMe
  have Hei : uint.nat e.Index' = uint.nat ci := by
    have := Hok.2.2.2.2.2 _ e HeE; omega
  ihave Hf : memstorageFields ms (memPhys p ents) $$ [HhardState Hents_f Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, nfi, nli, nen, nte, nsn
    simp only [named]
    iframe # ∗
    ipureintro; exact Hdummy
  wp_apply wp_MemoryStorage_lastIndex ms (memPhys p ents) Hpb $$ [$Hf] as %li ⟨%Hli, Hf⟩
  simp only [memPhys] at Hli
  wp_if_destruct
  · exfalso; word
  iunfold memstorageFields at Hf
  icases Hf with ⟨%hp1, %es1, %dummy1, %nfi1, %nli1, %nen1, %nte1, %nsn1, Hf⟩
  iNamedSuffix Hf "_1"
  have Hd1i : dummy1.Index' = p.index' := Hdummy_1.1
  icases Hents_1 with #Hents_1
  ihave %Hcl1 := entsRO_cons_len $$ Hents_1
  have Hcl1' : ents.length + 1 = sint.Z es1.len := Hcl1.2
  wp_auto
  wp_apply wp_slice_make3 (V := Loc) (W64 1) _ as %sl ⟨Hsl, Hsl_cap, %Hslcap⟩
  -- the entry at `ci`: `ms.ents[i]`, `i = ci - offset ≥ 1`
  have Hk : sint.Z (ci - p.index') = uint.Z ci - uint.Z p.index' := by word
  have He' : (dummy1 :: (memPhys p ents).ents)[(sint.Z (ci - p.index')).toNat]? = some e := by
    rw [Hk, show (uint.Z ci - uint.Z p.index').toNat =
      (uint.nat ci - uint.nat p.index' - 1) + 1 by word]
    exact HeE
  ihave #Hents1 := Hents_1
  iunfold entsRO at Hents1
  iunfold entsPts at Hents1
  icases Hents1 with ⟨%ls1, #Hls1, #Hbig1⟩
  icases entsBig_lookup ls1 (dummy1 :: (memPhys p ents).ents) _ e He' $$ Hbig1 with ⟨%lk, %Hlk, #Hek⟩
  ihave %Hbl1 := entsBig_length $$ Hbig1
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (ci - p.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hlk
  wp_apply wp_GetIndex.1 lk DFrac.discard e $$ [Hek] with -
  · iframe Hek
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (ci - p.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hlk
  wp_apply wp_GetTerm.1 lk DFrac.discard e $$ [Hek] with -
  · iframe Hek
  -- the fresh dummy entry at `ci`, frozen
  imod cellRO_alloc $$ «$v0» with #cI
  imod cellRO_alloc $$ «$v1» with #cT
  let d' : EntryM := EntryM.mk e.Term' e.Index' (zero_val raftpb.EntryType) []
  imod entOwn_of_struct «$r0_ptr» (raftpb.Entry.mk zeroValDef «$v1_ptr» «$v0_ptr» null slice.nil slice.nil 0) d' ⊤ rfl $$ [«$r0»] with Hd'
  · iframe «$r0» cT cI
    isplitl []; · iapply cellRO_null
    iapply ownSlice_nil
  imod entOwn_freeze $$ Hd' with #Hd'
  ihave %Hsllen := ownSlice_len $$ Hsl
  simp only [List.length_replicate] at Hsllen
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_store_slice_index sl (sint.Z (W64 0)) _ «$r0_ptr» $$ [Hsl] with Hsl
  · iframe Hsl; ipureintro; simp only [List.length_replicate]; constructor <;> word
  wp_auto
  ihave %Hwf1 := ownSlice_wf $$ Hls1
  -- `ms.ents[i+1:]`, the entries after `ci`
  rw [ite_eq_left ⟨by word, by word, Hwf1.2⟩]
  icases (ownSlice_slice (ci - p.index' + W64 1) es1.len es1 DFrac.discard
    ls1 ⟨by word, by word, by word⟩).1 $$ Hls1 with ⟨-, #Hrest, -⟩
  wp_apply wp_slice_append (V := Loc) $$ [$Hsl $Hsl_cap $Hrest] as %es' ⟨Hes', Hes'_cap, -⟩
  imod ownSlice_persist $$ Hes' with #Hes'
  have HE : subslice (sint.nat (ci - p.index' + W64 1)) (sint.nat es1.len)
      (dummy1 :: (memPhys p ents).ents) = ents.drop (uint.nat ci - uint.nat p.index') := by
    simp only [subslice, memPhys]
    rw [List.take_of_length_le (by simp only [List.length_cons]; word)]
    rw [show sint.nat (ci - p.index' + W64 1) = (uint.nat ci - uint.nat p.index') + 1 by word]
    rfl
  ihave #Hb2 := entsBig_subslice (sint.nat (ci - p.index' + W64 1)) (sint.nat es1.len)
    ls1 (dummy1 :: (memPhys p ents).ents) $$ Hbig1
  ihave #Hes2 : entsRO es' (d' :: subslice (sint.nat (ci - p.index' + W64 1))
      (sint.nat es1.len) (dummy1 :: (memPhys p ents).ents)) $$ []
  · iunfold entsRO; iunfold entsPts
    iexists («$r0_ptr» :: subslice (sint.nat (ci - p.index' + W64 1)) (sint.nat es1.len) ls1)
    isplitr
    · iExactEq Hes'
      rfl
    iapply (BigSepL2.bigSepL2_cons).2
    iframe Hd' Hb2
  -- the new state: the compaction point at `ci` (registered), the entries after it
  imod mono_nat_own_update (uint.nat ci) (by omega) $$ Hcp_inv with ⟨Hcp, #Hcplb'⟩
  imod memCompJust_register ms γs J (uint.nat ci) ⊤ HN $$ Hsi HB with #Hcjn
  have Hok' : MemOk (entryID.mk e.Term' ci) (ents.drop (uint.nat ci - uint.nat p.index')) M sv0 := by
    have H1 := Hok.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_drop]; omega
    · intro i hi
      simp only [List.length_drop] at hi
      exact Hok.2.1 i (by omega)
    · intro i h1 h2
      simp only [List.length_drop] at h1 h2 ⊢
      rw [List.getElem?_drop, Hok.2.2.1 i (by omega) (by omega)]
      congr 1; omega
    · exact Hxs
    · have := Hok.2.2.2.2.1
      simp only [List.length_drop]; omega
    · intro j e' h
      rw [List.getElem?_drop] at h
      have := Hok.2.2.2.2.2 _ _ h
      simp only
      omega
  have Hend : uint.nat p.index' + 1 + ents.length =
      uint.nat (entryID.mk e.Term' ci).index' + 1 +
        (ents.drop (uint.nat ci - uint.nat p.index')).length := by
    simp only [List.length_drop]; omega
  have Hd'i : d'.Index' = (entryID.mk e.Term' ci).index' := by
    simp only [d']
    have := Hei
    word
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState_1 Hents_f_1 Hes'_cap Hcs_firstIndex_1
    Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1 Hlog_inv Hen_inv Hcp Hsx_inv Hsl_inv Hlk_inv]
  · unfold memstorageInv
    inext
    iexists entryID.mk e.Term' ci, ents.drop (uint.nat ci - uint.nat p.index'), M, sv0
    simp only [named]
    isplitl [HhardState_1 Hents_f_1 Hes'_cap Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1
      Hcs_term_1 Hcs_snapshot_1]
    · unfold memstorageFields
      iexists hp1, es', d', nfi1, nli1, nen1, nte1, nsn1
      simp only [named]
      iframe
      isplitr
      · iExactEq Hes2
        rw [HE]; rfl
      ipureintro; exact ⟨Hd'i, rfl⟩
    isplitl [Hlog_inv]
    · iexact Hlog_inv
    isplitl [Hen_inv]
    · iExactEq Hen_inv
      rw [Hend]
    iframe Hcp Hsx_inv Hsl_inv Hsn_inv Hlk_inv Hcjn
    isplitr
    · iexists e
      isplitl []
      · iExactEq Hex
        simp only [Nat.add_zero]
      ipureintro; rfl
    isplitr
    · iexact Hsf_inv
    ipureintro; exact Hok'
  iapply HΦ
  isplitr
  · ipureintro; left; rfl
  iunfold memCompacted
  iright
  iframe Hcplb'
  iunfold memCompJust at Hcjn
  icases Hcjn with ⟨%L, #HL, %HLm⟩
  iexists L
  iframe HL
  ipureintro; exact ⟨_, HLm, Nat.le_refl _⟩

end proof

end EtcdGrove
end Perennial
