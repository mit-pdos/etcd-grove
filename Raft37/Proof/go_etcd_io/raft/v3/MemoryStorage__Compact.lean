/- `MemoryStorage.Compact` (`storage.go:254`), proved 2026-10-12 (Lean-first). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

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

theorem MemoryStorage.Compact.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Compact.spec (GF := GF) (hG := hG) := by
  intro ms γs σ ci ecomp Hidle Hpre
  wp_start as ⟨Hms, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- with nothing pending the contents are the owner's state
  icases memView_agree γs σ σp $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  have Hσp : σp = σ := Hvw.2.2.2 Hidle
  subst Hσp
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: σp.ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0i, Hd0t⟩ := Hdummy
  rw [Hd0i]
  wp_if_destruct
  · -- `ErrCompacted`: nothing changes
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f
      Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp
      iframe Hgs_inv
      isplitl
      · iexists hp, es, dummy, nfi, nli, nen, nte, nsn
        iframe # ∗
        ipureintro; exact ⟨Hd0i, Hd0t⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨Hif, rfl⟩
    unfold ownMemoryStorage
    iframe # ∗
    ipureintro; exact Hbounded
  obtain ⟨Hle, Hidx⟩ := Hpre (by omega)
  ihave Hf : memstorageFields ms σp $$ [HhardState Hents_f Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, nfi, nli, nen, nte, nsn
    iframe # ∗
    ipureintro; exact ⟨Hd0i, Hd0t⟩
  wp_apply wp_MemoryStorage_lastIndex ms σp Hpb_inv $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_if_destruct
  · exfalso; word
  iunfold memstorageFields at Hf
  icases Hf with ⟨%hp1, %es1, %dummy1, %nfi1, %nli1, %nen1, %nte1, %nsn1, Hf⟩
  iNamedSuffix Hf "_1"
  obtain ⟨Hd1i, Hd1t⟩ := Hdummy_1
  icases Hents_1 with #Hents_1
  clear Hcl Hl0
  ihave %Hcl := entsRO_cons_len $$ Hents_1
  wp_auto
  wp_apply wp_slice_make3 (V := Loc) (W64 1) _ as %sl ⟨Hsl, Hsl_cap, %Hslcap⟩
  -- the entry at `ci`: `ms.ents[i]`, `i = ci - offset ≥ 1`
  have Hk : sint.Z (ci - σp.prev.index') = uint.Z ci - uint.Z σp.prev.index' := by word
  have Hkl : (uint.Z ci - uint.Z σp.prev.index' - 1).toNat < σp.ents.length := by omega
  obtain ⟨e, He⟩ : ∃ e, σp.ents[(uint.Z ci - uint.Z σp.prev.index' - 1).toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem Hkl⟩
  have He' : (dummy1 :: σp.ents)[(sint.Z (ci - σp.prev.index')).toNat]? = some e := by
    rw [Hk, show (uint.Z ci - uint.Z σp.prev.index').toNat =
      (uint.Z ci - uint.Z σp.prev.index' - 1).toNat + 1 by omega]
    exact He
  have Hei := Hidx e He
  ihave #Hents1 := Hents_1
  iunfold entsRO at Hents1
  iunfold entsPts at Hents1
  icases Hents1 with ⟨%ls1, #Hls1, #Hbig1⟩
  icases entsBig_lookup ls1 (dummy1 :: σp.ents) _ e He' $$ Hbig1 with ⟨%lk, %Hlk, #Hek⟩
  ihave %Hbl1 := entsBig_length $$ Hbig1
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (ci - σp.prev.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hlk
  wp_apply wp_GetIndex.1 lk DFrac.discard e $$ [Hek] with -
  · iframe Hek
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (ci - σp.prev.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
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
  icases (ownSlice_slice (ci - σp.prev.index' + W64 1) es1.len es1 DFrac.discard
    ls1 ⟨by word, by word, by word⟩).1 $$ Hls1 with ⟨-, #Hrest, -⟩
  wp_apply wp_slice_append (V := Loc) $$ [$Hsl $Hsl_cap $Hrest] as %es' ⟨Hes', Hes'_cap, -⟩
  imod ownSlice_persist $$ Hes' with #Hes'
  -- the new state: the boundary at `ci` and its term, the entries after it
  have Hterm : termAt σp.prev σp.ents ci = some e.Term' := by
    have Hne : ¬ uint.Z ci = uint.Z σp.prev.index' := by omega
    unfold termAt
    simp only [Hne, ↓reduceIte, He]
    rfl
  have HE : subslice (sint.nat (ci - σp.prev.index' + W64 1)) (sint.nat es1.len)
      (dummy1 :: σp.ents) = (memStorCompacted σp ci e.Term').ents := by
    simp only [subslice, memStorCompacted]
    rw [List.take_of_length_le (by simp only [List.length_cons]; word)]
    rw [show sint.nat (ci - σp.prev.index' + W64 1) =
      (uint.Z ci - uint.Z σp.prev.index').toNat + 1 by word]
    rfl
  ihave #Hb2 := entsBig_subslice (sint.nat (ci - σp.prev.index' + W64 1)) (sint.nat es1.len)
    ls1 (dummy1 :: σp.ents) $$ Hbig1
  ihave #Hes2 : entsRO es' (d' :: subslice (sint.nat (ci - σp.prev.index' + W64 1))
      (sint.nat es1.len) (dummy1 :: σp.ents)) $$ []
  · iunfold entsRO; iunfold entsPts
    iexists («$r0_ptr» :: subslice (sint.nat (ci - σp.prev.index' + W64 1)) (sint.nat es1.len) ls1)
    isplitr
    · iExactEq Hes'
      rfl
    iapply (BigSepL2.bigSepL2_cons).2
    iframe Hd' Hb2
  have Hpb' : uint.Z (memStorCompacted σp ci e.Term').prev.index' +
      ((memStorCompacted σp ci e.Term').ents.length : Int) < 2^61 := by
    simp only [memStorCompacted, List.length_drop]
    omega
  imod memView_set γs σp σp (memStorCompacted σp ci e.Term') Hidle (by simp [memStorCompacted, Hidle])
    $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_1
    Hents_f_1 Hes'_cap Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1]
  · inext
    unfold memstorageInv memstorageFields
    iexists memStorCompacted σp ci e.Term'
    iframe Hgs_inv
    isplitl
    · iexists hp1, es', d', nfi1, nli1, nen1, nte1, nsn1
      rw [← HE]
      iframe # ∗
      ipureintro
      exact ⟨by simp [d', memStorCompacted, Hei], rfl⟩
    ipureintro; exact Hpb'
  iapply HΦ
  iright
  iexists e.Term'
  isplitr
  · ipureintro; exact ⟨by omega, Hterm, rfl⟩
  ihave Hsn := memSnapOwn_congr ms σp (memStorCompacted σp ci e.Term') rfl rfl rfl $$ Hsn
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro; exact Hpb'

end proof

end EtcdGrove
end Perennial
