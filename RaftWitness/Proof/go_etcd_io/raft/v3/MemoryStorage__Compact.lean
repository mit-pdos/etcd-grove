/- `MemoryStorage.Compact` (`storage.go:254`), proved 2026-10-12 (Lean-first). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetSubterm
public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

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
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetSubterm : raftpb.Entry.GetSubterm.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Compact.spec (GF := GF) (hG := hG) := by
  intro ms γs σt x ci ecomp Hpre
  wp_start as ⟨Htok, #Hfw, #Herr⟩
  iunfold memSnapTok at Htok
  icases Htok with ⟨#Hinit, #Hmu, #Hsinv, Hak, Hsvt, Hcbt⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σL, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- (D19i part 1) the floor's witness: the contents hold entries up to `x`, within the floor;
  -- the lock's boundary and snapshot are the token's
  icases memFloorTok_last ms γs σL x $$ Hfw Hgs_inv with ⟨%Hxl, Hgs_inv⟩
  ihave #Hflx := memFloorTok_flLb ms γs x $$ Hfw
  iunfold memInvGhost at Hgs_inv
  icases Hgs_inv with ⟨%Dl, Hd_inv, #Hlb_inv, %HD, Hlk_inv⟩
  have HidxL : PlogWf σL.prev σL.ents := (HD.2.2 σL (List.mem_of_getLast? HD.1)).2.2
  iunfold memCutInv at Hcut_inv
  iNamed Hcut_inv
  icases ghostVar_agree γs.cb _ _ _ _ $$ Hcb Hcbt with %Hcbe
  subst Hcbe
  icases ghostVar_agree γs.sn _ _ _ _ $$ Hsq Hsvt with %HagS
  obtain ⟨HS1, -, -⟩ := snapPart_inj HagS
  have Hlast := memCut_stLast Hcok.1
  have Hcok1 := Hcok.1
  have Hpbf : uint.Z (memCut σL σt.prev).prev.index' + ((memCut σL σt.prev).ents.length : Int) <
      2^61 := by
    unfold EtcdGrove.stLast at Hlast; omega
  have HlastF : uint.Z (memCut σL σt.prev).prev.index' + ((memCut σL σt.prev).ents.length : Int) =
      stLast σL := by
    unfold EtcdGrove.stLast at Hlast; exact Hlast
  have HprevF : (memCut σL σt.prev).prev = σt.prev := rfl
  have Hpb_inv0 := Hpb_inv
  generalize Hσf : memCut σL σt.prev = σp at Hpbf HlastF HprevF ⊢
  have Hpb_inv := Hpbf
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
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hd_inv Hlk_inv HhardState Hents_f
      Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcb Hbd Hsq]
    · inext
      unfold memstorageInv memstorageFields
      iexists σL, σt.prev
      isplitl [Hd_inv Hlk_inv]
      · unfold memInvGhost
        iexists Dl
        iframe Hd_inv Hlb_inv Hlk_inv
        ipureintro; exact HD
      rw [Hσf]
      isplitl [HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
      · iexists hp, es, dummy, nfi, nli, nen, nte, nsn
        iframe # ∗
        ipureintro; exact ⟨Hd0i, Hd0t⟩
      isplitr
      · ipureintro; exact Hpb_inv0
      iunfold memCutInv
      iexists S
      iframe Hcb Hbd Hcfl Hsq Hsrel
      ipureintro; exact ⟨Hcok, Hccap⟩
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rw [HprevF] at Hif; exact ⟨Hif, rfl⟩
    unfold memSnapTok
    iframe # ∗
  have Hgt : uint.Z σt.prev.index' < uint.Z ci := by rw [HprevF] at Hif; omega
  obtain ⟨Hle0, Hsle, Hcap⟩ := Hpre Hgt
  have Hle : uint.Z ci ≤ uint.Z σp.prev.index' + (σp.ents.length : Int) := by omega
  -- the entry at `ci` is numbered `ci`: the contents keep their entries numbered by position
  have Hidx : ∀ e, σp.ents[(uint.Z ci - uint.Z σp.prev.index' - 1).toNat]? = some e →
      e.Index' = ci := by
    intro e He
    rw [← Hσf] at He
    simp only [memCut, List.getElem?_drop] at He
    have := HidxL _ e He
    have h1 := Hcok1.1
    apply uint_Z_inj.1
    push_cast at this
    omega
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
  -- the fresh dummy entry at `ci`, of `e`'s subterm (2026-10-19, witness support): made with
  -- none, stored, given a non-zero subterm, then frozen
  imod cellRO_alloc $$ «$v0» with #cI
  imod cellRO_alloc $$ «$v1» with #cT
  let d' : EntryM := EntryM.mk e.Term' e.Index' (zero_val raftpb.EntryType) [] e.Subterm'
  imod entOwn_of_struct «$r0_ptr» (raftpb.Entry.mk zeroValDef «$v1_ptr» «$v0_ptr» null slice.nil null slice.nil 0)
    (EntryM.mk e.Term' e.Index' (zero_val raftpb.EntryType) [] (zero_val w64)) ⊤ rfl $$ [«$r0»] with Hd0
  · iframe «$r0» cT cI
    isplitl []; · iapply cellRO_null
    isplitl []; · iapply ownSlice_nil
    iapply cellRO_null
  ihave %Hsllen := ownSlice_len $$ Hsl
  simp only [List.length_replicate] at Hsllen
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_store_slice_index sl (sint.Z (W64 0)) _ «$r0_ptr» $$ [Hsl] with Hsl
  · iframe Hsl; ipureintro; simp only [List.length_replicate]; constructor <;> word
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (ci - σp.prev.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hlk
  wp_apply wp_GetSubterm.1 lk DFrac.discard e $$ [Hek] with -
  · iframe Hek
  wp_join iprop("Hd'" ∷ entOwn «$r0_ptr» d' ∗ "Hsl" ∷ sl ↦* (List.replicate 1 null).set 0 «$r0_ptr» ∗
      "st" ∷ st_ptr ↦ e.Subterm' ∗ "ents" ∷ ents_ptr ↦ sl)
    with [Hd0 Hsl st ents]
  · -- zero: the dummy has subterm `0 = e.Subterm'`
    iframe Hsl st ents
    have : e.Subterm' = zero_val w64 := by rw [Hif]; rfl
    simp only [d', this]
    iexact Hd0
  · -- a non-zero subterm: `ents[0].Subterm = new(st)`, a fresh cell holding it
    imod cellRO_alloc $$ «$r0» with #cS'
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) _ (DFrac.own 1) _ (by word) $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; rw [show (sint.Z (W64 0)).toNat = 0 by word]; rfl
    iunfold entOwn at Hd0
    iunfold entPts at Hd0
    iNamed Hd0
    wp_auto
    wp_join_done
    iframe Hsl st ents
    iunfold entOwn
    iunfold entPts
    iexists pt, pi, pty, ds, uf, _
    isplitr; · ipureintro; exact Hnn
    iframe HT cT HI cI HY cY HD Hd HS cS' Hpb
  iNamed 1
  imod entOwn_freeze $$ Hd' with #Hd'
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
  -- (D19i part 1) the new boundary: within the floor, at an entry of the contents, at most the
  -- storage's snapshot
  have HtermL : termAt σL.prev σL.ents ci = some e.Term' := by
    rw [← termAt_memCut Hcok1 ci (by omega)]
    rw [← Hσf] at Hterm
    simpa only [memCut] using Hterm
  have Hcok' : CutOk σL (entryID.mk e.Term' ci) := by
    refine ⟨by have := Hcok1.1; simp only; omega, by simp only; omega, HtermL⟩
  imod ghostVar_update_halves (entryID.mk e.Term' ci) γs.cb _ _ $$ Hcb Hcbt with ⟨Hcb, Hcbt⟩
  imod mono_nat_own_update (uint.Z ci).toNat (by omega) $$ Hbd with ⟨Hbd, -⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hd_inv Hlk_inv HhardState_1
    Hents_f_1 Hes'_cap Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1
    Hcb Hbd Hsq]
  · inext
    unfold memstorageInv
    iexists σL, entryID.mk e.Term' ci
    isplitl [Hd_inv Hlk_inv]
    · unfold memInvGhost
      iexists Dl
      iframe Hd_inv Hlb_inv Hlk_inv
      ipureintro; exact HD
    isplitl [HhardState_1 Hents_f_1 Hes'_cap Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1
      Hcs_term_1 Hcs_snapshot_1]
    · ihave Hf : memstorageFields ms (memStorCompacted σp ci e.Term') $$ [HhardState_1 Hents_f_1
        Hes'_cap Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1]
      · unfold memstorageFields
        iexists hp1, es', d', nfi1, nli1, nen1, nte1, nsn1
        rw [← HE]
        iframe # ∗
        ipureintro
        exact ⟨by simp [d', memStorCompacted, Hei], rfl⟩
      iapply memstorageFields_congr $$ Hf
      · rfl
      · rw [← Hσf]
        simp only [memCut, memStorCompacted, List.drop_drop]
        congr 1
        have := Hcok1.1
        omega
    isplitr
    · ipureintro; exact Hpb_inv0
    iunfold memCutInv
    iexists S
    iframe Hcb Hbd Hsq Hsrel
    isplitr
    · iright
      iapply memFlLb_le γs x ci Hle0 $$ Hflx
    ipureintro
    refine ⟨⟨Hcok', ?_⟩, Hcap⟩
    simp only
    rw [HS1]; exact Hsle
  iapply HΦ
  iright
  iexists e.Term'
  isplitr
  · ipureintro; exact ⟨Hgt, rfl⟩
  unfold memSnapTok
  rw [show snapPart { σt with prev := entryID.mk e.Term' ci } = snapPart σt from rfl]
  iframe # ∗

end proof

end EtcdGrove
end Perennial
