/- `MemoryStorage.Compact` (`storage.go:254`), proved 2026-10-12 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

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
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Compact.spec (GF := GF) (hG := hG) := by
  intro ms γs σ ci ecomp Hidle Hpre
  wp_start as ⟨Hms, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, %Hbounded⟩
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
  icases Hfields_inv with ⟨%hs, %snap, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, %voters,
    Hfields_inv⟩
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  simp only [List.length_cons] at Hlen
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy es DFrac.discard (dummy :: σp.ents) (by word) rfl
    $$ Hents with ⟨#Hd0, -⟩
  iStructNamedSuffix Hd0 "_d"
  have Hes0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True :=
    eq_true ⟨by word, by word⟩
  wp_auto
  simp only [Hes0, ↓reduceIte]
  wp_auto
  obtain ⟨Hd0i, Hd0t⟩ := Hdummy
  rw [Hd0i]
  wp_if_destruct
  · -- `ErrCompacted`: nothing changes
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hvoters Hents_f
      Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp
      iframe Hgs_inv
      isplitl
      · iexists hs, snap, es, dummy, nfi, nli, nen, nte, nsn, voters
        iframe # ∗
        ipureintro; exact ⟨Hsnap_id, Hd0i, Hd0t⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨Hif, rfl⟩
    unfold ownMemoryStorage
    iframe # ∗
    ipureintro; exact Hbounded
  obtain ⟨Hle, Hidx⟩ := Hpre (by omega)
  ihave Hf : memstorageFields ms σp $$ [HhardState Hsnapshot Hvoters Hents_f Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hs, snap, es, dummy, nfi, nli, nen, nte, nsn, voters
    iframe # ∗
    ipureintro; exact ⟨Hsnap_id, Hd0i, Hd0t⟩
  wp_apply wp_MemoryStorage_lastIndex ms σp Hpb_inv $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_if_destruct
  · exfalso; word
  iunfold memstorageFields at Hf
  icases Hf with ⟨%hs1, %snap1, %es1, %dummy1, %nfi1, %nli1, %nen1, %nte1, %nsn1, %voters1, Hf⟩
  iNamedSuffix Hf "_1"
  obtain ⟨Hd1i, Hd1t⟩ := Hdummy_1
  icases Hents_1 with #Hents_1
  ihave %Hlen1 := ownSlice_len $$ Hents_1
  simp only [List.length_cons] at Hlen1
  wp_auto
  wp_apply wp_slice_make3 (V := raftpb.Entry) (W64 1) _ as %sl ⟨Hsl, Hsl_cap, %Hslcap⟩
  -- the entry at `ci`: `ms.ents[i]`, `i = ci - offset ≥ 1`
  have Hk : sint.Z (ci - σp.prev.index') = uint.Z ci - uint.Z σp.prev.index' := by word
  have Hkb : (0 ≤ sint.Z (ci - σp.prev.index') ∧ sint.Z (ci - σp.prev.index') < sint.Z es1.len) =
      True := eq_true ⟨by word, by word⟩
  have Hkl : (uint.Z ci - uint.Z σp.prev.index' - 1).toNat < σp.ents.length := by omega
  obtain ⟨e, He⟩ : ∃ e, σp.ents[(uint.Z ci - uint.Z σp.prev.index' - 1).toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem Hkl⟩
  have He' : (dummy1 :: σp.ents)[(sint.Z (ci - σp.prev.index')).toNat]? = some e := by
    rw [Hk, show (uint.Z ci - uint.Z σp.prev.index').toNat =
      (uint.Z ci - uint.Z σp.prev.index' - 1).toNat + 1 by omega]
    exact He
  have Hei := Hidx e He
  icases ownSlice_elem_acc (sint.Z (ci - σp.prev.index')) e es1 DFrac.discard _ (by word) He'
    $$ Hents_1 with ⟨#Hek, -⟩
  iStructNamedSuffix Hek "_e"
  simp only [Hkb, ↓reduceIte]
  wp_auto
  -- `ents[0].Index = ...`, `ents[0].Term = ...`: the new slice's one element
  ihave %Hsllen := ownSlice_len $$ Hsl
  simp only [List.length_replicate] at Hsllen
  icases ownSlice_elem_acc (sint.Z (W64 0)) (zero_val raftpb.Entry) sl (DFrac.own 1) _ (by word)
    (by simp) $$ Hsl with ⟨Hz, Hsl⟩
  have Hs0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len) = True :=
    eq_true ⟨by word, by word⟩
  simp only [Hs0, ↓reduceIte]
  wp_auto
  simp only [Hkb, ↓reduceIte]
  wp_auto
  simp only [Hs0, ↓reduceIte]
  wp_auto
  ihave Hsl := Hsl $$ Hz
  ihave %Hwf1 := ownSlice_wf $$ Hents_1
  -- `ms.ents[i+1:]`, the entries after `ci`
  have Hb : (0 ≤ sint.Z (ci - σp.prev.index' + W64 1) ∧
      sint.Z (ci - σp.prev.index' + W64 1) ≤ sint.Z es1.len ∧ sint.Z es1.len ≤ sint.Z es1.cap) =
      True := eq_true ⟨by word, by word, Hwf1.2⟩
  simp only [Hb, ↓reduceIte]
  icases (ownSlice_slice (ci - σp.prev.index' + W64 1) es1.len es1 DFrac.discard
    (dummy1 :: σp.ents) ⟨by word, by word, by word⟩).1 $$ Hents_1 with ⟨-, #Hrest, -⟩
  wp_apply wp_slice_append (V := raftpb.Entry) $$ [$Hsl $Hsl_cap $Hrest] as %es' ⟨Hes', Hes'_cap, -⟩
  imod ownSlice_persist $$ Hes' with #Hes'
  -- the new state: the boundary at `ci` and its term, the entries after it
  have Hterm : termAt σp.prev σp.ents ci = some e.Term' := by
    have Hne : ¬ uint.Z ci = uint.Z σp.prev.index' := by omega
    unfold termAt
    simp only [Hne, ↓reduceIte, He]
    rfl
  let d' : raftpb.Entry := { (zero_val raftpb.Entry) with Index' := e.Index', Term' := e.Term' }
  have Hlist : (List.replicate 1 (zero_val raftpb.Entry)).set (sint.Z (W64 0)).toNat d' ++
      subslice (sint.nat (ci - σp.prev.index' + W64 1)) (sint.nat es1.len) (dummy1 :: σp.ents) =
      d' :: (memStorCompacted σp ci e.Term').ents := by
    simp only [subslice, memStorCompacted]
    rw [List.take_of_length_le (by simp only [List.length_cons]; word)]
    rw [show sint.nat (ci - σp.prev.index' + W64 1) =
      (uint.Z ci - uint.Z σp.prev.index').toNat + 1 by word]
    rfl
  ihave #Hes2 : es' ↦*□ (d' :: (memStorCompacted σp ci e.Term').ents) $$ [Hes']
  · rw [← Hlist]
    iExactEq Hes'
    rfl
  have Hpb' : uint.Z (memStorCompacted σp ci e.Term').prev.index' +
      ((memStorCompacted σp ci e.Term').ents.length : Int) < 2^61 := by
    simp only [memStorCompacted, List.length_drop]
    omega
  imod memView_set γs σp σp (memStorCompacted σp ci e.Term') Hidle (by simp [memStorCompacted, Hidle])
    $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_1 Hsnapshot_1 Hvoters_1
    Hents_f_1 Hes'_cap Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1]
  · inext
    unfold memstorageInv memstorageFields
    iexists memStorCompacted σp ci e.Term'
    iframe Hgs_inv
    isplitl
    · iexists hs1, snap1, es', d', nfi1, nli1, nen1, nte1, nsn1, voters1
      iframe # ∗
      ipureintro
      exact ⟨Hsnap_id_1, by simp [d', memStorCompacted, Hei], rfl⟩
    ipureintro; exact Hpb'
  iapply HΦ
  iright
  iexists e.Term'
  isplitr
  · ipureintro; exact ⟨by omega, Hterm, rfl⟩
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro; exact Hpb'

end proof

end EtcdGrove
end Perennial
