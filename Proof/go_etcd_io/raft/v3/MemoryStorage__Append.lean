/- `MemoryStorage.Append` (`storage.go:300`; U8 v2 step 3, 2026-10-29): over the range vocabulary.
The caller's range from the batch's first index `k` to the end is disjoint from the frozen dummy at
the compaction point `c`, so `c < k`: no shortcut, no truncation, `offset = k - c ≤ len(ms.ents)`
(no panic). The range is deleted from the map and the batch inserted, the end moved to `k + |es|`. -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__firstIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The lock's pure facts after the append: the entries after the compaction point `c` are the
stored ones below `k`, then the batch; the map is the old one with the range from `k` to the old
end deleted (`M1`) and the batch inserted (`M2`). -/
private theorem append_memOk (p : entryID) (ents es : List EntryM) (M M1 M2 : GMap Nat EntryM)
    (sv : SnapshotM) (k : Nat) (Hok : MemOk p ents M sv)
    (Hk1 : uint.nat p.index' < k) (Hk2 : k ≤ uint.nat p.index' + 1 + ents.length)
    (Hlen : k + es.length ≤ 2^61) (Hne : es ≠ [])
    (Hsi : uint.nat sv.Metadata'.Index' = 0 ∨ uint.nat sv.Metadata'.Index' < k)
    (HM1 : ∀ i, M1.lookup i =
      if k ≤ i ∧ i < uint.nat p.index' + 1 + ents.length then none else M.lookup i)
    (HM2 : ∀ i, M2.lookup i = if k ≤ i ∧ i < k + es.length then es[i - k]? else M1.lookup i)
    (Hidx : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j) :
    MemOk p (ents.take (k - uint.nat p.index' - 1) ++ es) M2 sv := by
  obtain ⟨_, Hab, Hin, Hsl, _, Hix⟩ := Hok
  have Hesl : 0 < es.length := List.length_pos_iff.2 Hne
  have Htl : (ents.take (k - uint.nat p.index' - 1)).length = k - uint.nat p.index' - 1 := by
    rw [List.length_take]; omega
  unfold MemOk
  simp only [List.length_append, Htl]
  refine ⟨by omega, ?_, ?_, Hsl, by omega, ?_⟩
  · intro i hi
    rw [HM2 i, ite_eq_right (by omega), HM1 i]
    by_cases h : i < uint.nat p.index' + 1 + ents.length
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega)]; exact Hab i (by omega)
  · intro i hi1 hi2
    rw [HM2 i]
    by_cases h : k ≤ i
    · rw [ite_eq_left (by omega), List.getElem?_append_right (by omega), Htl]
      congr 1; omega
    · rw [ite_eq_right (by omega), HM1 i, ite_eq_right (by omega), Hin i hi1 (by omega),
        List.getElem?_append_left (by omega), List.getElem?_take_of_lt (by omega)]
  · intro j e hj
    by_cases h : j < k - uint.nat p.index' - 1
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h] at hj
      exact Hix j e hj
    · rw [List.getElem?_append_right (by omega), Htl] at hj
      rw [Hidx _ e hj]; omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Two slice values with the same pointer and length own the same (non-empty) elements (a copy
of `InvRaftlog`'s `ownSlice_same_ptr_len`, to keep this module's imports small): the full slice
`ms.ents[:offset:offset]` from the `slice.slice` form `ownSlice_slice` gives. -/
private theorem append_ownSlice_same_ptr_len {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s1 s2 : GoSlice) (dq : DFrac) (vs : List V) :
    vs ≠ [] →
    s1.ptr = s2.ptr →
    s1.len = s2.len →
    sint.Z s2.len ≤ sint.Z s2.cap →
    ⊢ (s1 ↦*{dq} vs : IProp GF) -∗ s2 ↦*{dq} vs := by
  intro Hne Hptr Hlen Hcap
  obtain ⟨p1, l1, c1⟩ := s1
  obtain ⟨p2, l2, c2⟩ := s2
  simp only at Hptr Hlen Hcap
  subst Hptr Hlen
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 Hne
  · iright
    iframe H
    ipureintro; exact Hcap

theorem MemoryStorage.Append.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Append.spec (GF := GF) (hG := hG) := by
  intro ms γs k old es s dq Hidx Hlen
  wp_start as ⟨#Hlock, Hold, Hend, Hs⟩
  iunfold entsPts at Hs
  icases Hs with ⟨%lsb, Hsb, #Hbigb⟩
  ihave %Hblen := entsBig_length $$ Hbigb
  by_cases Hnil : es = []
  · -- an empty batch: `Append` returns at once
    subst Hnil
    ihave %Hslen := ownSlice_len $$ Hsb
    simp only [List.length_nil] at Hblen
    rw [List.length_eq_zero_iff.1 Hblen] at Hslen
    simp only [List.length_nil] at Hslen
    wp_apply wp_with_defer as %defer defer
    wp_if_destruct
    · iapply HΦ
      iframe Hold Hend
      iunfold entsPts
      iexists lsb
      iframe Hsb Hbigb
    · exfalso
      apply Hif
      word
  obtain ⟨e0, rest, rfl⟩ : ∃ e0 rest, es = e0 :: rest := by
    cases es with
    | nil => exact absurd rfl Hnil
    | cons a b => exact ⟨a, b, rfl⟩
  have Hk0 : uint.nat e0.Index' = k := by simpa using Hidx 0 e0 rfl
  ihave %Hslen := ownSlice_len $$ Hsb
  simp only [List.length_cons] at Hslen Hblen Hlen
  icases entsBig_lookup lsb (e0 :: rest) 0 e0 rfl $$ Hbigb with ⟨%lb0, %Hlb0, #Heb0⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  wp_if_destruct
  · exfalso
    have H0 := Hslen.1
    rw [Hif, show sint.nat (W64 0) = 0 from rfl] at H0
    omega
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memEnd at Hend
  icases Hend with ⟨Hen, Hek⟩
  icases ghostVar_agree γs.en _ _ _ _ $$ Hen Hen_inv with %He
  iunfold memLog at Hold
  icases Hold with ⟨Hold, -⟩
  icases Hd0_inv with ⟨%d0, #Hd0, %Hd0t⟩
  icases memLogL_frozen_ne γs.log k old _ d0 $$ Hold Hd0 with %Hck
  ihave #Hd0_inv : (∃ (e : EntryM), (uint.nat p.index') ↪[γs.log]□ e ∗ ⌜e.Term' = p.term'⌝) $$ []
  · iexists d0; iframe Hd0; ipureintro; exact Hd0t
  ihave %Hsi : ⌜uint.nat sv.Metadata'.Index' = 0 ∨ uint.nat sv.Metadata'.Index' < k⌝ $$ [Hold]
  · icases Hsf_inv with (%H0 | ⟨%e1, #He1, -⟩)
    · ipureintro; left; exact H0
    · icases memLogL_frozen_ne γs.log k old _ e1 $$ Hold He1 with %H1
      ipureintro; right
      have := Hok_inv.2.2.2.2
      omega
  have Hb := Hok_inv.1
  have Hck' : uint.nat p.index' < k := by omega
  have Hke : k ≤ uint.nat p.index' + 1 + ents.length := by omega
  have Hpb : uint.Z (memPhys p ents).prev.index' + ((memPhys p ents).ents.length : Int) < 2^61 := by
    simp only [memPhys]; word
  wp_apply wp_MemoryStorage_firstIndex ms (memPhys p ents) Hpb $$ [$Hfields_inv] as %fi ⟨%Hfi, Hf⟩
  simp only [memPhys] at Hfi
  have Hlenz : uint.Z s.len = (rest.length : Int) + 1 := by
    have := Hslen.1; rw [Hblen] at this; word
  -- `entries[0].GetIndex()`, read four times
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len from ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  -- `last < first`: no, the batch starts above the compaction point
  wp_if_destruct
  · exfalso; word
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len from ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  -- `first > entries[0].Index`: no
  wp_if_destruct
  · exfalso; word
  -- `offset := entries[0].GetIndex() - ms.ents[0].GetIndex()`
  iunfold memstorageFields at Hf
  icases Hf with ⟨%hp, %se, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hf⟩
  iNamed Hf
  simp only [memPhys] at Hdummy
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  iunfold entsRO at Hents
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, #Hls, #Hbig⟩
  ihave %Hbl := entsBig_length $$ Hbig
  icases entsBig_lookup ls (dummy :: (memPhys p ents).ents) 0 dummy rfl $$ Hbig with ⟨%l0, %Hl0, #He0⟩
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len from ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z se.len from ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index se (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0i, Hd0t'⟩ := Hdummy
  rw [Hd0i]
  simp only [memPhys] at Hcl Hbl ⊢
  have Hoff : uint.Z (e0.Index' - p.index') = uint.Z e0.Index' - uint.Z p.index' := by word
  have Heslen : uint.Z se.len = (ents.length : Int) + 1 := by
    have := Hcl.2; word
  ihave %Hwf := ownSlice_wf $$ Hls
  -- the ghost update: the caller's range out, the batch in, the end moved
  imod memLogL_delete γs.log M k old $$ Hlog_inv Hold with ⟨%M1, Hlog_inv, %HM1⟩
  have Habs : ∀ i, k ≤ i → i < k + (e0 :: rest).length → M1.lookup i = none := by
    intro i h1 _
    rw [HM1 i]
    by_cases h : i < k + old.length
    · rw [ite_eq_left ⟨h1, h⟩]
    · rw [ite_eq_right (by omega)]; exact Hok_inv.2.1 i (by omega)
  imod memLogL_insert γs.log M1 k (e0 :: rest) Habs $$ Hlog_inv with ⟨%M2, Hlog_inv, Hnew, %HM2⟩
  imod ghostVar_update_halves (k + (e0 :: rest).length) γs.en _ _ $$ Hen Hen_inv with ⟨Hen, Hen_inv⟩
  have Hok' := append_memOk p ents (e0 :: rest) M M1 M2 sv k Hok_inv Hck' Hke
    (by simp only [List.length_cons]; omega) (by simp) Hsi (by rw [← He]; exact HM1) HM2 Hidx
  have Hel : uint.nat p.index' + 1 + (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest).length =
      k + (e0 :: rest).length := by
    simp only [List.length_append, List.length_take, List.length_cons]; omega
  have Hkc : sint.nat (e0.Index' - p.index') = k - uint.nat p.index' := by word
  ihave Hpost : (entsPts s dq (e0 :: rest) -∗ Φ #interface.nil) $$ [HΦ Hnew Hen Hek]
  · iintro Hs
    iapply HΦ
    iframe Hs
    rw [ite_eq_right (by simp)]
    iunfold memLog; iunfold memEnd
    iframe
    ipureintro; right; simp only [List.length_cons]; omega
  wp_if_destruct
  · -- the batch overwrites stored entries: `append(ms.ents[:offset:offset], entries...)`
    have Hcut := of_decide_eq_true Hif.symm
    rw [Hoff] at Hcut
    rw [ite_eq_left ⟨by word, by word, by word, by word⟩]
    icases (ownSlice_slice (W64 0) (e0.Index' - p.index') se DFrac.discard ls
      ⟨by word, by word, by word⟩).1 $$ Hls with ⟨-, #Hsub, -⟩
    have Hsubeq : subslice (sint.nat (W64 0)) (sint.nat (e0.Index' - p.index')) ls =
        ls.take (sint.nat (e0.Index' - p.index')) := by
      simp only [subslice]; rfl
    ihave #Hsub1 : slice.slice se Loc (W64 0) (e0.Index' - p.index') ↦*□
        ls.take (sint.nat (e0.Index' - p.index')) $$ [Hsub]
    · rw [← Hsubeq]; iexact Hsub
    have Hne : ls.take (sint.nat (e0.Index' - p.index')) ≠ [] := by
      intro Hc
      have := congrArg List.length Hc
      simp only [List.length_take, Hbl, List.length_cons, List.length_nil] at this
      omega
    ihave #Hsub2 := append_ownSlice_same_ptr_len
      (slice.slice se Loc (W64 0) (e0.Index' - p.index'))
      (slice.fullSlice se Loc (W64 0) (e0.Index' - p.index') (e0.Index' - p.index'))
      _ _ Hne rfl rfl (by simp only [slice.fullSlice]; word) $$ Hsub1
    ihave Hcap0 := ownSliceCap_empty (V := Loc)
      (slice.fullSlice se Loc (W64 0) (e0.Index' - p.index') (e0.Index' - p.index'))
      (by simp only [slice.fullSlice]) (by simp only [slice.fullSlice]; word)
    wp_auto
    wp_apply wp_slice_append_persistent (V := Loc) _ _ s lsb dq
      $$ [$Hsub2 $Hcap0 $Hsb] as %es' ⟨#Hes', Hes'_cap, Hsb⟩
    ihave #Hbt := entsBig_take (sint.nat (e0.Index' - p.index')) ls (dummy :: ents) $$ Hbig
    ihave #Hba := entsBig_app _ lsb _ (e0 :: rest) $$ [Hbt Hbigb]
    · iframe Hbt Hbigb
    ihave #Hes2 : entsRO es' (dummy :: (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest)) $$ []
    · have Hl : (dummy :: ents).take (sint.nat (e0.Index' - p.index')) ++ e0 :: rest =
          dummy :: (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest) := by
        rw [Hkc, show k - uint.nat p.index' = (k - uint.nat p.index' - 1) + 1 by omega,
          List.take_succ_cons, List.cons_append, Nat.add_sub_cancel]
      rw [← Hl]
      iunfold entsRO; iunfold entsPts
      iexists _
      iframe Hes' Hba
    ihave Hf' : memstorageFields ms (memPhys p (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest)) $$ [HhardState Hents_f Hes'_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · unfold memstorageFields
      iexists hp, es', dummy, nfi, nli, nen, nte, nsn
      simp only [named, memPhys]
      iframe # ∗
      ipureintro; exact ⟨Hd0i, Hd0t'⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hf' Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk_inv]
    · unfold memstorageInv
      iexists p, (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest), M2, sv
      simp only [named]
      rw [Hel]
      iframe # ∗
      ipureintro; exact Hok'
    iapply Hpost
    iunfold entsPts
    iexists lsb
    iframe Hsb Hbigb
  wp_if_destruct
  · -- the batch continues the stored entries: `append(ms.ents, entries...)`
    have Hend := of_decide_eq_true Hif.symm
    have Hk : ents.length = k - uint.nat p.index' - 1 := by
      have H1 : uint.Z se.len = uint.Z (e0.Index' - p.index') := by rw [Hend]
      word
    wp_apply wp_slice_append_persistent (V := Loc) se ls s lsb dq
      $$ [$Hls $Hents_cap $Hsb] as %es' ⟨#Hes', Hes'_cap, Hsb⟩
    ihave #Hba := entsBig_app ls lsb (dummy :: ents) (e0 :: rest) $$ [Hbig Hbigb]
    · iframe Hbig Hbigb
    ihave #Hes2 : entsRO es' (dummy :: (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest)) $$ []
    · rw [List.take_of_length_le (by omega), ← List.cons_append]
      iunfold entsRO; iunfold entsPts
      iexists _
      iframe Hes' Hba
    ihave Hf' : memstorageFields ms (memPhys p (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest)) $$ [HhardState Hents_f Hes'_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · unfold memstorageFields
      iexists hp, es', dummy, nfi, nli, nen, nte, nsn
      simp only [named, memPhys]
      iframe # ∗
      ipureintro; exact ⟨Hd0i, Hd0t'⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hf' Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk_inv]
    · unfold memstorageInv
      iexists p, (ents.take (k - uint.nat p.index' - 1) ++ e0 :: rest), M2, sv
      simp only [named]
      rw [Hel]
      iframe # ∗
      ipureintro; exact Hok'
    iapply Hpost
    iunfold entsPts
    iexists lsb
    iframe Hsb Hbigb
  · -- a gap after the stored entries: excluded, `offset ≤ len(ms.ents)`
    exfalso
    rename_i Hlt
    have h1 : ¬ (uint.Z (e0.Index' - p.index') < uint.Z se.len) :=
      fun h => Hlt (by simp [h])
    have h2 : se.len ≠ e0.Index' - p.index' := fun h => Hif (by simp [h])
    have h3 : uint.Z se.len ≠ uint.Z (e0.Index' - p.index') := fun h => h2 (uint_Z_inj.1 h)
    word

end proof

end EtcdGrove
end Perennial
