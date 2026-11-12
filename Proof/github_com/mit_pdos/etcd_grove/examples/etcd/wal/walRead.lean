/- Lean-first (no Rocq counterpart). The proof of `walRead`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walLastHS
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walFoldChk
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem walRead.wp_proof (wp_walLastHS : walLastHS.spec (GF := GF) (hG := hG))
    (wp_walFoldChk : walFoldChk.spec (GF := GF) (hG := hG)) :
    walRead.spec (GF := GF) (hG := hG) := by
  intro s h hw
  wp_start as #Hr
  ihave Hr2 := Hr
  iunfold opsRep at Hr2
  icases Hr2 with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  wp_apply wp_walLastHS $$ [Hr]
  · iexact Hr
  iintro -
  wp_auto
  wp_apply +noauto (wp_slice_make3 (V := walOp) (W64 0) s.len (by word)) as %f0 ⟨Hf0, Hf0cap, -⟩
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist Hf0
  wp_auto
  ihave HI : (∃ (i : w64) (fs : GoSlice) (fvs : List walOp),
      "i" ∷ i_ptr ↦ i ∗ "f" ∷ f_ptr ↦ fs ∗ "h" ∷ h_ptr ↦ s ∗
      "Hf" ∷ fs ↦*□ fvs ∗ "Hfcap" ∷ ownSliceCap walOp fs (DFrac.own 1) ∗
      "Hfe" ∷ opsElems fvs ((h.take (sint.nat i)).filter (tKeep (tLastHS h).commit')) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i f h Hf0cap]
  · iexists W64 0, f0, []
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
    isplitl []
    · iexact Hf0
    isplitl []
    · iapply opsElems_nil
    ipureintro; constructor <;> word
  wp_for HI
  icases Hf with #Hf
  icases Hfe with #Hfe
  cleanup_bool_decide
  wp_if_destruct
  · have hil : sint.nat i < es.length := by
      have : sint.nat i < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, es[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨Hi.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z i) v s DFrac.discard es Hi.1 (by simpa [sint.nat] using Hv) $$ Hs
      with ⟨Hv, -⟩
    icases opsElems_lookup es h (sint.nat i) v Hv $$ Hel with ⟨%op, #Hop⟩
    icases Hop with ⟨%Hop, #Hopr⟩
    ihave Hopr2 := Hopr
    iunfold opRep at Hopr2
    icases Hopr2 with ⟨%Hf, -⟩
    obtain ⟨hsn, hhs, hix, htm⟩ := Hf
    iStructNamed Hv
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have hstep := tKeep_filter_take_succ (tLastHS h).commit' h (sint.nat i) op Hop
    wp_auto
    rw [hsn]
    cases hos : op.snap
    · have hk : tKeep (tLastHS h).commit' op = true := by simp [tKeep, hos]
      simp only [hk, ↓reduceIte] at hstep
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index s (sint.Z i) es DFrac.discard v hb.1 as -
      · isplitl []
        · iexact Hs
        ipureintro
        simpa [sint.nat] using Hv
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_auto
      wp_apply wp_slice_append_persistent (sl := fs) (vs := fvs) $$ [$Hfcap $Hosl] as %fs' ⟨Hf', Hfcap, -⟩
      · iexact Hf
      wp_for_post
      iframe
      iexists i + W64 1, fs', fvs ++ [v]
      iframe
      rw [hi1, hstep]
      isplitl []
      · iapply opsElems_snoc
        isplitl []
        · iexact Hfe
        · iexact Hopr
      ipureintro; constructor <;> word
    · wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      rw [hix]
      wp_if_destruct
      · have hk : tKeep (tLastHS h).commit' op = false := by
          simp only [tKeep, hos, Bool.true_and, Bool.not_eq_false', decide_eq_true_eq]; word
        simp only [hk, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep
        wp_for_post
        iframe
        iexists i + W64 1, fs, fvs
        iframe
        rw [hi1, hstep]
        isplitl []
        · iexact Hf
        isplitl []
        · iexact Hfe
        ipureintro; constructor <;> word
      · have hk : tKeep (tLastHS h).commit' op = true := by
          simp only [tKeep, hos, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]; intro h'; apply Hif; word
        simp only [hk, ↓reduceIte] at hstep
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index s (sint.Z i) es DFrac.discard v hb.1 as -
        · isplitl []
          · iexact Hs
          ipureintro
          simpa [sint.nat] using Hv
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        wp_auto
        wp_apply wp_slice_append_persistent (sl := fs) (vs := fvs) $$ [$Hfcap $Hosl] as %fs' ⟨Hf', Hfcap, -⟩
        · iexact Hf
        wp_for_post
        iframe
        iexists i + W64 1, fs', fvs ++ [v]
        iframe
        rw [hi1, hstep]
        isplitl []
        · iapply opsElems_snoc
          isplitl []
          · iexact Hfe
          · iexact Hopr
        ipureintro; constructor <;> word
  · have hin : sint.nat i = h.length := by
      have : sint.nat i = sint.nat s.len := by word
      omega
    rw [hin, List.take_length]
    have hwf : tHistWf (h.filter (tKeep (tLastHS h).commit')) :=
      fun o ho => hw o (List.mem_filter.1 ho).1
    wp_apply wp_walFoldChk fs (h.filter (tKeep (tLastHS h).commit')) hwf as %v %ok Hres
    · iunfold opsRep
      iexists fvs
      isplitl []
      · iexact Hf
      · iexact Hfe
    wp_end

end proof

end etcd_wal
end EtcdGrove
end Perennial
