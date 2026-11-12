/- Lean-first (no Rocq counterpart). The proof of `walLastHS`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walLastHS
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.phsNext

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

theorem tLastHS_take_succ (h : List TOp) (j : Nat) (o : TOp) (ho : h[j]? = some o) :
    tLastHS (h.take (j + 1)) =
      if o.snap then tLastHS (h.take j) else tPhsNext (tLastHS (h.take j)) o.hs := by
  unfold tLastHS
  rw [List.take_add_one, ho, Option.toList_some, List.foldl_append]
  rfl

theorem walLastHS.wp_proof (wp_phsNext : phsNext.spec (GF := GF) (hG := hG)) :
    walLastHS.spec (GF := GF) (hG := hG) := by
  intro s h
  wp_start as Hr
  iunfold opsRep at Hr
  icases Hr with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  ihave HI : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "p" ∷ p_ptr ↦ tLastHS (h.take (sint.nat j)) ∗ "h" ∷ h_ptr ↦ s ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i p h]
  · iexists W64 0
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hjl : sint.nat j < es.length := by
      have : sint.nat j < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, es[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z j) v s DFrac.discard es Hj.1 (by simpa [sint.nat] using Hv) $$ Hs
      with ⟨Hv, -⟩
    icases opsElems_lookup es h (sint.nat j) v Hv $$ Hel with ⟨%o, %Ho, Hop⟩
    iunfold opRep at Hop
    icases Hop with ⟨%Hf, -⟩
    obtain ⟨hsn, hhs, -, -⟩ := Hf
    iStructNamed Hv
    wp_auto
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hstep := tLastHS_take_succ h (sint.nat j) o Ho
    rw [hsn]
    cases hos : o.snap
    · simp only [hos, Bool.false_eq_true, ↓reduceIte] at hstep
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_apply wp_phsNext
      wp_for_post
      iframe
      iexists j + W64 1
      rw [hj1, hstep, hhs]
      iframe
      ipureintro; constructor <;> word
    · simp only [hos, ↓reduceIte] at hstep
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1
      rw [hj1, hstep]
      iframe
      ipureintro; constructor <;> word
  · have hjn : sint.nat j = h.length := by
      have : sint.nat j = sint.nat s.len := by word
      omega
    rw [hjn, List.take_length]
    wp_end

end proof

end etcd_wal
end EtcdGrove
end Perennial
