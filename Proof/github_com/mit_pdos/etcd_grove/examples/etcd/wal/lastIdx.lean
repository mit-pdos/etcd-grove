/- Lean-first (no Rocq counterpart). The proof of `lastIdx`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.lastIdx
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

theorem lastIdx.wp_proof : lastIdx.spec (GF := GF) (hG := hG) := by
  intro s h
  wp_start as #Hr
  iunfold opsRep at Hr
  icases Hr with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "e" ∷ e_ptr ↦ (h.take (sint.nat i)).foldl
        (fun x o => if o.snap then x else (o.ents.getLast?.map (·.index')).getD x) (W64 0) ∗
      "sn" ∷ sn_ptr ↦ (h.take (sint.nat i)).foldl
        (fun x o => if o.snap ∧ uint.nat x < uint.nat o.idx then o.idx else x) (W64 0) ∗
      "h" ∷ h_ptr ↦ s ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i e sn h]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.foldl_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z i < sint.Z s.len
  · rw [if_pos (by simp [hlt])]
    have hil : sint.nat i < es.length := by
      have : sint.nat i < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, es[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨Hi.1, hlt⟩
    icases ownSlice_elem_acc (sint.Z i) v s DFrac.discard es Hi.1 (by simpa [sint.nat] using Hv) $$ Hs
      with ⟨Hv, -⟩
    icases opsElems_lookup es h (sint.nat i) v Hv $$ Hel with ⟨%op, %Hop, #Hopr⟩
    iunfold opRep at Hopr
    icases Hopr with ⟨%Hf, #Hoe⟩
    obtain ⟨hsn, -, hix, -⟩ := Hf
    ihave %Hoel := ownSlice_len $$ Hoe
    iStructNamed Hv
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    wp_auto
    repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    rw [hsn]
    cases hos : op.snap
    · wp_auto
      repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_if_destruct
      · have hne : op.ents ≠ [] := by
          intro h0; rw [h0] at Hoel; simp at Hoel; word
        obtain ⟨x, Hx⟩ : ∃ x, op.ents.getLast? = some x := by
          cases hl : op.ents.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
          | some x => exact ⟨x, rfl⟩
        have hxl : op.ents[op.ents.length - 1]? = some x := by
          rw [← List.getLast?_eq_getElem?]; exact Hx
        have hb2 : 0 ≤ sint.Z (v.ents'.len - W64 1) ∧ sint.Z (v.ents'.len - W64 1) < sint.Z v.ents'.len := by
          constructor <;> word
        icases ownSlice_elem_acc (sint.Z (v.ents'.len - W64 1)) x v.ents' DFrac.discard op.ents hb2.1
          (by rw [show (sint.Z (v.ents'.len - W64 1)).toNat = op.ents.length - 1 by word]; exact hxl)
          $$ Hoe with ⟨Hxv, -⟩
        iStructNamed Hxv
        repeat (simp only [hb, hb2, _root_.and_self, ↓reduceIte]; try wp_auto)
        wp_for_post
        iframe
        iexists i + W64 1
        rw [hi1, foldl_take_succ _ _ h (sint.nat i) op Hop, foldl_take_succ _ _ h (sint.nat i) op Hop]
        simp only [hos, Bool.false_eq_true, ↓reduceIte, _root_.false_and, Hx, Option.map_some, Option.getD_some]
        iframe
        ipureintro; constructor <;> word
      · have he : op.ents = [] := by
          rw [← List.length_eq_zero_iff, Hoel.1]; word
        wp_for_post
        iframe
        iexists i + W64 1
        rw [hi1, foldl_take_succ _ _ h (sint.nat i) op Hop, foldl_take_succ _ _ h (sint.nat i) op Hop]
        simp only [hos, Bool.false_eq_true, ↓reduceIte, _root_.false_and, he, List.getLast?_nil, Option.map_none,
          Option.getD_none]
        iframe
        ipureintro; constructor <;> word
    · wp_auto
      repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      rw [hix]
      wp_if_destruct
      · repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
        wp_for_post
        iframe
        iexists i + W64 1
        rw [hi1, foldl_take_succ _ _ h (sint.nat i) op Hop, foldl_take_succ _ _ h (sint.nat i) op Hop]
        simp only [hos, ↓reduceIte, _root_.true_and]
        rw [if_pos (by word)]
        iframe
        ipureintro; constructor <;> word
      · wp_for_post
        iframe
        iexists i + W64 1
        rw [hi1, foldl_take_succ _ _ h (sint.nat i) op Hop, foldl_take_succ _ _ h (sint.nat i) op Hop]
        simp only [hos, ↓reduceIte, _root_.true_and]
        rw [if_neg (by intro h'; apply Hif; word)]
        iframe
        ipureintro; constructor <;> word
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hin : sint.nat i = h.length := by
      have : sint.nat i = sint.nat s.len := by word
      omega
    rw [hin, List.take_length]
    wp_auto
    unfold tLastIdx
    simp only
    wp_if_destruct
    · rw [if_pos (by word)]
      wp_end
    · rw [if_neg (by intro h'; apply Hif; word)]
      wp_end

end proof

end etcd_wal
end EtcdGrove
end Perennial
