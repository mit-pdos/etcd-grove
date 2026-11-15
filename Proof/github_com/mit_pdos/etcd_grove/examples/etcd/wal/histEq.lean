/- Lean-first (no Rocq counterpart). The proof of `histEq`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.histEq
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.opEq

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

theorem histEq.wp_proof (wp_opEq : opEq.spec (GF := GF) (hG := hG)) :
    histEq.spec (GF := GF) (hG := hG) := by
  intro sa sb ha hb
  wp_start as ⟨Ha, Hb⟩
  iunfold opsRep at Ha Hb
  icases Ha with ⟨%xs, #Has, #Hae⟩
  icases Hb with ⟨%bs, #Hbs, #Hbe⟩
  ihave %Hal := ownSlice_len $$ Has
  ihave %Hbl := ownSlice_len $$ Hbs
  ihave %Hael := opsElems_length $$ Hae
  ihave %Hbel := opsElems_length $$ Hbe
  ihave HΦ := ret_gen _ _ _ $$ HΦ
  wp_auto
  wp_if_destruct
  · have hleq := Hif
    have hlen : ha.length = hb.length := by rw [← Hael, ← Hbel, Hal.1, Hbl.1, Hif]
    ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
        "%Ht" ∷ ⌜ha.take (sint.nat j) = hb.take (sint.nat j)⌝ ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sa.len⌝ : IProp GF) $$ [i]
    · iexists W64 0
      iframe
      isplit
      · ipureintro; rw [show sint.nat (W64 0) = 0 from rfl]; simp
      · ipureintro; constructor <;> word
    wp_for HI
    by_cases hlt : sint.Z j < sint.Z sa.len
    · rw [if_pos (by simp [hlt])]
      have hjl : sint.nat j < xs.length := by
        have : sint.nat j < sint.nat sa.len := by word
        omega
      obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
      obtain ⟨y, Hy⟩ : ∃ y, bs[sint.nat j]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hba : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sa.len := ⟨Hj.1, hlt⟩
      have hbb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sb.len := ⟨Hj.1, by rw [← hleq]; exact hlt⟩
      icases ownSlice_elem_acc (sint.Z j) x sa DFrac.discard xs Hj.1
        (by simpa [sint.nat] using Hx) $$ Has with ⟨Hxv, -⟩
      icases ownSlice_elem_acc (sint.Z j) y sb DFrac.discard bs Hj.1
        (by simpa [sint.nat] using Hy) $$ Hbs with ⟨Hyv, -⟩
      icases opsElems_lookup xs ha (sint.nat j) x Hx $$ Hae with ⟨%ox, %Hox, #Hoxr⟩
      icases opsElems_lookup bs hb (sint.nat j) y Hy $$ Hbe with ⟨%oy, %Hoy, #Hoyr⟩
      wp_auto
      repeat (simp only [hba, hbb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_apply wp_opEq
      · iframe; isplitl []; iexact Hoxr; iexact Hoyr
      iintro -
      wp_auto
      wp_if_destruct
      · wp_for_post
        iframe
        iexists j + W64 1
        iframe
        have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rw [hj1]
        isplit
        · ipureintro; rw [← Hif] at Hoy; exact list_take_succ_eq Hox Hoy Ht
        · ipureintro; constructor <;> word
      · wp_for_post
        iapply HΦ
        isplitl []
        · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc
          rw [Hox] at Hoy; exact Hif (Option.some.inj Hoy)
        · itrivial
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hjn : sint.nat j = ha.length := by
        have : sint.nat j = sint.nat sa.len := by word
        omega
      rw [hjn, List.take_length, hlen, List.take_length] at Ht
      wp_auto
      wp_end
  · iapply HΦ
    isplitl []
    · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc
      apply Hif; word
    · itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial
