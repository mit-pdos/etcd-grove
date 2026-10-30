/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/CheckHistory.lean`: each event's
condition is false by `histOk`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.CheckHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetupWrite
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Permitted

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem CheckHistory.wp_proof (wp_SetupWrite : SetupWrite.spec (GF := GF) (hG := hG))
    (wp_Writer : Writer.spec (GF := GF) (hG := hG))
    (wp_Permitted : Permitted.spec (GF := GF) (hG := hG)) :
    CheckHistory.spec (GF := GF) (hG := hG) := by
  intro esl evs dq setupRev endKey Hok
  wp_start as Hevs
  ihave %Hel := ownSlice_len $$ Hevs
  wp_auto
  ihave HI : (∃ (j : w64) (e0 : wev),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "Hevs" ∷ esl ↦*{dq} evs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len⌝ : IProp GF) $$ [i e Hevs]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z esl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem evs (sint.nat j) as x
    have hxm : x ∈ evs := List.mem_of_getElem? Hx_lookup
    wp_apply wp_load_slice_index esl (sint.Z j) evs dq x Hj.1 $$ [Hevs] as Hevs
    · iframe; ipureintro; exact Hx_lookup
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, x
        iframe
        ipureintro; constructor <;> word
      · (try wp_auto)
        have hne := Hif
        wp_apply wp_SetupWrite
        wp_if_destruct
        · -- a repeated set-up put
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, x
          iframe
          ipureintro; constructor <;> word
        · (try wp_auto)
          wp_apply wp_Writer
          wp_apply wp_Permitted
          rw [decide_eq_true (Hok x hxm (by word) hne Hif)]
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, x
          iframe
          ipureintro; constructor <;> word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    iframe

end proof

end authkv
end EtcdGrove
end Perennial
