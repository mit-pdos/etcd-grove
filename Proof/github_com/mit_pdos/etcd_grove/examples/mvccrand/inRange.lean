/- Lean-first (no Rocq counterpart). The proof of `inRange`: its three cases. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.inRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem inRange.wp_proof : inRange.spec (GF := GF) (hG := hG) := by
  intro key endk kk e k dq dq'
  wp_start as ⟨Hk, He⟩
  wp_auto
  ihave %Hel := ownSlice_len $$ He
  wp_if_destruct
  · simp only [inRangeM, ↓reduceIte]
    wp_apply wp_bytes_to_string key kk dq $$ [$Hk] as Hk
    (try wp_auto)
    iapply HΦ; iframe
  · simp only [inRangeM, Bool.false_eq_true, ↓reduceIte, mvcc.inRange]
    wp_apply wp_bytes_to_string key kk dq $$ [$Hk] as Hk
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      simp only [Bool.not_true, Bool.false_and]
      iapply HΦ; iframe
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        have he : e = [] := List.eq_nil_of_length_eq_zero (by rw [Hel.1, Hif]; rfl)
        simp only [he, decide_true, Bool.true_or, Bool.and_true, Bool.not_false]
        iapply HΦ; iframe
      · wp_apply wp_bytes_to_string endk e dq' $$ [$He] as He
        (try wp_auto)
        rename_i hlen
        have he : e ≠ [] := by
          intro he; subst he; apply hlen; simp at Hel; word
        simp only [decide_eq_false he, Bool.false_or, Bool.not_false, Bool.true_and]
        iapply HΦ; iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
