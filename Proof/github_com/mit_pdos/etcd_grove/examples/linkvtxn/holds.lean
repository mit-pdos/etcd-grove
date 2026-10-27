/-
Lean-first (no Rocq counterpart).

The proof of `holds`: `lookup`, then the comparison by its kind.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.holds
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.lookup

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem holds.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG)) :
    holds.spec (GF := GF) (hG := hG) := by
  intro sl es dq c
  wp_start as Hs
  wp_auto
  wp_apply wp_lookup sl es dq c.Key' $$ [$Hs] as %v %ok ⟨Hs, %Hlk⟩
  have hr : lookupL es c.Key' = (v, ok) := Hlk.symm
  wp_if_destruct
  · cases ok
    · wp_auto
      rw [show holdsL es c = false by simp [holdsL, hr, Hif]]
      iapply HΦ
      iframe
    · wp_auto
      rw [show holdsL es c = decide (v.Val' = c.Val') by simp [holdsL, hr, Hif]]
      iapply HΦ
      iframe
  · wp_if_destruct
    · rw [show holdsL es c = decide (v.Ver' = c.Num') by
        unfold holdsL; rw [hr, if_neg ‹¬c.Kind' = W64 0›, if_pos Hif]]
      iapply HΦ
      iframe
    · rw [show holdsL es c = decide (v.Mod' = c.Num') by
        unfold holdsL; rw [hr, if_neg ‹¬c.Kind' = W64 0›, if_neg Hif]]
      iapply HΦ
      iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
