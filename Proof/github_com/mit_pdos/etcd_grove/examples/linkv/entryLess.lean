/-
Lean-first (no Rocq counterpart).

The proof of `entryLess`: the two string comparisons and `||`/`&&`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.entryLess

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem entryLess.wp_proof : entryLess.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show entryLessB a b = true by simp [entryLessB, Hif]]
    iapply HΦ; itrivial
  · have Hk := Hif
    wp_if_destruct
    · rw [show entryLessB a b = decide (go.GoStringLt a.val' b.val') by
        simp only [entryLessB, decide_eq_false Hk, decide_eq_true Hif, Bool.false_or,
          Bool.true_and]]
      iapply HΦ; itrivial
    · rw [show entryLessB a b = false by simp [entryLessB, Hk, Hif]]
      iapply HΦ; itrivial

end proof

end linkv
end EtcdGrove
end Perennial
