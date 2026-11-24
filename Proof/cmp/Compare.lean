/-
Proof of `Spec/cmp/Compare.lean`. Lean-first.
-/
module

public import Spec.cmp.Compare

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.cmp.Assumptions]

theorem cmp.Compare.wp_proof : cmp.Compare.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    ipureintro
    simp only [Hif, ↓reduceIte]
    rfl
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      ipureintro
      sorry
    · (try wp_auto)
      iapply HΦ
      ipureintro
      sorry

end proof

end EtcdGrove
end Perennial
