/-
Proof of `Spec/cmp/Less.lean`. Lean-first.
-/
module

public import Spec.cmp.Less

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

theorem cmp.Less.wp_proof : cmp.Less.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  iapply HΦ
  ipureintro
  simp

theorem cmp.Less.wp_proofInt32 : cmp.Less.specInt32 (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  iapply HΦ
  ipureintro
  simp

end proof

end EtcdGrove
end Perennial
