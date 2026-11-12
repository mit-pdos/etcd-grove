/-
Lean-first (no Rocq counterpart).

The proof of `meta.Accessor` on a `metav1.Object`: the type switch's first case.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimeta

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

theorem Accessor.wp_proof : Accessor.spec (GF := GF) (hG := hG) := by
  intro ii hty
  wp_start
  wp_auto
  simp only [hty, ↓reduceIte]
  wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end apimeta
end EtcdGrove
end Perennial
