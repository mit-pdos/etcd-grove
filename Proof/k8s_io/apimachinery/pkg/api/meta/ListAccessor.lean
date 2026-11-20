/-
Lean-first (no Rocq counterpart).

The proof of `meta.ListAccessor` on a value in `meta.List`'s type set: the type switch's first case
(k8s 7g follow-up (B'), `notes/k8s-7g-listaccessor-bprime.md`; until then an axiom).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor

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

theorem ListAccessor.wp_proof : ListAccessor.spec (GF := GF) (hG := hG) := by
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
