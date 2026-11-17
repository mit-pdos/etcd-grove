/-
Lean-first (no Rocq counterpart). The proof of `runtime.Decode`: the decoder's `Decode(data, nil,
nil)`, its object and error returned.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.Decode

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]

theorem runtime.Decode.wp_proof : runtime.Decode.spec (GF := GF) (hG := hG) := by
  intro di dsl P R
  wp_start as ⟨HP, Hdec⟩
  (try wp_auto)
  wp_apply Hdec $$ [$HP] as %x %g %err HR
  (try wp_auto)
  iapply HΦ
  iexact HR

end proof

end EtcdGrove
end Perennial
