/- Lean-first (no Rocq counterpart). The proof of `check`: the condition holds, so no panic. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check

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

theorem check.wp_proof : check.spec (GF := GF) (hG := hG) := by
  intro ok msg
  wp_start as %Hok
  subst Hok
  wp_auto
  iapply HΦ; itrivial

end proof

end mvccrand
end EtcdGrove
end Perennial
