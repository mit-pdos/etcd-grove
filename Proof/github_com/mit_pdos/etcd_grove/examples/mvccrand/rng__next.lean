/- Lean-first (no Rocq counterpart). The proof of `rng.next`: straight-line arithmetic. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__next

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

theorem rng.next.wp_proof : rng.next.spec (GF := GF) (hG := hG) := by
  intro r g
  wp_start as Hr
  wp_auto
  iapply HΦ
  iexists _
  iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
