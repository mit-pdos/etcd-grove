/- Lean-first (no Rocq counterpart). The proof of `noCluster.Version`: it returns `nil`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.noCluster__Version

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

theorem noCluster.Version.wp_proof : noCluster.Version.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro; rfl

end proof

end mvccrand
end EtcdGrove
end Perennial
