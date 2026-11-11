/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/clusterConfig.lean`. Lean-first:
the struct literal, stored and loaded.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.clusterConfig

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem clusterConfig.wp_proof : clusterConfig.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
