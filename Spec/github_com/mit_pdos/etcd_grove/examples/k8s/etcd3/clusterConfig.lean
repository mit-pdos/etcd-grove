/-
`clusterConfig()` (`examples/k8s/etcd3/k8setcd3.go`; step 1 of "k8s etcd3 over cluster3" in
`notes/k8s-etcd3-plan.md`, 2026-11-06): `MainCluster`'s cluster configuration, a `cluster3.Config` literal. Lean-first.

**The triple:** from the package's `isPkgInit`, `clusterConfig()` returns `clusterCfg`
(`Cluster.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev clusterConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.clusterConfig)) (Val #()))
  {{ RET #clusterCfg; True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
