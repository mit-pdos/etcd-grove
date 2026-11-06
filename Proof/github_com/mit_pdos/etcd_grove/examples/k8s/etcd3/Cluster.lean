/-
**`MainCluster`'s cluster** (step 1 of "k8s etcd3 over cluster3" in `notes/k8s-etcd3-plan.md`,
2026-11-06): the driver's three-member configuration (`clusterConfig()`, a `cluster3.Config` literal:
the member names `k8setcd3c-1`, `-2`, `-3`, the cluster token `k8setcd3c`, the peer addresses
`127.0.0.1:2404{1,2,3}`, the client addresses `127.0.0.1:2405{1,2,3}`, the bridges'
`127.0.0.1:2406{1,2,3}`, snapshots as `examples/etcd/partition`'s). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The cluster's configuration** (`clusterConfig()`, see the file header). -/
abbrev clusterCfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config :=
  { Token' := go!"k8setcd3c", Name1' := go!"k8setcd3c-1", Name2' := go!"k8setcd3c-2",
    Name3' := go!"k8setcd3c-3",
    Peer1' := go!"127.0.0.1:24041", Peer2' := go!"127.0.0.1:24042", Peer3' := go!"127.0.0.1:24043",
    Client1' := go!"127.0.0.1:24051", Client2' := go!"127.0.0.1:24052",
    Client3' := go!"127.0.0.1:24053",
    Bridge1' := go!"127.0.0.1:24061", Bridge2' := go!"127.0.0.1:24062",
    Bridge3' := go!"127.0.0.1:24063",
    SnapCount' := W64 1, SnapCatchUp' := W64 1 }

/-- **The configuration meets the cluster's specs' premise** (`cluster3.cfgOk`). -/
theorem clusterCfg_ok : cluster3.cfgOk clusterCfg := by
  constructor <;> dsimp only [clusterCfg] <;> (try unfold plainEndpoint) <;> decide

end pure

end k8s_etcd3
end EtcdGrove
end Perennial
