/-
**`MainPartition`'s cluster** (K6 of `notes/k8s-compactor-plan.md`, 2026-11-05): the compactor
example's three-member configuration (`clusterConfig()`, a `cluster3.Config` literal: the member names
`k8scompactorp-1`, `-2`, `-3`, the cluster token `k8scompactorp`, the peer addresses
`127.0.0.1:2394{1,2,3}`, the client addresses `127.0.0.1:2393{1,2,3}`, the bridges'
`127.0.0.1:2395{1,2,3}`, snapshots as `examples/etcd/partition`'s), and the cluster's premises at it
(`cluster3.premises`). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The cluster's configuration** (`clusterConfig()`, see the file header). -/
abbrev clusterCfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config :=
  { Token' := go!"k8scompactorp", Name1' := go!"k8scompactorp-1", Name2' := go!"k8scompactorp-2",
    Name3' := go!"k8scompactorp-3",
    Peer1' := go!"127.0.0.1:23941", Peer2' := go!"127.0.0.1:23942", Peer3' := go!"127.0.0.1:23943",
    Client1' := go!"127.0.0.1:23931", Client2' := go!"127.0.0.1:23932",
    Client3' := go!"127.0.0.1:23933",
    Bridge1' := go!"127.0.0.1:23951", Bridge2' := go!"127.0.0.1:23952",
    Bridge3' := go!"127.0.0.1:23953",
    SnapCount' := W64 1, SnapCatchUp' := W64 1 }

/-- **The configuration meets the cluster's specs' premise** (`cluster3.cfgOk`). -/
theorem clusterCfg_ok : cluster3.cfgOk clusterCfg := by
  constructor <;> dsimp only [clusterCfg] <;> (try unfold plainEndpoint) <;> decide

end pure

end k8s_compactor
end EtcdGrove
end Perennial
