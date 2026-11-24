/- Lean-first (no Rocq counterpart).

Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/FileOf.lean` (kvdurable's
`Cluster.fileOf`, without the cluster).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.FileOf
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.itoa

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem FileOf.wp_proof (wp_itoa : itoa.spec (GF := GF) (hG := hG)) :
    FileOf.spec (GF := GF) (hG := hG) := by
  intro dir id
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_itoa id $$ [$Hpkg]
  unfold kdFileName
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
