/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__dropped.lean`. Lean-first
(no Rocq counterpart): the counter, then the sender's node told (`isNode` is all its reports
take), the message only read through its getters.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__dropped
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.dropped.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : node.ReportSnapshot.spec (GF := GF) (hG := hG)) :
    Cluster.dropped.spec (GF := GF) (hG := hG) := by
  intro γr vs c sid src ml dq dqe cap st
  wp_start as ⟨#Hcc, #HisRep, Hm⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  ihave #Hctr := isStats_field (c.[RCluster, go!"Stats"]) go!"Dropped" (by decide) $$ Hstats
  iunfold isRep at HisRep
  icases HisRep with ⟨%n, %rst, %sts, %ρ, #HR⟩
  iunfold isReplicaR at HR
  iNamed HR
  ihave #Hrep' := Hrep
  iclear Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_add _ _ $$ [$Hpkg $Hctr]
  wp_apply wp_GetTo.1 ml dq dqe cap st $$ [$Hpbinit $Hm] as Hm
  try wp_auto
  wp_apply wp_ReportUnreachable n γr.cluster kvrRaftN sid st.msg.To' $$ [$Hraftinit $HisNode]
  wp_apply wp_GetType.1 ml dq dqe cap st $$ [$Hpbinit $Hm] as Hm
  try wp_auto
  wp_if_destruct
  · wp_apply wp_GetTo.1 ml dq dqe cap st $$ [$Hpbinit $Hm] as Hm
    try wp_auto
    wp_apply wp_ReportSnapshot n γr.cluster kvrRaftN sid st.msg.To' _ $$ [$Hraftinit $HisNode]
    try wp_auto
    iapply HΦ $$ Hm
  · try wp_auto
    iapply HΦ $$ Hm

end proof

end kvreconf
end EtcdGrove
end Perennial
