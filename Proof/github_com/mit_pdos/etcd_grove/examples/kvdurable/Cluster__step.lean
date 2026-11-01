/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__step.lean`. Lean-first
(no Rocq counterpart).


-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__step
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Spec.context.WithTimeoutBackground
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.step.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Cluster.step.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c sid src dst ml st
  wp_start as ⟨#Hcc, #Hsrc, #Hdst, Hm, #Hsent, Hcred⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  ihave #HctrD := isStats_field (c.[KCluster, go!"Stats"]) go!"Dropped" (by decide) $$ Hstats
  ihave #HctrS := isStats_field (c.[KCluster, go!"Stats"]) go!"SnapshotsSent" (by decide) $$ Hstats
  iclear Hstats
  iunfold isRep at Hdst
  icases Hdst with ⟨%dn, %dstl, %dsts, %dsq, %dρ, #HD⟩
  iunfold isReplicaR at HD
  icases HD with ⟨#HDrep, -⟩
  iunfold isReplica at HDrep
  icases HDrep with ⟨-, -, -, -, #HDnode, -, -, -, -, -, #HDisNode, -⟩
  iunfold isRep at Hsrc
  icases Hsrc with ⟨%n, %rst, %sts, %sq0, %ρ, #HR⟩
  iunfold isReplicaR at HR
  icases HR with ⟨#HSrep, -⟩
  iunfold isReplica at HSrep
  icases HSrep with ⟨-, -, -, -, #HSnode, -, -, -, -, -, #HSisNode, -⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hpbinit $Hm] as Hm
  wp_apply wp_GetTo.1 ml _ _ _ _ $$ [$Hpbinit $Hm] as Hm
  try wp_auto
  wp_apply context.wp_Background
  try wp_auto
  wp_apply hWT _ $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
  try wp_auto
  ihave #Hnc : nodeCtx ctx' cd $$ []
  · unfold nodeCtx; iright; iexact Hctx
  imod stepIn_intro γ.r.cluster kdRaftN st.msg.To' ml sid st rfl $$ [$Hsent $Hm $Hcred] with Hin
  wp_apply wp_node_Step dn γ.r.cluster kdRaftN st.msg.To' ml ctx' cd
    $$ [$Hraftinit $HDisNode $Hnc $Hin] as %err #Herr
  try wp_auto
  wp_apply Hcancel
  try wp_auto
  cases err with
  | nil =>
    -- taken
    try wp_auto
    wp_if_destruct
    · wp_apply wp_add _ _ $$ [$Hpkg $HctrS]
      wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b8 -
      cases b8
      all_goals
        try wp_auto
        wp_apply wp_ReportSnapshot n γ.r.cluster kdRaftN sid st.msg.To' _ $$ [$Hraftinit $HSisNode]
        try wp_auto
        iapply HΦ
        itrivial
    · try wp_auto
      iapply HΦ
      itrivial
  | ok e1 =>
    -- not taken (timed out, or the target stopped): dropped
    try wp_auto
    wp_apply wp_add _ _ $$ [$Hpkg $HctrD]
    wp_apply wp_ReportUnreachable n γ.r.cluster kdRaftN sid st.msg.To' $$ [$Hraftinit $HSisNode]
    try wp_auto
    wp_if_destruct
    · wp_apply wp_ReportSnapshot n γ.r.cluster kdRaftN sid st.msg.To' _ $$ [$Hraftinit $HSisNode]
      try wp_auto
      iapply HΦ
      itrivial
    · try wp_auto
      iapply HΦ
      itrivial

end proof

end kvdurable
end EtcdGrove
end Perennial
