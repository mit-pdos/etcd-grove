/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__Disrupt.lean`.
Lean-first (no Rocq counterpart).

The loop, until `sleep` reports `stop`: a random replica, a timeout context, and one of raft's
calls at its node (`isNode`, from `isReplica`), over the context: `TransferLeadership` (to a random
replica's id, from the leader `Status` reports), `Campaign` or `ForgetLeader`; the answers are
dropped.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__Disrupt
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.sleep
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Spec.go_etcd_io.raft.v3.node__TransferLeadership
public import Spec.go_etcd_io.raft.v3.node__Campaign
public import Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import Spec.go_etcd_io.raft.v3.node__Status
public import Spec.context.WithTimeoutBackground
public import Proof.go_etcd_io.raft.v3.InvNodeCtx

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

theorem Cluster.Disrupt.wp_proof (wp_sleep : sleep.spec (GF := GF) (hG := hG))
    (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_TransferLeadership : node.TransferLeadership.spec (GF := GF) (hG := hG))
    (wp_Campaign : node.Campaign.spec (GF := GF) (hG := hG))
    (wp_ForgetLeader : node.ForgetLeader.spec (GF := GF) (hG := hG))
    (wp_Status : node.Status.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Cluster.Disrupt.spec (GF := GF) (hG := hG) := by
  intro γr vs c pause stop γc
  wp_start as ⟨#Hc, #Hstop⟩
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  try wp_auto
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  wp_apply wp_sleep pause stop γc $$ [$Hpkg $Hstop] as %b -
  wp_if_destruct
  · -- a disruption
    wp_apply wp_random γr vs c $$ [$Hc] as %r ⟨%id, #Hr⟩
    iunfold isRep at Hr
    icases Hr with ⟨%n, %st, %sts, %ρ, #HR⟩
    iunfold isReplicaR at HR
    icases HR with ⟨#Hrep, -⟩
    iunfold isReplica at Hrep
    icases Hrep with ⟨-, -, #Hnode, -, -, -, #HisNode, -⟩
    try wp_auto
    wp_apply context.wp_Background
    try wp_auto
    wp_apply hWT _ $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
    try wp_auto
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    wp_apply wp_below (W64 3) as %k -
    try wp_auto
    wp_if_destruct
    · -- a leadership transfer to a random replica
      try wp_auto
      wp_apply wp_Status n γr.cluster kvrRaftN id $$ [$Hraftinit $HisNode] as %st0 -
      try wp_auto
      wp_apply wp_random γr vs c $$ [$Hc] as %r2 ⟨%id2, #Hr2⟩
      iunfold isRep at Hr2
      icases Hr2 with ⟨%n2, %st2, %sts2, %ρ2, #HR2⟩
      iunfold isReplicaR at HR2
      icases HR2 with ⟨#Hrep2, -⟩
      iunfold isReplica at Hrep2
      icases Hrep2 with ⟨-, #Hid2, -⟩
      try wp_auto
      wp_apply wp_TransferLeadership n γr.cluster kvrRaftN id _ _ ctx' cd
        $$ [$Hraftinit $HisNode $Hnc]
      try wp_auto
      wp_apply Hcancel
      try wp_auto
      wp_for_post
      iframe
    wp_if_destruct
    · -- a campaign
      try wp_auto
      wp_apply wp_Campaign n γr.cluster kvrRaftN id ctx' cd $$ [$Hraftinit $HisNode $Hnc] as %err -
      try wp_auto
      wp_apply Hcancel
      try wp_auto
      wp_for_post
      iframe
    · -- the leader forgotten
      try wp_auto
      wp_apply wp_ForgetLeader n γr.cluster kvrRaftN id ctx' cd $$ [$Hraftinit $HisNode $Hnc]
        as %err -
      try wp_auto
      wp_apply Hcancel
      try wp_auto
      wp_for_post
      iframe
  · cases b
    · exact absurd rfl Hif
    simp only [Bool.not_true, _root_.decide_true, ↓reduceIte]
    try wp_auto
    iapply HΦ
    itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
