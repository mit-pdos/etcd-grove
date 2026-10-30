/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__Reconfigure.lean`.
Lean-first (no Rocq counterpart).

The loop, until `sleep` reports `stop`: a random change (`randomChange`: owned, of a defined
transition), the counter, a timeout context, and `ProposeConfChange` at a random replica's node with
the persistent update `kvr_ccAu_dup` (from the store's invariant, at `γ.dup`); its answer is
dropped.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__Reconfigure
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.sleep
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__randomChange
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.context.WithTimeoutBackground
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientAu
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

theorem Cluster.Reconfigure.wp_proof (wp_sleep : sleep.spec (GF := GF) (hG := hG))
    (wp_randomChange : Cluster.randomChange.spec (GF := GF) (hG := hG))
    (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_ProposeConfChange : node.ProposeConfChange.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Cluster.Reconfigure.spec (GF := GF) (hG := hG) := by
  intro γr vs c pause stop γc
  wp_start as ⟨#Hc, #Hstop⟩
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcnt := isStats_field (c.[RCluster, go!"Stats"]) go!"ConfChangesProposed"
    (by simp [statsFields]) $$ Hstats
  try wp_auto
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  wp_apply wp_sleep pause stop γc $$ [$Hpkg $Hstop] as %b -
  wp_if_destruct
  · -- a change, proposed
    wp_apply wp_randomChange γr vs c $$ [$Hc] as %cc %o ⟨Hcc, %Hto⟩
    wp_apply wp_add _ _ $$ [$Hpkg $Hcnt]
    try wp_auto
    wp_apply context.wp_Background
    try wp_auto
    wp_apply hWT _ $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
    try wp_auto
    wp_apply wp_random γr vs c $$ [$Hc] as %r ⟨%id, #Hr⟩
    iunfold isRep at Hr
    icases Hr with ⟨%n, %st, %sts, %ρ, #HR⟩
    iunfold isReplicaR at HR
    icases HR with ⟨#Hrep, -⟩
    iunfold isReplica at Hrep
    icases Hrep with ⟨-, -, #Hnode, -, -, -, #HisNode, -⟩
    try wp_auto
    ihave #Hpau := kvr_ccAu_dup γr o Hto $$ Hinv
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    wp_apply wp_ProposeConfChange n γr.cluster kvrRaftN id cc o (DFrac.own 1) ctx' cd
      $$ [$Hraftinit $HisNode $Hnc $Hcc $Hpau] as %err -
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
