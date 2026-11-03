/-
kvreconf's proof (the same Go text), ported. Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__Reconfigure.lean`.
Lean-first (no Rocq counterpart).

The loop, until `sleep` reports `stop`: a random change (`randomChange`: owned, of a defined
transition), the counter, a timeout context, and `ProposeConfChange` at a random replica's node with
the persistent update `kd_ccAu_dup` (from the store's invariant, at `γ.dup`); its answer is
dropped.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Reconfigure
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.sleep
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__randomChange
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.context.WithTimeoutBackground
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ReconfAu
public import Proof.go_etcd_io.raft.v3.InvNodeCtx

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

theorem Cluster.Reconfigure.wp_proof (wp_sleep : sleep.spec (GF := GF) (hG := hG))
    (wp_randomChange : Cluster.randomChange.spec (GF := GF) (hG := hG))
    (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_ProposeConfChange : node.ProposeConfChange.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Cluster.Reconfigure.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c pause stop γc
  wp_start as ⟨#Hc, #Hstop⟩
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcnt := isStats_field (c.[KCluster, go!"Stats"]) go!"ConfChangesProposed"
    (by simp [statsFields]) $$ Hstats
  try wp_auto
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  wp_apply wp_sleep pause stop γc $$ [$Hpkg $Hstop] as %b -
  wp_if_destruct
  · -- a change, proposed
    wp_apply wp_randomChange γ vs dir c $$ [$Hc] as %cc %o ⟨Hcc, %Hto⟩
    wp_apply wp_add _ _ $$ [$Hpkg $Hcnt]
    try wp_auto
    wp_apply context.wp_Background
    try wp_auto
    wp_apply hWT _ $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
    try wp_auto
    wp_apply wp_random γ vs dir c $$ [$Hc] as %r ⟨%id, #Hr, -⟩
    iunfold isRep at Hr
    icases Hr with ⟨%n, %st, %sts, %sq, %ρ, #HR⟩
    iunfold isReplicaR at HR
    icases HR with ⟨#Hrep, -⟩
    iunfold isReplica at Hrep
    icases Hrep with ⟨-, -, -, -, #Hnode, -, -, -, -, -, #HisNode, -⟩
    try wp_auto
    ihave #Hpau := kd_ccAu_dup γ o Hto $$ Hinv
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    wp_apply wp_ProposeConfChange n γ.r.cluster kdRaftN id cc o (DFrac.own 1) ctx' cd
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

end kvdurable
end EtcdGrove
end Perennial
