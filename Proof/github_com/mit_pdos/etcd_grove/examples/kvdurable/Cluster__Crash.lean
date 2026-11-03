/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__Crash.lean`. Lean-first
(no Rocq counterpart).

The loop, until `sleep` reports `stop`, with the crasher's token as its invariant: a random replica
(`c.random()`: its id, read from the incarnation, is a started one) restarted by `Cluster.restart`,
which takes the token and gives it back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Crash
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.sleep
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__restart
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

-- `wp_auto` would unfold the token (to `own`'s model) in the context
attribute [local irreducible] crasher in
theorem Cluster.Crash.wp_proof (wp_sleep : sleep.spec (GF := GF) (hG := hG))
    (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_restart : Cluster.restart.spec (GF := GF) (hG := hG)) :
    Cluster.Crash.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c pause stop γc
  wp_start as ⟨#Hc, Hcr, #Hstop⟩
  -- (not `iunfold isClusterC` in the main context: it unfolds `crasher` too)
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable
    $$ []
  · iunfold isClusterC at Hc
    iNamed Hc
    iexact Hpkg
  try wp_auto
  wp_for Hcr
  wp_apply wp_sleep pause stop γc $$ [$Hpkg $Hstop] as %b -
  wp_if_destruct
  · -- a crash
    wp_apply wp_random γ vs dir c $$ [$Hc] as %r ⟨%id, #Hr, #Hknown⟩
    iunfold isRep at Hr
    icases Hr with ⟨%n, %st, %sts, %sq, %ρ, #HR⟩
    iunfold isReplicaR at HR
    icases HR with ⟨#Hrep, -⟩
    iunfold isReplica at Hrep
    icases Hrep with ⟨-, -, #Hid, -⟩
    try wp_auto
    wp_apply wp_restart γ vs dir c id $$ [$Hc $Hknown $Hcr] as Hcr
    try wp_auto
    wp_for_post
    iframe
  · cases b
    · exact absurd rfl Hif
    simp only [Bool.not_true, _root_.decide_true, ↓reduceIte]
    try wp_auto
    iapply HΦ
    iexact Hcr

end proof

end kvdurable
end EtcdGrove
end Perennial
