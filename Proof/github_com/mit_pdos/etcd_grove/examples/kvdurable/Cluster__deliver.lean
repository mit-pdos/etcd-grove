/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__deliver.lean`. Lean-first
(no Rocq counterpart).

The target is looked up by the message's `To` (`Cluster.replica`, not known to be started): `nil`
or the running replica of that id, which `step` takes. A drop only reads the message (`dropped`).
The delayed delivery's goroutine takes the message and its resources. A duplicate is a fresh copy
(`copyMsg`) of the owned message, before it is stepped; the credits are made persistent
(`msgCredits_copy`, `γ.dup = true`: `isClusterC`) and `sentMsg` is, so both steps get them.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__replica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__dropped
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__step
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.copyMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.below
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Perennial.Proof.time.Link
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

theorem Cluster.deliver.wp_proof
    (wp_replica : Cluster.replica.spec (GF := GF) (hG := hG))
    (wp_dropped : Cluster.dropped.spec (GF := GF) (hG := hG))
    (wp_step : Cluster.step.spec (GF := GF) (hG := hG))
    (wp_copyMsg : copyMsg.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    Cluster.deliver.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c sid src ml st
  wp_start as ⟨#Hcc, #Hsrc, Hm, #Hsent, Hcred⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetTo.1 ml _ _ _ _ $$ [$Hpbinit $Hm] as Hm
  wp_apply wp_replica γ vs dir c st.msg.To' false $$ [$Hcc] as %dst Hdst
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  try wp_auto
  wp_if_destruct
  · -- no target: dropped
    wp_apply wp_dropped γ vs dir c sid src ml _ _ _ _ $$ [$Hcc $Hsrc $Hm] as -
    try wp_auto
    iapply HΦ
    itrivial
  wp_apply wp_oneIn (W64 20) (by decide) $$ [$Hpkg] as %b1 -
  cases b1
  · icases Hdst with (%Hn | #Hdst)
    · exact absurd Hn Hif
    try wp_auto
    wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b2 -
    cases b2
    · -- now, perhaps twice
      try wp_auto
      wp_apply wp_oneIn (W64 32) (by decide) $$ [$Hpkg] as %b3 -
      cases b3
      · try wp_auto
        wp_apply wp_step γ vs dir c sid src dst ml st $$ [$Hcc $Hsrc $Hdst $Hm $Hsent $Hcred]
        try wp_auto
        iapply HΦ
        itrivial
      · try wp_auto
        wp_apply wp_copyMsg ml _ _ _ _ $$ [$Hpkg $Hm] as %l' ⟨Hm, Hl'⟩
        ihave #Hcred := msgCredits_copy γ.r.cluster kdRaftN st Hdup $$ Hcred
        try wp_auto
        wp_apply wp_step γ vs dir c sid src dst ml st $$ [$Hcc $Hsrc $Hdst $Hm $Hsent $Hcred]
        try wp_auto
        wp_if_destruct
        · try wp_auto
          iapply HΦ
          itrivial
        · ihave #Hctr := isStats_field (c.[KCluster, go!"Stats"]) go!"Duplicated" (by decide)
            $$ Hstats
          wp_apply wp_add _ _ $$ [$Hpkg $Hctr]
          wp_apply wp_step γ vs dir c sid src dst l' st $$ [$Hcc $Hsrc $Hdst $Hl' $Hsent $Hcred]
          try wp_auto
          iapply HΦ
          itrivial
    · -- later, from another goroutine
      ihave #Hctr := isStats_field (c.[KCluster, go!"Stats"]) go!"Delayed" (by decide) $$ Hstats
      try wp_auto
      wp_apply wp_add _ _ $$ [$Hpkg $Hctr]
      wp_apply wp_below (W64 20) $$ [$Hpkg] as %d -
      try wp_auto
      wp_apply wp_fork $$ [delay c m src dst Hm Hcred]
      · try wp_auto
        wp_apply time.wp_Sleep
        try wp_auto
        wp_apply wp_step γ vs dir c sid src dst ml st $$ [$Hcc $Hsrc $Hdst $Hm $Hsent $Hcred]
        try wp_auto
        itrivial
      try wp_auto
      iapply HΦ
      itrivial
  · -- dropped by chance
    try wp_auto
    wp_apply wp_dropped γ vs dir c sid src ml _ _ _ _ $$ [$Hcc $Hsrc $Hm] as -
    try wp_auto
    iapply HΦ
    itrivial

end proof

end kvdurable
end EtcdGrove
end Perennial
