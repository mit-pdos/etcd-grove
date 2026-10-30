/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__randomID.lean`.
Lean-first (no Rocq counterpart).

`startNew` if `add` and one time in four (its id if it started one); else the conf state's voters,
outgoing voters and learners appended into a fresh slice, and a random replica's id (`isRep`'s
read-only `id` field) if that is empty or one time in four, else `pick` of it (not empty).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__randomID
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__startNew
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.pick
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners

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

theorem Cluster.randomID.wp_proof (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_startNew : Cluster.startNew.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG)) :
    Cluster.randomID.spec (GF := GF) (hG := hG) := by
  intro γr vs c csp cs add
  wp_start as ⟨#Hc, #Hcs⟩
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  -- a fresh replica's id, sometimes
  cases add <;> try wp_auto
  rotate_left
  wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
  cases b <;> try wp_auto
  rotate_left
  wp_apply wp_startNew γr vs c $$ [$Hc] as %id0 %ok -
  try wp_auto
  cases ok <;> try wp_auto
  rotate_left
  · iapply HΦ; itrivial
  -- the configuration's ids
  all_goals
    wp_apply wp_GetVoters csp DFrac.discard cs $$ [$Hpb $Hcs] as %sv ⟨#Hsv, -⟩
    ihave Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
    ihave Hncap := ownSliceCap_nil (V := w64) (GF := GF)
    wp_apply wp_slice_append slice.nil [] sv cs.Voters' DFrac.discard $$ [$Hnil $Hncap $Hsv]
      as %m1 ⟨Hm1, Hm1cap, -⟩
    wp_apply wp_GetVotersOutgoing csp DFrac.discard cs $$ [$Hpb $Hcs] as %so ⟨#Hso, -⟩
    wp_apply wp_slice_append m1 _ so cs.VotersOutgoing' DFrac.discard $$ [$Hm1 $Hm1cap $Hso]
      as %m2 ⟨Hm2, Hm2cap, -⟩
    wp_apply wp_GetLearners csp DFrac.discard cs $$ [$Hpb $Hcs] as %sl ⟨#Hsl, -⟩
    wp_apply wp_slice_append m2 _ sl cs.Learners' DFrac.discard $$ [$Hm2 $Hm2cap $Hsl]
      as %m3 ⟨Hm3, -, -⟩
    try wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hm3
    wp_if_destruct
    · try wp_auto
      wp_apply wp_random γr vs c $$ [$Hc] as %r1 ⟨%id1, #Hr1⟩
      iunfold isRep at Hr1
      icases Hr1 with ⟨%n1, %st1, %sts1, %ρ1, #HR1⟩
      iunfold isReplicaR at HR1
      icases HR1 with ⟨#Hrep1, -⟩
      iunfold isReplica at Hrep1
      icases Hrep1 with ⟨-, #Hid1, -⟩
      try wp_auto
      iapply HΦ; itrivial
    · have Hlen0 := Hif
      wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
      wp_if_destruct
      · try wp_auto
        have Hne : [] ++ cs.Voters' ++ cs.VotersOutgoing' ++ cs.Learners' ≠ [] := by
          intro h; rw [h] at Hlen; simp at Hlen; apply Hlen0; word
        wp_apply wp_pick _ _ _ Hne $$ [$Hm3] as %x -
        iapply HΦ; itrivial
      · try wp_auto
        wp_apply wp_random γr vs c $$ [$Hc] as %r1 ⟨%id1, #Hr1⟩
        iunfold isRep at Hr1
        icases Hr1 with ⟨%n1, %st1, %sts1, %ρ1, #HR1⟩
        iunfold isReplicaR at HR1
        icases HR1 with ⟨#Hrep1, -⟩
        iunfold isReplica at Hrep1
        icases Hrep1 with ⟨-, #Hid1, -⟩
        try wp_auto
        iapply HΦ; itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
