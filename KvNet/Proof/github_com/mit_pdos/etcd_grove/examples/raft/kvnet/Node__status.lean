/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Node__status.lean`, at the store's replica
(`kvRep`, `Facts.lean`). Lean-first (no Rocq counterpart). The replica's `contents` (a fresh copy of the
store's map, the index, the configuration), raft's `Status` (its hard state read through
`statusOwn_hardState`), the counters (`Stats.Snapshot`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__status
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__current
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica__contents
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__Snapshot
public import KvNet.Spec.go_etcd_io.raft.v3.node__Status
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Facts

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Node.status.wp_proof
    (wp_contents : Replica.contents.spec (GF := GF) (hG := hG))
    (wp_Status : node.Status.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Snapshot : Stats.Snapshot.spec (GF := GF) (hG := hG))
    (γk : KdNames) (vs : List w64) (dir : GoString) (F : KvFacts GF) (stp : NodeStopper GF)
    (wp_current : Node.current.spec (GF := GF) (hG := hG) F (kvRep γk vs dir) stp) :
    Node.status.spec (GF := GF) (hG := hG) F (kvRep γk vs dir) stp := by
  intro nd γ N id
  wp_start as #Hnd
  ihave #Hnd' := Hnd
  iunfold isNodeS at Hnd'
  icases Hnd' with ⟨%cfg, %Mc, %sp, %f, -, -, -, #Hsp, #Hst, -, -, -, -, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  -- (2026-11-24, G5) the current incarnation's replica, read once
  wp_apply wp_current nd γ N id $$ [$Hpkg $Hnd] as %r ⟨%n, #Hrn, #Hrep, #HisN⟩
  iunfold kvRep at Hrep
  try wp_auto
  wp_apply wp_contents γk vs dir id r $$ [$Hrep] as %m %idx %csp ⟨%M, %c, HM, %HMf, #Hcs⟩
  try wp_auto
  wp_apply wp_Status n γ N id $$ [$Hraft $HisN] as %st Hso
  ihave ⟨Hso, %hs, #Hhs⟩ := statusOwn_hardState st $$ Hso
  try wp_auto
  iunfold hsOpt at Hhs
  icases Hhs with (%Hnil | #Hro)
  · obtain ⟨Hp, -⟩ := Hnil
    rw [Hp]
    wp_apply wp_GetTerm.2 $$ [$Hpb]
    try wp_auto
    rw [Hp]
    wp_apply wp_GetCommit.2 $$ [$Hpb]
    try wp_auto
    wp_apply wp_Snapshot sp $$ [$Hpkg $Hst] as %v %Hvl
    try wp_auto
    iapply HΦ
    iexists M, c
    isplitl [HM]
    · iexact HM
    iframe Hcs
    ipureintro; exact Hvl
  · wp_apply wp_GetTerm.1 _ hs $$ [$Hpb $Hro]
    try wp_auto
    wp_apply wp_GetCommit.1 _ hs $$ [$Hpb $Hro]
    try wp_auto
    wp_apply wp_Snapshot sp $$ [$Hpkg $Hst] as %v %Hvl
    try wp_auto
    iapply HΦ
    iexists M, c
    isplitl [HM]
    · iexact HM
    iframe Hcs
    ipureintro; exact Hvl

end proof

end raft_kvnet
end EtcdGrove
end Perennial
