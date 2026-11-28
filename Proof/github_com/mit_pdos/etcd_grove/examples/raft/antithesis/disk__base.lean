/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/disk__base.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk__base
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem disk.base.wp_proof (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    disk.base.spec (GF := GF) (hG := hG) := by
  intro d w
  wp_start as Hd
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold diskOwn at Hd
  icases Hd with ⟨%hsl, %esl, Hhs, #Hhsr, Hsnap, Hents, #Hes, Hcap⟩
  wp_auto
  wp_apply wp_GetMetadata.2 $$ [$Hpb]
  wp_apply wp_GetIndex null DFrac.discard (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0))
    $$ [$Hpb] as -
  · iunfold smOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
  try wp_auto
  iapply HΦ
  iunfold diskOwn
  iexists hsl, esl
  iframe
  iframe Hhsr Hes

end proof

end AntHarness
end EtcdGrove
end Perennial
