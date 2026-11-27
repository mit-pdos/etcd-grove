/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__storeBase.lean`: the detached
storage's snapshot (`MemoryStorage.Snapshot`) is at index `0`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.StoreJust
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

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

theorem node.storeBase.wp_proof (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    node.storeBase.spec (GF := GF) (hG := hG) := by
  intro n ms γs h sv hsv
  wp_start as ⟨Hst, #Hlock, Hmeta, Hfresh⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave Hinit := isInitialized_access $$ Hraft
  unfold isInitialized
  iNamed Hinit
  try wp_auto
  ihave Hat : memStorAt ms γs storeJ (some (0, sv)) emp $$ [Hfresh]
  · simp only [memStorAt]; iframe Hlock Hfresh
  ihave #Hc0 := memCompacted_zero γs
  wp_apply wp_Snapshot ms γs storeJ (some (0, sv)) 0 none _ $$ [$Hraft $Hat $Hc0 $ErrSnapUnavail]
    as %snap %err ⟨-, %Herr, %sv', Hs, %Hsv, Ho⟩
  subst Herr
  icases Ho with ⟨%Heq, Hfresh⟩
  subst Heq
  ihave Hs := ownSnapW_E $$ Hs
  ihave Hs := ownSnapE_weaken $$ Hs
  try wp_auto
  wp_apply wp_GetMetadata.1 snap _ sv' $$ [$Hpb $Hs] as %pm ⟨Hpm, -⟩
  wp_apply wp_MdGetIndex pm _ _ $$ [$Hpb $Hpm] as -
  try wp_auto
  rw [hsv]
  iapply HΦ
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
