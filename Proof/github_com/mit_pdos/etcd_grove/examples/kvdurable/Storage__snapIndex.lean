/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__snapIndex.lean`. Lean-first
(no Rocq counterpart).

`MemoryStorage.Snapshot` (never an error; the clone whole, `ownSnapW`), its metadata's index read
through the getters: the stored snapshot's index in the detached mode, at least the known
compaction point attached.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__snapIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.go_etcd_io.raft.v3.InvPbLog

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

theorem Storage.snapIndex.wp_proof
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    Storage.snapIndex.spec (GF := GF) (hG := hG) := by
  intro s ms γs J o c
  wp_start as ⟨#Hrec, Hat, #Hc⟩
  ihave #Hrec' := Hrec
  iunfold kdStorRec at Hrec'
  icases Hrec' with ⟨#Hf, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  -- what the call does not give back (the lock, or the invariant) is persistent: kept
  cases o with
  | none =>
    iunfold memStorAt at Hat
    icases Hat with ⟨#Hkeep, Hp⟩
    ihave Hat : memStorAt ms γs J none emp $$ [Hp]
    · simp only [memStorAt]; iframe Hkeep Hp
    try wp_auto
    wp_apply wp_Snapshot ms γs J none c false _ $$ [$Hraft $Hat $Hc $ErrSnapUnavail]
      as %snap %err ⟨-, %Herr, %sv, Hs, %Hsv, Ho⟩
    · iempintro
    ihave Hs := ownSnapW_E $$ Hs
    ihave Hs := ownSnapE_weaken $$ Hs
    try wp_auto
    wp_apply wp_GetMetadata.1 snap _ sv $$ [$Hpb $Hs] as %pm ⟨Hpm, -⟩
    wp_apply wp_MdGetIndex pm _ _ $$ [$Hpb $Hpm] as -
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact Hsv.1
    simp only
    iexact Hkeep
  | some p =>
    obtain ⟨c0, sv0⟩ := p
    iunfold memStorAt at Hat
    icases Hat with ⟨#Hkeep, Hp⟩
    ihave Hat : memStorAt ms γs J (some (c0, sv0)) emp $$ [Hp]
    · simp only [memStorAt]; iframe Hkeep Hp
    try wp_auto
    wp_apply wp_Snapshot ms γs J (some (c0, sv0)) c false _ $$ [$Hraft $Hat $Hc $ErrSnapUnavail]
      as %snap %err ⟨-, %Herr, %sv, Hs, %Hsv, Ho⟩
    · iempintro
    ihave Hs := ownSnapW_E $$ Hs
    ihave Hs := ownSnapE_weaken $$ Hs
    try wp_auto
    wp_apply wp_GetMetadata.1 snap _ sv $$ [$Hpb $Hs] as %pm ⟨Hpm, -⟩
    wp_apply wp_MdGetIndex pm _ _ $$ [$Hpb $Hpm] as -
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact Hsv.1
    simp only
    icases Ho with ⟨%Heq, Hfr⟩
    subst Heq
    iframe Hkeep Hfr
    ipureintro; rfl

end proof

end kvdurable
end EtcdGrove
end Perennial
