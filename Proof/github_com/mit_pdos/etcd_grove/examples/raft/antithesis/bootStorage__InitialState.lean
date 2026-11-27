/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/bootStorage__InitialState.lean`:
`MemoryStorage.InitialState` (detached: the hard state, the stored snapshot's conf state
read-only), then `MemoryStorage.Snapshot` (detached, as kvdurable's `snapIndex`) and the snapshot's
index: at `0` a fresh `ConfState{Voters: s.voters}`, frozen read-only (`csPts_of_struct_ro`, as
kv's `Storage.InitialState`), otherwise the storage's conf state.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- Justifications nothing reads (the detached `Snapshot` call names none). -/
private def trivJ : MemJust GF where
  SV _ := iprop(True)
  B _ := iprop(True)
  DL _ := iprop(True)
  SV_pers _ := inferInstance
  B_pers _ := inferInstance
  B_timeless _ := inferInstance
  DL_pers _ := inferInstance

theorem bootStorage.InitialState.wp_proof
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    bootStorage.InitialState.spec (GF := GF) (hG := hG) := by
  intro s ms vs γs hs c sv esu
  wp_start as ⟨#Hrec, #Hlock, Hmeta, Hfresh, #Hesu⟩
  iunfold bootStorRec at Hrec
  icases Hrec with ⟨%vsl, #Hms, #Hvsl, #Hvs⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_InitialState ms γs hs c sv $$ [$Hraft $Hmeta $Hfresh]
    as %hp %cs0 ⟨#Hhs, Hmeta, Hfresh, #Hcs0⟩
  try wp_auto
  ihave Hat : memStorAt ms γs trivJ (some (c, sv)) emp $$ [Hfresh]
  · simp only [memStorAt]; iframe Hlock Hfresh
  ihave #Hc0 := memCompacted_zero γs
  wp_apply wp_Snapshot ms γs trivJ (some (c, sv)) 0 none esu $$ [$Hraft $Hat $Hc0 $Hesu]
    as %snap %err ⟨-, %Herr, %sv', Hs, %Hsv, Ho⟩
  subst Herr
  icases Ho with ⟨%Heq, Hfresh⟩
  subst Heq
  ihave Hs := ownSnapW_E $$ Hs
  ihave Hs := ownSnapE_weaken $$ Hs
  try wp_auto
  wp_apply wp_GetMetadata.1 snap _ sv' $$ [$Hpb $Hs] as %pm ⟨Hpm, -⟩
  wp_apply wp_MdGetIndex pm _ _ $$ [$Hpb $Hpm] as -
  iapply wp_fupd
  try wp_auto
  wp_if_destruct
  · irename «$r1» => Hcs
    generalize «$r1_ptr» = cs at *
    -- `&pb.ConfState{Voters: s.voters}`: the voters read-only, the other slices `nil`,
    -- `AutoLeave` `nil`, frozen
    imod csPts_of_struct_ro cs
        (⟨zero_val _, vsl, slice.nil, slice.nil, slice.nil, null, slice.nil, 0⟩ : raftpb.ConfState)
        (bootConfState vs sv') ⊤ rfl $$ [Hcs] with #Hcs
    · iframe Hcs
      simp only [bootConfState, if_pos Hif]
      iframe Hvs
      repeat (isplitr; · iapply ownSlice_nil)
      iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
    imodintro
    iapply HΦ
    iframe Hhs Hmeta Hfresh Hcs
  · try wp_auto
    imodintro
    iapply HΦ
    rw [show bootConfState vs sv' = sv'.Metadata'.ConfState' by rw [bootConfState, if_neg Hif]]
    iframe Hhs Hmeta Hfresh Hcs0

end proof

end AntHarness
end EtcdGrove
end Perennial
