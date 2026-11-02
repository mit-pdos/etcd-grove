/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/putSnapshot.lean`. Lean-first (no
Rocq counterpart): the getters lend the snapshot's parts (its metadata split in two, `dfrac_split`:
one part lends its conf state, `csOptA_csOpt_acc`, the other is read for the index and term), each
written with `putUint64`/`putIDs`/`putBytes`, then given back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putUint64
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putIDs
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putBytes
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearnersNext
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetAutoLeave
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.SnapLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

theorem putSnapshot.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_putIDs : putIDs.spec (GF := GF) (hG := hG))
    (wp_putBytes : putBytes.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Snapshot.GetData.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_GetLearnersNext : raftpb.ConfState.GetLearnersNext.spec (GF := GF) (hG := hG))
    (wp_GetAutoLeave : raftpb.ConfState.GetAutoLeave.spec (GF := GF) (hG := hG)) :
    putSnapshot.spec (GF := GF) (hG := hG) := by
  intro buf B p dq s
  wp_start as ⟨Hbuf, Hcap, Hs⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetMetadata.1 p dq s $$ [$Hpb $Hs] as %pm ⟨Hsm, Hback1⟩
  obtain ⟨dq1, dq2, Hdq⟩ := dfrac_split dq
  subst Hdq
  icases smOpt_split _ _ _ _ $$ Hsm with ⟨Hsm1, Hsm2⟩
  try wp_auto
  wp_apply wp_GetConfState pm dq1 s.Metadata' $$ [$Hpb $Hsm1] as %pc ⟨Hcs, Hback2⟩
  icases csOptA_csOpt_acc _ _ _ $$ Hcs with ⟨%dq', Hcs, Hback3⟩
  try wp_auto
  wp_apply wp_GetIndex pm dq2 s.Metadata' $$ [$Hpb $Hsm2] as Hsm2
  wp_apply wp_putUint64 buf B _ $$ [$Hbuf $Hcap] as %b1 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetTerm pm dq2 s.Metadata' $$ [$Hpb $Hsm2] as Hsm2
  wp_apply wp_putUint64 b1 _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetVoters pc dq' _ $$ [$Hpb $Hcs] as %sv ⟨Hsv, Hcb⟩
  wp_apply wp_putIDs b2 sv _ _ dq' $$ [$Hb $Hcap $Hsv] as %b3 ⟨Hb, Hcap, Hsv⟩
  ihave Hcs := Hcb $$ Hsv
  try wp_auto
  wp_apply wp_GetLearners pc dq' _ $$ [$Hpb $Hcs] as %sl ⟨Hsl, Hcb⟩
  wp_apply wp_putIDs b3 sl _ _ dq' $$ [$Hb $Hcap $Hsl] as %b4 ⟨Hb, Hcap, Hsl⟩
  ihave Hcs := Hcb $$ Hsl
  try wp_auto
  wp_apply wp_GetVotersOutgoing pc dq' _ $$ [$Hpb $Hcs] as %so ⟨Hso, Hcb⟩
  wp_apply wp_putIDs b4 so _ _ dq' $$ [$Hb $Hcap $Hso] as %b5 ⟨Hb, Hcap, Hso⟩
  ihave Hcs := Hcb $$ Hso
  try wp_auto
  wp_apply wp_GetLearnersNext pc dq' _ $$ [$Hpb $Hcs] as %sn ⟨Hsn, Hcb⟩
  wp_apply wp_putIDs b5 sn _ _ dq' $$ [$Hb $Hcap $Hsn] as %b6 ⟨Hb, Hcap, Hsn⟩
  ihave Hcs := Hcb $$ Hsn
  try wp_auto
  wp_apply wp_GetAutoLeave pc dq' _ $$ [$Hpb $Hcs] as Hcs
  ihave Hcs := Hback3 $$ Hcs
  ihave Hsm1 := Hback2 $$ Hcs
  ihave Hsm := smOpt_combine _ _ _ _ $$ [$Hsm1 $Hsm2]
  ihave Hs := Hback1 $$ Hsm
  -- the auto-leave byte (`autoB`), then the data
  have Hdata : ∀ (byte : w8), byte = autoB s.Metadata'.ConfState'.AutoLeave' →
      B ++ u64Le s.Metadata'.Index' ++ u64Le s.Metadata'.Term' ++
          encIDs s.Metadata'.ConfState'.Voters' ++ encIDs s.Metadata'.ConfState'.Learners' ++
          encIDs s.Metadata'.ConfState'.VotersOutgoing' ++
          encIDs s.Metadata'.ConfState'.LearnersNext' ++ [byte] ++ putB s.Data' =
        B ++ encSnap s := by
    intro byte h
    subst h
    simp only [encSnap, encConf, List.append_assoc, List.cons_append]
  cases Hif : s.Metadata'.ConfState'.AutoLeave'
  all_goals (
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b7 ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_GetData.1 p (dq1 • dq2) s $$ [$Hpb $Hs] as %ds ⟨Hd, Hdb⟩
    wp_apply wp_putBytes b7 ds _ _ (dq1 • dq2) $$ [$Hb $Hcap $Hd] as %b8 ⟨Hb, Hcap, Hd⟩
    ihave Hs := Hdb $$ Hd
    try wp_auto
    iapply HΦ
    iframe Hcap Hs)
  · rw [Hdata (W8 0) (by simp [autoB, Hif])]; iexact Hb
  · rw [Hdata (W8 1) (by simp [autoB, Hif])]; iexact Hb

end proof

end kvdurable
end EtcdGrove
end Perennial
