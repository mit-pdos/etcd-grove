/-
Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/putConfState.lean`: the
getters lend the four id lists in turn (`putIDs` each), then auto-leave's byte, as `putSnapshot`'s
configuration part.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putConfState
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putIDs
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearnersNext
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetAutoLeave

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

theorem putConfState.wp_proof (wp_putIDs : putIDs.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_GetLearnersNext : raftpb.ConfState.GetLearnersNext.spec (GF := GF) (hG := hG))
    (wp_GetAutoLeave : raftpb.ConfState.GetAutoLeave.spec (GF := GF) (hG := hG)) :
    putConfState.spec (GF := GF) (hG := hG) := by
  intro buf B p dq c
  wp_start as ⟨Hb, Hcap, Hcs⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetVoters p dq _ $$ [$Hpb $Hcs] as %sv ⟨Hsv, Hcb⟩
  wp_apply wp_putIDs buf sv _ _ dq $$ [$Hb $Hcap $Hsv] as %b1 ⟨Hb, Hcap, Hsv⟩
  ihave Hcs := Hcb $$ Hsv
  try wp_auto
  wp_apply wp_GetLearners p dq _ $$ [$Hpb $Hcs] as %sl ⟨Hsl, Hcb⟩
  wp_apply wp_putIDs b1 sl _ _ dq $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩
  ihave Hcs := Hcb $$ Hsl
  try wp_auto
  wp_apply wp_GetVotersOutgoing p dq _ $$ [$Hpb $Hcs] as %so ⟨Hso, Hcb⟩
  wp_apply wp_putIDs b2 so _ _ dq $$ [$Hb $Hcap $Hso] as %b3 ⟨Hb, Hcap, Hso⟩
  ihave Hcs := Hcb $$ Hso
  try wp_auto
  wp_apply wp_GetLearnersNext p dq _ $$ [$Hpb $Hcs] as %sn ⟨Hsn, Hcb⟩
  wp_apply wp_putIDs b3 sn _ _ dq $$ [$Hb $Hcap $Hsn] as %b4 ⟨Hb, Hcap, Hsn⟩
  ihave Hcs := Hcb $$ Hsn
  try wp_auto
  wp_apply wp_GetAutoLeave p dq _ $$ [$Hpb $Hcs] as Hcs
  have Hconf : ∀ (byte : w8), byte = autoB c.AutoLeave' →
      B ++ encIDs c.Voters' ++ encIDs c.Learners' ++ encIDs c.VotersOutgoing' ++
          encIDs c.LearnersNext' ++ [byte] = B ++ encConf c := by
    intro byte h
    subst h
    simp only [encConf, List.append_assoc]
  cases Hif : c.AutoLeave'
  all_goals (
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b5 ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe Hcap Hcs)
  · rw [Hconf (W8 0) (by simp [autoB, Hif])]; iexact Hb
  · rw [Hconf (W8 1) (by simp [autoB, Hif])]; iexact Hb

end proof

end kvraft
end EtcdGrove
end Perennial
