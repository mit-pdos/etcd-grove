/- Port of election_proof/proof_raftLog__nextCommittedEnts.v (857d09190). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__nextCommittedEnts
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressSnapshot
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__maxAppliableIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__slice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A prefix no longer than `n` is a prefix of the first `n`. -/
private theorem prefix_take_bound {A : Type _} (l1 l2 : List A) (n : Nat)
    (H : l1 <+: l2) (Hn : l1.length ≤ n) : l1 <+: l2.take n := by
  obtain ⟨k, rfl⟩ := H
  rw [List.take_append, List.take_of_length_le Hn]
  exact List.prefix_append _ _

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.nextCommittedEnts.wp_proof
    (wp_raftLog_hasNextOrInProgressSnapshot :
      raftLog.hasNextOrInProgressSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_maxAppliableIndex : raftLog.maxAppliableIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG)) :
    raftLog.nextCommittedEnts.spec (GF := GF) (hG := hG) := by
  intro l ls au
  wp_start as H
  iNamed H
  icases ownRaftLog_ready_wf l _ $$ Hlog with ⟨%Hrw, Hlog⟩
  icases ownRaftLog_committed l _ $$ Hlog with ⟨%Hcb, Hlog⟩
  icases ownRaftLog_nowrap l _ $$ Hlog with ⟨%Hnw, Hlog⟩
  iNamed Hlog
  wp_auto
  cases Hpz : lv.applyingEntsPaused'
  case true =>
    -- paused: nothing
    wp_auto
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    isplitr; · iapply entsPts_nil
    isplitr; · iapply ownSliceCap_nil
    ipureintro; exact ⟨List.nil_prefix, fun _ => rfl⟩
  have Hroom : uint.Z ls.apsize < uint.Z ls.apmax := Hpaused Hpz
  ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
  clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset Happlied
    Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused Hstor Hpend
  iclear HisStorage Husnap Hl_logger Hu_logger
  wp_auto
  wp_apply wp_raftLog_hasNextOrInProgressSnapshot l _ $$ [Hlog] as %b ⟨Hlog, %Hb⟩
  · iexact Hlog
  cases Hsn : ls.snap with
  | some sid =>
    -- a pending snapshot: nothing
    rw [Hsn, decide_eq_true (by simp)] at Hb
    subst b
    wp_auto
    iapply HΦ
    iframe Hlog
    isplitr; · iapply entsPts_nil
    isplitr; · iapply ownSliceCap_nil
    ipureintro; exact ⟨List.nil_prefix, fun _ => rfl⟩
  | none =>
    rw [Hsn, decide_eq_false (by simp)] at Hb
    subst b
    wp_auto
    -- `lo := l.applying + 1`
    iNamed Hlog
    wp_auto
    rw [Hapg]
    ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset Happlied
      Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused Hstor Hpend
    iclear HisStorage Husnap Hl_logger Hu_logger
    wp_apply wp_raftLog_maxAppliableIndex l _ au $$ [Hlog] as %hi0 ⟨Hlog, %Hhi0⟩
    · iexact Hlog
    have Hhi0' : uint.Z hi0 ≤ uint.Z ls.committed := by cases au <;> simp at Hhi0 <;> omega
    wp_if_destruct
    · -- nothing to apply
      iapply HΦ
      iframe Hlog
      isplitr; · iapply entsPts_nil
      isplitr; · iapply ownSliceCap_nil
      ipureintro; exact ⟨List.nil_prefix, fun H => absurd rfl H⟩
    -- `maxSize := l.maxApplyingEntsSize - l.applyingEntsSize`: positive
    iNamed Hlog
    wp_auto
    wp_if_destruct
    · exfalso; rw [Hasz, Hamx] at Hif; word
    ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    rw [Hasz, Hamx]
    clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset Happlied
      Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused Hstor Hpend
    iclear HisStorage Husnap Hl_logger Hu_logger
    -- (D19i part 1) from `applying + 1`, above the floor: no `ErrCompacted`
    icases ownRaftLog_fl _ _ $$ Hlog with ⟨%Hflb, Hlog⟩
    icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrwf, Hlog⟩
    wp_apply wp_raftLog_slice l ls (ls.applying + W64 1) (hi0 + W64 1) (ls.apmax - ls.apsize) ?_
      $$ [Hlog] as %s %es %err0 ⟨Hlog, Hsr⟩
    · obtain ⟨⟨Hcb1, Hcb2, Hcb3⟩, Hcb4⟩ := Hcb
      specialize Hcb4 Hsn
      refine ⟨?_, ?_, ?_⟩ <;> word
    · iexact Hlog
    icases Hsr with (⟨%Herr0, #Hs, %Hes, Hcap⟩ | ⟨%Hle0, -, -⟩)
    rotate_left
    · exfalso
      obtain ⟨⟨Hcb1, Hcb2, Hcb3⟩, Hcb4⟩ := Hcb
      specialize Hcb4 Hsn
      word
    subst Herr0
    wp_auto
    obtain ⟨-, Hlen, -, Hpre⟩ := Hes
    iapply HΦ
    iframe Hlog Hs Hcap
    ipureintro
    refine ⟨?_, fun H => absurd rfl H⟩
    unfold logCommittedEnts
    apply prefix_take_bound _ _ _ Hpre
    obtain ⟨⟨Hcb1, Hcb2, Hcb3⟩, Hcb4⟩ := Hcb
    word

end proof

end EtcdGrove
end Perennial
