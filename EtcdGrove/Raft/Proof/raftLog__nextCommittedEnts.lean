/- Port of election_proof/proof_raftLog__nextCommittedEnts.v (857d09190). -/
import EtcdGrove.Raft.Spec.raftLog__nextCommittedEnts
import EtcdGrove.Raft.Spec.raftLog__hasNextOrInProgressSnapshot
import EtcdGrove.Raft.Spec.raftLog__maxAppliableIndex
import EtcdGrove.Raft.Spec.raftLog__slice

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.nextCommittedEnts.wp_proof
    (wp_raftLog_hasNextOrInProgressSnapshot :
      raftLog.hasNextOrInProgressSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_maxAppliableIndex : raftLog.maxAppliableIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG)) :
    raftLog.nextCommittedEnts.spec (GF := GF) (hG := hG) := by
  intro l ls au
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases ownRaftLog_ready_wf l _ $$ Hlog with ⟨%Hrw, Hlog⟩
  icases ownRaftLog_committed l _ $$ Hlog with ⟨%Hcb, Hlog⟩
  icases ownRaftLog_nowrap l _ $$ Hlog with ⟨%Hnw, Hlog⟩
  simp only at Hrw Hnw Hcb
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  wp_auto
  cases Hpz : lv.applyingEntsPaused'
  case true =>
    -- paused: nothing
    wp_auto
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSliceCap_nil
    ipureintro; exact ⟨List.nil_prefix, fun _ => rfl⟩
  have Hroom : uint.Z lasz < uint.Z lamx := by subst lasz lamx; exact Hpaused Hpz
  ihave Hlog : ownRaftLog l ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩
    $$ [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
  clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset HnoConfChange Happlied
    Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused
  iclear HisStorage Husnap Hl_logger Hu_logger
  wp_auto
  wp_apply wp_raftLog_hasNextOrInProgressSnapshot l _ $$ [Hlog] as %b ⟨Hlog, %Hb⟩
  · iexact Hlog
  simp only at Hb
  cases snap with
  | some sid =>
    -- a pending snapshot: nothing
    rw [decide_eq_true (by simp)] at Hb
    subst b
    wp_auto
    iapply HΦ
    iframe Hlog
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSliceCap_nil
    ipureintro; exact ⟨List.nil_prefix, fun _ => rfl⟩
  | none =>
    rw [decide_eq_false (by simp)] at Hb
    subst b
    wp_auto
    -- `lo := l.applying + 1`
    icases (ownRaftLog_unfold l prev sents uents lcm lap none lip lapg lpend lasz lamx).1 $$ Hlog
      with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
    unfold ownRaftLogCore
    icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
    iNamed Hcore
    wp_auto
    rw [Hapg]
    ihave Hlog : ownRaftLog l ⟨prev, sents, uents, lcm, lap, none, lip, lapg, lpend, lasz, lamx⟩
      $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset HnoConfChange Happlied
      Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused
    iclear HisStorage Husnap Hl_logger Hu_logger
    wp_apply wp_raftLog_maxAppliableIndex l _ au $$ [Hlog] as %hi0 ⟨Hlog, %Hhi0⟩
    · iexact Hlog
    simp only at Hhi0
    have Hhi0' : uint.Z hi0 ≤ uint.Z lcm := by cases au <;> simp at Hhi0 <;> omega
    wp_if_destruct
    · -- nothing to apply
      iapply HΦ
      iframe Hlog
      isplitr; · iapply ownSlice_nil
      isplitr; · iapply ownSliceCap_nil
      ipureintro; exact ⟨List.nil_prefix, fun H => absurd rfl H⟩
    -- `maxSize := l.maxApplyingEntsSize - l.applyingEntsSize`: positive
    icases (ownRaftLog_unfold l prev sents uents lcm lap none lip lapg lpend lasz lamx).1 $$ Hlog
      with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
    unfold ownRaftLogCore
    icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
    iNamed Hcore
    wp_auto
    wp_if_destruct
    · exfalso; subst lasz lamx; word
    ihave Hlog : ownRaftLog l ⟨prev, sents, uents, lcm, lap, none, lip, lapg, lpend, lasz, lamx⟩
      $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    rw [Hasz, Hamx]
    clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset HnoConfChange Happlied
      Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused
    iclear HisStorage Husnap Hl_logger Hu_logger
    wp_apply wp_raftLog_slice l ⟨prev, sents, uents, lcm, lap, none, lip, lapg, lpend, lasz, lamx⟩
      (lapg + W64 1) (hi0 + W64 1) (lamx - lasz) ?_ $$ [Hlog] as %s %es ⟨Hlog, #Hs, %Hes, Hcap⟩
    · dsimp only
      obtain ⟨⟨Hcb1, Hcb2, Hcb3⟩, Hcb4⟩ := Hcb
      specialize Hcb4 rfl
      refine ⟨?_, ?_, ?_⟩ <;> word
    · iexact Hlog
    obtain ⟨-, Hlen, -, Hpre⟩ := Hes
    iapply HΦ
    iframe Hlog Hs Hcap
    ipureintro
    refine ⟨?_, fun H => absurd rfl H⟩
    unfold logCommittedEnts
    apply prefix_take_bound _ _ _ Hpre
    dsimp only
    obtain ⟨⟨Hcb1, Hcb2, Hcb3⟩, Hcb4⟩ := Hcb
    word

end proof

end EtcdGrove
end Perennial
