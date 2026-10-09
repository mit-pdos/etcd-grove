/- Port of election_proof/proof_raftLog__hasNextCommittedEnts.v (857d09190). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__hasNextCommittedEnts
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__maxAppliableIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.hasNextCommittedEnts.wp_proof
    (wp_raftLog_hasNextOrInProgressSnapshot :
      raftLog.hasNextOrInProgressSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_maxAppliableIndex : raftLog.maxAppliableIndex.spec (GF := GF) (hG := hG)) :
    raftLog.hasNextCommittedEnts.spec (GF := GF) (hG := hG) := by
  intro l ls au
  wp_start as H
  iNamed H
  icases ownRaftLog_ready_wf l _ $$ Hlog with ⟨%Hrw, Hlog⟩
  icases ownRaftLog_nowrap l _ $$ Hlog with ⟨%Hnw, Hlog⟩
  icases ownRaftLog_committed l _ $$ Hlog with ⟨%Hcb, Hlog⟩
  iNamed Hlog
  wp_auto
  cases Hpz : lv.applyingEntsPaused'
  case true =>
    wp_auto
    iapply HΦ
    isplitl
    · reseal_raftLog
    ipureintro; intro Hc; cases Hc
  ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
  clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset HnoConfChange Happlied
    Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused
  iclear HisStorage Husnap Hl_logger Hu_logger
  wp_auto
  wp_apply wp_raftLog_hasNextOrInProgressSnapshot l _ $$ [Hlog] as %b ⟨Hlog, %Hb⟩
  · iexact Hlog
  cases Hsn : ls.snap with
  | some sid =>
    rw [Hsn, decide_eq_true (by simp)] at Hb
    subst b
    wp_auto
    iapply HΦ
    iframe Hlog
    ipureintro; intro Hc; cases Hc
  | none =>
    rw [Hsn, decide_eq_false (by simp)] at Hb
    subst b
    wp_auto
    iNamed Hlog
    wp_auto
    rw [Hapg]
    ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    clear Hcm Hap Hapg Hip Hasz Hamx Hidx Hnowrap Hstore Hoffset HnoConfChange Happlied
      Hpapplied Hcommitted Hssnap Hipb Hpersist Happlying Hpaused
    iclear HisStorage Husnap Hl_logger Hu_logger
    wp_apply wp_raftLog_maxAppliableIndex l _ au $$ [Hlog] as %hi0 ⟨Hlog, %Hhi0⟩
    · iexact Hlog
    have Hhi0' : uint.Z hi0 ≤ uint.Z ls.committed := by cases au <;> simp at Hhi0 <;> omega
    iapply HΦ
    iframe Hlog
    ipureintro
    intro Hlt
    simp only [decide_eq_true_eq] at Hlt
    refine ⟨rfl, ?_⟩
    word

end proof

end EtcdGrove
end Perennial
