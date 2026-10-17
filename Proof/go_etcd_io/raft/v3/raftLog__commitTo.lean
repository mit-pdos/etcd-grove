/- Port of election_proof/proof_raftLog__commitTo.v; raft#139's `commitTo(leaderTerm, tocommit)`
(`notes/pr-verify/raft-139.md`). -/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex

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

theorem raftLog.commitTo.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.commitTo.spec (GF := GF) (hG := hG) := by
  intro l ls lt tocommit
  wp_start as H
  iNamed H
  icases ownRaftLog_struct_lt _ _ $$ Hlog with ⟨%lv0, Hl, %Hcl, Hback⟩
  obtain ⟨Hcm0, Hlt0⟩ := Hcl
  wp_auto
  by_cases Heq : lt = ls.leaderTerm
  case neg =>
    -- another leader term: nothing changes
    rw [decide_eq_false (show ¬ lt = lv0.leaderTerm' by rw [Hlt0]; exact Heq)]
    wp_auto
    iapply HΦ
    rw [logCommitTo_other _ _ _ Heq]
    iapply Hback $$ Hl
  rw [decide_eq_true (show lt = lv0.leaderTerm' by rw [Hlt0]; exact Heq)]
  wp_auto
  ihave Hlog := Hback $$ Hl
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw, Hlog⟩
  wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  have Hlast : logLast ls = li := by
    apply uint_Z_inj.1
    rw [LogNoWrap.logLast_Z Hnw, Hli]
  wp_apply wp_go_min_u64
  have Hc : logCommitTo ls lt tocommit = plogCommitTo ls.committed (w64Min tocommit li) := by
    unfold logCommitTo; rw [if_pos Heq, Hlast]
  rw [Hc]
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcmb, Hlog⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrw, Hlog⟩
  have Hmin := w64Min_spec tocommit li
  iNamed Hlog
  wp_auto
  wp_if_destruct
  · have Hlt : uint.Z ls.committed < uint.Z (w64Min tocommit li) := by rw [← Hcm]; exact Hif
    iapply HΦ
    rw [plogCommitTo, if_pos Hlt]
    reseal_raftLog
    all_goals first
      | word
      | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ (by word) (Hssnap Hs))
  · iapply HΦ
    rw [plogCommitTo, ite_eq_right (by rw [← Hcm]; exact Hif)]
    reseal_raftLog

end proof

end EtcdGrove
end Perennial
