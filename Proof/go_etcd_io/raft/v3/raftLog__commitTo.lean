/- Port of election_proof/proof_raftLog__commitTo.v. -/
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
  intro l ls tocommit Hle
  simp only [plogLastIndexZ, List.length_append] at Hle
  wp_start as H
  iNamed H
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv0, Hl, %Hcmap, Hback⟩
  obtain ⟨Hcm, Hap⟩ := Hcmap
  wp_auto
  wp_if_destruct
  · have Hlt : uint.Z ls.committed < uint.Z tocommit := Hcm ▸ Hif
    clear Hif Hcm Hap
    ihave Hlog := Hback $$ Hl
    wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    wp_if_destruct
    · exfalso; word
    iNamed Hlog
    wp_auto
    iapply HΦ
    rw [plogCommitTo, ite_eq_left Hlt]
    reseal_raftLog
    all_goals first
      | word
      | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ (by word) (Hssnap Hs))
  · iapply HΦ
    rw [plogCommitTo, ite_eq_right (by rw [← Hcm]; exact Hif)]
    iapply Hback $$ Hl

end proof

end EtcdGrove
end Perennial
