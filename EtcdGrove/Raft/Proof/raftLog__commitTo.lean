/- Port of election_proof/proof_raftLog__commitTo.v. -/
import EtcdGrove.Raft.Spec.raftLog__commitTo
import EtcdGrove.Raft.Spec.raftLog__lastIndex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.commitTo.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.commitTo.spec (GF := GF) (hG := hG) := by
  intro l ls tocommit Hle
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  simp only [plogLastIndexZ, List.length_append] at Hle ⊢
  wp_start as H
  iNamed H
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv0, Hl, %Hcmap, Hback⟩
  obtain ⟨Hcm, Hap⟩ := Hcmap
  simp only at Hcm Hap
  wp_auto
  wp_if_destruct
  · have Hlt : uint.Z lcm < uint.Z tocommit := Hcm ▸ Hif
    clear Hif Hcm Hap
    ihave Hlog := Hback $$ Hl
    wp_apply wp_raftLog_lastIndex _ ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ $$ [$Hlog]
      as %li ⟨Hlog, %Hli⟩
    simp only at Hli
    wp_if_destruct
    · exfalso; word
    icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
      with ⟨%lv, Hl, %Hcm', %Hap', %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
    iunfold ownRaftLogCore at Hcore
    icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
    iNamed Hcore
    wp_auto
    iapply HΦ
    rw [plogCommitTo, ite_eq_left Hlt]
    reseal_raftLog
    all_goals
      simp only
      subst Hcm' Hap'
      first
        | omega
        | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ (by omega) (Hssnap Hs))
  · iapply HΦ
    rw [plogCommitTo, ite_eq_right (by rw [← Hcm]; exact Hif)]
    iapply Hback $$ Hl

end proof

end EtcdGrove
end Perennial
