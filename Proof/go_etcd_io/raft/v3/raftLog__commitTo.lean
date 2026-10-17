/- Port of election_proof/proof_raftLog__commitTo.v. -/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Proof.go_etcd_io.raft.v3.InvLogger

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

/-- `isLoggerVal`, opened (as in `Proof/raftLog__findConflict.lean`). -/
private theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

/-- etcd-io/raft#104: the PR's `commitTo` meets `specNew` (no premise; the out-of-range
case clamps to `lastIndex()` after a `Warningf`). -/
theorem raftLog.commitTo.wp_proof_new
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.commitTo.specNew (GF := GF) (hG := hG) := by
  intro l ls tocommit
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
    · -- the PR's new case: `Warningf`, then `committed = lastIndex()`
      wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li2 ⟨Hlog, %Hli2⟩
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      iNamed Hlog
      icases isLoggerVal_open _ $$ Hl_logger with ⟨%lg, %Hlg, #Hlgr⟩
      wp_auto
      ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
      · reseal_raftLog
      rw [Hlg]
      wp_apply Logger.wp_logf lg _ _ _ (by decide) $$ Hlgr
      wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li3 ⟨Hlog, %Hli3⟩
      iNamed Hlog
      wp_auto
      iapply HΦ $$ %li3
      isplitl
      · reseal_raftLog
        all_goals first
          | word
          | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ (by word) (Hssnap Hs))
      · ipureintro
        simp only [plogLastIndexZ, List.length_append]
        push_cast
        omega
    iNamed Hlog
    wp_auto
    iapply HΦ $$ %tocommit
    isplitl
    · reseal_raftLog
      all_goals first
        | word
        | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ (by word) (Hssnap Hs))
    · ipureintro
      simp only [plogLastIndexZ, List.length_append]
      push_cast
      omega
  · iapply HΦ $$ %ls.committed
    isplitl
    · iapply Hback $$ Hl
    · ipureintro
      have Hle : uint.Z tocommit ≤ uint.Z ls.committed := by rw [← Hcm]; word
      omega

/-- The PR's spec implies the old one: under the premise `tocommit ≤ lastIndex()` the
clamp is not taken and `committed` becomes `plogCommitTo committed tocommit`. So every
caller's proof, which uses `raftLog.commitTo.spec`, stands on the PR's code. -/
theorem raftLog.commitTo.spec_implies_old
    (H : raftLog.commitTo.specNew (GF := GF) (hG := hG)) :
    raftLog.commitTo.spec (GF := GF) (hG := hG) := by
  intro l ls tocommit Hle
  iintro %Φ ⟨#Hpkg, Hlog⟩ HΦ
  iapply H l ls tocommit $$ [$Hpkg $Hlog]
  inext
  iintro %c ⟨Hlog, %Hc⟩
  have Heq : c = plogCommitTo ls.committed tocommit := by
    unfold plogCommitTo
    split <;> (apply word.unsigned_inj; omega)
  rw [← Heq]
  iapply HΦ $$ Hlog

end proof

end EtcdGrove
end Perennial
