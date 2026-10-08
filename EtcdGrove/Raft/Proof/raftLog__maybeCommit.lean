/-
Port of election_proof/proof_raftLog__maybeCommit.v.
-/
import EtcdGrove.Raft.Spec.raftLog__maybeCommit
import EtcdGrove.Raft.Spec.raftLog__matchTerm
import EtcdGrove.Raft.Spec.raftLog__commitTo

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

theorem raftLog.maybeCommit.wp_proof
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG)) :
    raftLog.maybeCommit.spec (GF := GF) (hG := hG) := by
  intro l ls aid
  wp_start as H
  iNamed H
  icases ownRaftLog_struct l ls $$ Hlog with ⟨%lv, Hl, %Hlv, Hback⟩
  obtain ⟨Hcm, Hap⟩ := Hlv
  wp_auto
  by_cases Ht0 : aid.term' = W64 0
  · -- `at.term == 0`: no
    rw [decide_eq_true Ht0]
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl
    · iapply Hback $$ Hl
    ipureintro
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨Hne, -, -⟩
    exact Hne Ht0
  rw [decide_eq_false Ht0]
  wp_auto
  rw [Hcm]
  by_cases Hlt : uint.Z ls.committed < uint.Z aid.index'
  case neg =>
    -- `at.index <= committed`: no
    rw [decide_eq_false Hlt]
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl
    · iapply Hback $$ Hl
    ipureintro
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨-, Hlt', -⟩
    exact Hlt Hlt'
  rw [decide_eq_true Hlt]
  wp_auto
  ihave Hlog := Hback $$ Hl
  wp_apply wp_raftLog_matchTerm _ ls _ $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  cases b with
  | true =>
    -- `matchTerm`: commit. `commitTo`'s premise from the match.
    have Hm : PlogMatches ls.prev (ls.sents ++ ls.uents) aid := of_decide_eq_true Hb.symm
    have Hrange := plogTermAt_some_range _ _ _ _ Hm
    wp_auto
    wp_apply wp_raftLog_commitTo _ ls aid.index' Hrange.2 $$ [$Hlog] as Hlog
    iapply HΦ
    rw [show plogCommitTo ls.committed aid.index' = aid.index' by simp [plogCommitTo, Hlt]]
    iframe
    ipureintro
    symm
    exact decide_eq_true ⟨Ht0, Hlt, Hm⟩
  | false =>
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    ipureintro
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨-, -, Hm⟩
    exact absurd (decide_eq_true Hm) (by rw [← Hb]; simp)

end proof

end EtcdGrove
end Perennial
