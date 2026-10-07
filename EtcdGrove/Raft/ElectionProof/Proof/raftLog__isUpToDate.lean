/-
Port of election_proof/proof_raftLog__isUpToDate.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__isUpToDate
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastEntryID

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

theorem raftLog.isUpToDate.wp_proof
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG)) :
    raftLog.isUpToDate.spec (GF := GF) (hG := hG) := by
  intro l e ls
  wp_start as Hlog
  wp_auto
  wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %our ⟨Hlog, %Hour⟩
  -- `their.term > our.term || (their.term == our.term && their.index >= our.index)`,
  -- which is `plogUpToDate` of `lastEntryID`'s result
  wp_if_destruct
  · iapply HΦ
    iframe
    ipureintro
    subst Hour
    simp only [plogUpToDate]
    simp [Hif]
  · by_cases Heq : e.term' = our.term'
    · simp only [Heq, decide_true]
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      subst Hour
      simp only [plogUpToDate]
      rw [decide_eq_decide]
      constructor
      · intro h; exact Or.inr ⟨Heq, h⟩
      · rintro (h | ⟨_, h⟩)
        · exact absurd h Hif
        · exact h
    · simp only [Heq, decide_false]
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      subst Hour
      simp only [plogUpToDate]
      symm
      rw [decide_eq_false_iff_not]
      rintro (h | ⟨h, _⟩)
      · exact Hif h
      · exact Heq h
