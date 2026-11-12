/-
Port of election_proof/proof_raftLog__matchTerm.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__matchTerm
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__term

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.matchTerm.wp_proof
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG)) :
    raftLog.matchTerm.spec (GF := GF) (hG := hG) := by
  intro l ls id
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  wp_apply wp_raftLog_term l ls $$ [$Hlog] as %t %err ⟨Hlog, %Herr, %Ht, -, -⟩
  cases err with
  | ok eok =>
    -- `err != nil`: `id.index` is out of range, or (D19i part 1) compacted below the floor
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    refine ⟨fun h => (by cases h), fun Hge => ?_⟩
    symm
    apply decide_eq_false
    intro Hm
    have Hr := plogTermAt_some_range _ _ _ _ Hm
    unfold plogLastIndexZ at Hr
    simp only [List.length_append] at Hr
    have Hc := Herr.2 (by push_cast at Hr; omega) Hge
    cases Hc
  | nil =>
    have Ht := Ht rfl
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    have : PlogMatches ls.prev (ls.sents ++ ls.uents) id ↔ t = id.term' := by
      unfold PlogMatches; rw [Ht]; simp
    refine ⟨fun h => ?_, fun _ => (by simp only [this])⟩
    rw [this]
    simpa using h

end proof

end EtcdGrove
end Perennial
