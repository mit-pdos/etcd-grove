/-
Port of election_proof/proof_raftLog__findConflictByTerm.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__findConflictByTerm
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

theorem raftLog.findConflictByTerm.wp_proof
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG)) :
    raftLog.findConflictByTerm.spec (GF := GF) (hG := hG) := by
  intro l ls index term
  wp_start as H
  iNamed H
  wp_auto
  -- (D21 M3) the walk stops at or above `1` once the log's term at `1` (if it has one) is at
  -- most `term`
  ihave IH : iprop(∃ (idx : w64),
      "index" ∷ index_ptr ↦ idx ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "%Hidx" ∷ ⌜uint.Z idx ≤ uint.Z index ∧
        (1 ≤ uint.Z index →
          (∀ t0, plogTermAt ls.prev (ls.sents ++ ls.uents) (W64 1) = some t0 →
            uint.Z t0 ≤ uint.Z term) → 1 ≤ uint.Z idx)⌝) $$ [index Hlog]
  · iexists index
    iframe
    ipureintro
    exact ⟨Int.le_refl _, fun h _ => h⟩
  wp_for IH
  wp_if_destruct
  · wp_apply wp_raftLog_term $$ [$Hlog] as %t %err ⟨Hlog, %Herr, %Ht, -⟩
    cases err with
    | ok eok =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact ⟨Hidx.1, fun _ _ => by word⟩
    | nil =>
      wp_auto
      wp_if_destruct
      · wp_for_post
        iapply HΦ
        iframe
        ipureintro
        exact ⟨Hidx.1, fun _ _ => by word⟩
      · wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, fun h1 hC => ?_⟩
        have H1 := Hidx.2 h1 hC
        by_cases hi : uint.Z idx = 1
        · exfalso
          have hw : idx = W64 1 := by word
          have := hC t (by rw [← hw]; exact Ht rfl)
          word
        · word
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨by word, fun h1 hC => by have := Hidx.2 h1 hC; word⟩

end proof

end EtcdGrove
end Perennial
