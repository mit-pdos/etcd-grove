/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/core/Helpers.lean (241f27e).
-/
/-
Helper lemmas of agent CORE shared by the raft proofs (not part of the frozen interface):
namespace disjointness of the protocol invariant (`gprotN`) and raft's namespaces.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

/-- The protocol invariant's namespace is outside every namespace of raft (`raftN.@x`). -/
theorem gprotN_diff_raft (x : String) : (↑gprotN : CoPset) ⊆ ⊤ \ ↑(raftN.@x) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' =>
    ndot_ne_disjoint nroot (show ("gprot" : String) ≠ "raft" by decide) p
      ⟨hp, nclose_subseteq raftN x p h'⟩⟩

theorem gprotN_diff_termN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑termN := gprotN_diff_raft "term"
theorem gprotN_diff_cidxN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑cidxN := gprotN_diff_raft "cidx"
theorem gprotN_diff_logN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑logN := gprotN_diff_raft "log"

end github_com.hashicorp.raft

end Perennial
