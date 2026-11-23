/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RepsOk.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Discharging `swift.RepsOk` (recoveredSync's premises on its reports, Proof/swift/RecSync.lean):
the parts a majority gives (`isMajority`), the phases' bound from the reports' truthfulness
(`entryOk`). The rest (no `SCAN`, the pre-accepted dependencies without duplicates, the
reports' total size) is listed in notes/prove-swift.md §11 (model requests).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace swift

theorem majority_facts {N : Nat} {reps : List (Nat × sp.Report)}
    (h : sp.isMajority N (reps.map Prod.fst)) (hN : 1 ≤ N) :
    reps ≠ [] ∧ (reps.map Prod.fst).Nodup ∧ reps.length ≤ N ∧ ∀ a ∈ reps, a.1 < N := by
  obtain ⟨hnd, hlt, hlen⟩ := h
  refine ⟨?_, hnd, ?_, fun a ha => hlt a.1 (List.mem_map_of_mem ha)⟩
  · intro h0; subst h0; simp at hlen
  · have hsub : (reps.map Prod.fst) ⊆ List.range N := fun x hx => List.mem_range.mpr (hlt x hx)
    have := (List.subperm_of_subset hnd hsub).length_le
    simpa using this

/-- `RepsOk` from a majority's reports and the facts the model does not give yet. -/
theorem repsOk_of {N : Nat} {reps : List (Nat × sp.Report)}
    (h : sp.isMajority N (reps.map Prod.fst)) (hN : 1 ≤ N ∧ N ≤ 7)
    (hcb : ∀ a ∈ reps, a.2.cbal < 2 ^ 31)
    (hents : ∀ a ∈ reps, ∀ e ∈ a.2.entries, e.phase.toNat ≤ 3 ∧ e.cmd.op ≠ swift.opSCAN ∧
      (e.phase.toNat = 1 → e.dep.Nodup))
    (hsize : (reps.flatMap (·.2.entries)).length < 2 ^ 31)
    (hpg : ∀ a ∈ reps, ∀ e ∈ a.2.entries, e.cmd.isPut ∨ e.cmd.isGet) : swift.RepsOk N reps := by
  obtain ⟨hne, hnd, hlen, hlt⟩ := majority_facts h hN.1
  exact ⟨hne, hnd, hlen, hN, fun a ha => ⟨hlt a ha, hcb a ha⟩, hents, hsize, hpg⟩

end swift

end Perennial.github_com.imdea_software.swiftpaxos
