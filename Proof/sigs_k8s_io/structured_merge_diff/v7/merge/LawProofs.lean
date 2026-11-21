/-
**`merge`'s laws, proved** (`merge/Laws.lean`): each `<name>.law` as `<name>_law_holds`. An
unproved law is a `sorry` here (the brief's rule), named in the report.
Prove phase (2026-11-20).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsStage
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsM1
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsMergeSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

/-- **`prune` is its three passes**: with at least one manager, `addBackOwnedMF` is the one pass over
the union, and the three `removeItems` are `prune`'s lines (by definition). -/
theorem prune_stages_law_holds : prune_stages.law := by
  intro S t merged mf L hne hmf
  cases mf with
  | nil => exact absurd rfl hmf
  | cons me mf =>
    simp only [prune, hne, ite_false, addBackOwnedMF, addBackOwned, addBackDangling]

/-- `MF.set` writes one manager's entry. -/
theorem MF.get_set_law_holds : MF.get_set.law := by
  intro mf k e m
  unfold MF.get MF.set
  rw [LawProofs.lookupKV_insertKV]
  by_cases h : m = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `MF.set` keeps the managers sorted. -/
theorem MF.set_sorted_law_holds : MF.set_sorted.law := by
  intro mf k e h
  unfold MF.set
  rw [LawProofs.keysSorted_iff_pairwise] at h ⊢
  exact LawProofs.insertKV_pairwise k e mf h

/-- Removing paths adds no node. -/
theorem removeItems_size_law_holds : removeItems_size.law :=
  fun S t x R => removeAt_size S t R x

/-- `prune`'s passes keep the object conforming (D10 (b)). -/
theorem prune_conforms_law_holds : prune_conforms.law := by
  sorry

end smd
end EtcdGrove
end Perennial
