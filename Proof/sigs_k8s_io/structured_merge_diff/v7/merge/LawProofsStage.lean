/-
**Helpers of `merge`'s stage proofs** (`Updater.prune`, `addBackOwnedItems(ForVersion)`,
`addBackDanglingItems`, ...): the size premises of the callees (`EnsureNamedFieldsAreMembers`'
`CardLt (2 ^ 63)`) from the API's `smdSizeMax` bounds, and the imports of the laws they use.
Prove phase (2026-11-20).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsNamed
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

/-- A value's field set is small enough for `EnsureNamedFieldsAreMembers`. -/
theorem fieldSet_cardLt (S : Schema) (t : TypeRef) (x : UVal) (h : x.size < smdSizeMax) :
    (fieldSet S t x).CardLt (2 ^ 63) := by
  have := fieldSet_card_law_holds S t [] x h
  unfold FSet.CardLt at *
  unfold fieldSet
  omega

/-- A set of a `VersionedSet` (no empty path) with few trie nodes is small enough for
`EnsureNamedFieldsAreMembers`. -/
theorem nodes_cardLt (s : PathSet) (hne : [] ∉ s) (h : s.nodes.card < smdSizeMax) :
    s.CardLt (2 ^ 63) := by
  have := PathSet_card_nodes_of_ne s hne
  unfold FSet.CardLt
  unfold smdSizeMax at h
  omega

/-- Dropping one manager's entries. -/
theorem MF_get_filter_ne (mf : MF) (k m : GoString) :
    MF.get (mf.filter (fun me : GoString × VSet => me.1 != k)) m = if m = k then none else mf.get m := by
  induction mf with
  | nil => simp [MF.get, lookupKV]
  | cons me rest ih =>
    obtain ⟨k1, e1⟩ := me
    unfold MF.get at ih ⊢
    by_cases hk : k1 = k
    · subst hk
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false, ih, lookupKV]
      by_cases hm : m = k1
      · simp [hm]
      · simp [hm, Ne.symm hm]
    · have : (k1 != k) = true := by simpa using hk
      simp only [List.filter_cons, this, ite_true, lookupKV, ih]
      by_cases hm : m = k
      · subst hm; simp [hk]
      · simp [hm]

/-- Dropping entries keeps the managers sorted. -/
theorem MF_filter_sorted (mf : MF) (p : GoString × VSet → Bool) (h : keysSorted mf = true) :
    keysSorted (mf.filter p) = true := by
  rw [LawProofs.keysSorted_iff_pairwise] at h ⊢
  exact h.filter p

end smd
end EtcdGrove
end Perennial
