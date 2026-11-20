/-
**The facts behind `Set`/`SetNodeMap.EnsureNamedFieldsAreMembers`' bodies**: the children's part
of `ensureNamedOpt` (only deep paths matter), a set's members and node counts bounded by its
cardinality, and the child type Go computes.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsNamed
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpE

theorem mem_under' (S : PathSet) (e : PE) (q : Path) : q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_under_law_holds S e q
theorem mem_deep' (S : PathSet) (q : Path) : q ∈ S.deep ↔ q ∈ S ∧ 2 ≤ q.length :=
  PathSet_mem_deep_law_holds S q
theorem mem_tops' (S : PathSet) (e : PE) : e ∈ S.tops ↔ [e] ∈ S := PathSet_mem_tops_law_holds S e
theorem mem_heads' (S : PathSet) (e : PE) : e ∈ S.heads ↔ ∃ q, q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_heads_law_holds S e

theorem ens_under (S : Schema) (ty : Option TypeRef) (s : PathSet) (e : PE) :
    (ensureNamedOpt S ty s).under e = ensureNamedOpt S (childType S ty e) (s.under e) :=
  ensureNamedOpt_under_law_holds S ty s e

/-- A path of two or more elements, by its head and rest. -/
theorem mem_deep_cons (A : PathSet) (e : PE) (r : Path) :
    (e :: r) ∈ A.deep ↔ r ∈ A.under e := by
  rw [mem_deep', mem_under']
  constructor
  · rintro ⟨h, hl⟩; refine ⟨?_, h⟩; rintro rfl; simp at hl
  · rintro ⟨hr, h⟩; refine ⟨h, ?_⟩
    match r, hr with
    | _ :: _, _ => simp

theorem under_deep (A : PathSet) (e : PE) : A.deep.under e = A.under e := by
  apply FSet.ext'; intro q
  rw [mem_under', mem_under', mem_deep']
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨h1, h2, ?_⟩
    match q, h1 with
    | _ :: _, _ => simp

theorem deep_ext {A B : PathSet} (h : ∀ e, A.under e = B.under e) : A.deep = B.deep := by
  apply FSet.ext'; intro q
  match q with
  | [] => rw [mem_deep', mem_deep']; simp
  | e :: r => rw [mem_deep_cons, mem_deep_cons, h e]

/-- **Only the deep paths reach the children's part.** -/
theorem ens_deep (S : Schema) (ty : Option TypeRef) (s : PathSet) :
    (ensureNamedOpt S ty s).deep = (ensureNamedOpt S ty s.deep).deep := by
  apply deep_ext; intro e
  rw [ens_under, ens_under, under_deep]

theorem ens_nil (S : Schema) (ty : Option TypeRef) (s : PathSet) (h : [] ∉ s) :
    [] ∉ ensureNamedOpt S ty s := by
  rw [fpD.mem_ensureNamedOpt]
  rintro (h' | ⟨p, -, hq⟩)
  · exact h h'
  · exact fpD.namedAlong_ne S ty p [] hq rfl

theorem ens_sub (S : Schema) (ty : Option TypeRef) (s : PathSet) (q : Path) (h : q ∈ s) :
    q ∈ ensureNamedOpt S ty s := (fpD.mem_ensureNamedOpt S ty s q).2 (Or.inl h)

end fpE

end smd
end EtcdGrove
end Perennial
