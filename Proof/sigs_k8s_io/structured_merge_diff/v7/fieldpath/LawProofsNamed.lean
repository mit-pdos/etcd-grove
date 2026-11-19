/-
**`fieldpath/NamedVocab.lean`'s laws, proved**: `ensureNamed` at a named type, and the children's
and members' parts of `ensureNamedOpt` (what `SetNodeMap`/`Set.EnsureNamedFieldsAreMembers`'
recursion rests on).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

namespace fpD

/-- The one-element part of `namedAlong` at a path element. -/
def namedTop (S : Schema) (ty : Option TypeRef) (pe : PE) : List Path :=
  match ty.bind (fun t => S.find t.name), pe with
  | some (.map fs _ _), .field n => if (lookupKV n fs).isSome then [[pe]] else []
  | _, _ => []

theorem namedAlong_acc (S : Schema) : ∀ (acc : Path) (ty : Option TypeRef) (p : Path),
    namedAlong S acc ty p = (namedAlong S [] ty p).map (acc ++ ·)
  | acc, ty, [] => by simp [namedAlong]
  | acc, ty, pe :: r => by
    simp only [namedAlong, List.map_append]
    rw [namedAlong_acc S (acc ++ [pe]) _ r, namedAlong_acc S ([] ++ [pe]) _ r]
    congr 1
    · split
      · simp
      · generalize ty.bind (fun t => S.find t.name) = o
        rcases o with _ | (_ | _ | _) <;> cases pe <;> simp <;> split <;> simp
    · simp [List.map_map, Function.comp_def, List.append_assoc]

theorem namedAlong_cons (S : Schema) (ty : Option TypeRef) (pe : PE) (r : Path) :
    namedAlong S [] ty (pe :: r) =
      (if r.isEmpty then [] else namedTop S ty pe) ++
        (namedAlong S [] (childType S ty pe) r).map (pe :: ·) := by
  simp only [namedAlong]
  rw [namedAlong_acc S ([] ++ [pe])]
  congr 1

theorem mem_namedTop (S : Schema) (ty : Option TypeRef) (pe : PE) (q : Path) :
    q ∈ namedTop S ty pe ↔ q = [pe] ∧ ∃ n fs el rel, pe = .field n ∧
      ty.bind (fun t => S.find t.name) = some (.map fs el rel) ∧ (lookupKV n fs).isSome := by
  unfold namedTop
  split
  · next fs el rel n h =>
    rw [h]
    split
    · next hs => simp only [List.mem_singleton]; exact ⟨fun h => ⟨h, n, fs, el, rel, rfl, rfl, hs⟩,
        fun h => h.1⟩
    · next hs =>
      simp only [List.not_mem_nil, false_iff, not_and]
      rintro - ⟨n', fs', el', rel', he, hf, hs'⟩
      cases he; cases hf; exact hs hs'
  · next hne =>
    simp only [List.not_mem_nil, false_iff, not_and]
    rintro - ⟨n', fs', el', rel', he, hf, hs'⟩
    subst he
    exact hne fs' el' rel' n' hf rfl

theorem namedAlong_ne (S : Schema) : ∀ (ty : Option TypeRef) (p q : Path),
    q ∈ namedAlong S [] ty p → q ≠ []
  | ty, [], q, h => by simp [namedAlong] at h
  | ty, pe :: r, q, h => by
    rw [namedAlong_cons] at h
    rcases List.mem_append.1 h with h | h
    · split at h
      · simp at h
      · exact ((mem_namedTop S ty pe q).1 h).1 ▸ List.cons_ne_nil _ _
    · obtain ⟨q', -, rfl⟩ := List.mem_map.1 h
      exact List.cons_ne_nil _ _

theorem mem_ensureNamedOpt (S : Schema) (ty : Option TypeRef) (s : PathSet) (q : Path) :
    q ∈ ensureNamedOpt S ty s ↔ q ∈ s ∨ ∃ p, p ∈ s ∧ q ∈ namedAlong S [] ty p := by
  unfold ensureNamedOpt
  rw [FSet.mem_union', FSet.mem_bind']

end fpD

open fpD in
theorem ensureNamed_opt_law_holds : ensureNamed_opt.law := fun _ _ _ => rfl

open fpD in
theorem ensureNamedOpt_under_law_holds : ensureNamedOpt_under.law := by
  intro S ty s e
  apply FSet.ext'
  intro q
  have hu : ∀ (S : PathSet) e q, q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S :=
    PathSet_mem_under_law_holds
  simp only [hu, mem_ensureNamedOpt]
  constructor
  · rintro ⟨hq, h | ⟨p, hp, hqp⟩⟩
    · exact Or.inl ⟨hq, h⟩
    · match p, hp, hqp with
      | pe :: r, hp, hqp =>
        rw [namedAlong_cons] at hqp
        rcases List.mem_append.1 hqp with h | h
        · split at h
          · simp at h
          · have := ((mem_namedTop S ty pe _).1 h).1
            simp at this; exact absurd this.2 hq
        · obtain ⟨q', hq', he⟩ := List.mem_map.1 h
          simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine Or.inr ⟨r, ⟨?_, hp⟩, hq'⟩
          intro hr; subst hr; simp [namedAlong] at hq'
  · rintro (⟨hq, h⟩ | ⟨r, ⟨hr, hp⟩, hqr⟩)
    · exact ⟨hq, Or.inl h⟩
    · refine ⟨namedAlong_ne S _ r q hqr, Or.inr ⟨e :: r, hp, ?_⟩⟩
      rw [namedAlong_cons]
      exact List.mem_append_right _ (List.mem_map.2 ⟨q, hqr, rfl⟩)

open fpD in
theorem ensureNamedOpt_tops_law_holds : ensureNamedOpt_tops.law := by
  intro S ty s e
  rw [PathSet_mem_tops_law_holds, mem_ensureNamedOpt, PathSet_mem_tops_law_holds,
    PathSet_mem_heads_law_holds]
  constructor
  · rintro (h | ⟨p, hp, hqp⟩)
    · exact Or.inl h
    · match p, hp, hqp with
      | pe :: r, hp, hqp =>
        rw [namedAlong_cons] at hqp
        rcases List.mem_append.1 hqp with h | h
        · split at h
          · simp at h
          · next hr =>
            obtain ⟨he, n, fs, el, rel, hpe, hf, hs⟩ := (mem_namedTop S ty pe _).1 h
            simp only [List.cons.injEq, and_true] at he
            subst he
            refine Or.inr ⟨⟨r, ?_, hp⟩, n, fs, el, rel, hpe, hf, hs⟩
            intro h0; subst h0; simp at hr
        · obtain ⟨q', hq', he⟩ := List.mem_map.1 h
          simp only [List.cons.injEq] at he
          exact absurd he.2 (namedAlong_ne S _ r q' hq')
  · rintro (h | ⟨⟨r, hr, hp⟩, n, fs, el, rel, hpe, hf, hs⟩)
    · exact Or.inl h
    · refine Or.inr ⟨e :: r, hp, ?_⟩
      rw [namedAlong_cons]
      apply List.mem_append_left
      have : r.isEmpty = false := by cases r <;> simp_all
      rw [this]
      exact (mem_namedTop S ty e [e]).2 ⟨rfl, n, fs, el, rel, hpe, hf, hs⟩

end smd
end EtcdGrove
end Perennial
