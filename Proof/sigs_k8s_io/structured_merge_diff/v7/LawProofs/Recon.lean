/-
**The root laws' declarative readings, proved** (`v7/Laws.lean`, "Pure laws"): `atomicNodes_mem`,
`reconcile_mem`, `reconcile_id` and `ensureNamed_mem`, over the membership facts of `FSet`.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Pure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

namespace LawProofs

/-! ## `FSet` membership -/

section fset
variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem FSet.mem_mk (l : List α) (x : α) : x ∈ FSet.ofList l ↔ x ∈ l := by
  change decide (x ∈ l) = true ↔ _
  simp

theorem FSet.mem_union' (a b : FSet α) (x : α) : x ∈ FSet.union a b ↔ x ∈ a ∨ x ∈ b := by
  induction a using Quotient.inductionOn with
  | h la =>
    induction b using Quotient.inductionOn with
    | h lb =>
      change x ∈ FSet.ofList (la ++ lb) ↔ x ∈ FSet.ofList la ∨ x ∈ FSet.ofList lb
      simp only [FSet.mem_mk, List.mem_append]

theorem FSet.mem_filter' (p : α → Bool) (a : FSet α) (x : α) :
    x ∈ FSet.filter p a ↔ x ∈ a ∧ p x = true := by
  induction a using Quotient.inductionOn with
  | h la =>
    change x ∈ FSet.ofList (la.filter p) ↔ x ∈ FSet.ofList la ∧ p x = true
    simp only [FSet.mem_mk, List.mem_filter]

theorem FSet.mem_bind' (f : α → List β) (a : FSet α) (y : β) :
    y ∈ FSet.bind f a ↔ ∃ x, x ∈ a ∧ y ∈ f x := by
  induction a using Quotient.inductionOn with
  | h la =>
    change y ∈ FSet.ofList (la.flatMap f) ↔ ∃ x, x ∈ FSet.ofList la ∧ y ∈ f x
    simp only [FSet.mem_mk, List.mem_flatMap]

theorem FSet.any_iff' (p : α → Bool) (a : FSet α) : a.any p = true ↔ ∃ x, x ∈ a ∧ p x = true := by
  induction a using Quotient.inductionOn with
  | h la =>
    change la.any p = true ↔ ∃ x, x ∈ FSet.ofList la ∧ p x = true
    simp only [List.any_eq_true, FSet.mem_mk]

theorem FSet.isEmpty_iff' (a : FSet α) : a.isEmpty = true ↔ ∀ x, x ∉ a := by
  unfold FSet.isEmpty
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, FSet.any_iff']
  simp

end fset

/-! ## Strict prefixes -/

theorem mem_strictPrefixes : ∀ (q p : Path), p ∈ strictPrefixes q ↔ ∃ r, r ≠ [] ∧ q = p ++ r
  | [], p => by simp [strictPrefixes]
  | e :: q, p => by
      simp only [strictPrefixes, List.mem_cons, List.mem_map]
      constructor
      · rintro (rfl | ⟨p', hp', rfl⟩)
        · exact ⟨e :: q, by simp, by simp⟩
        · obtain ⟨r, hr, rfl⟩ := (mem_strictPrefixes q p').1 hp'
          exact ⟨r, hr, by simp⟩
      · rintro ⟨r, hr, h⟩
        cases p with
        | nil => exact Or.inl rfl
        | cons x p' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr ⟨p', (mem_strictPrefixes _ p').2 ⟨r, hr, rfl⟩, rfl⟩

/-! ## The named fields along a path -/

/-- `namedAlong` on a non-empty path: what it adds at the head, and the rest. -/
theorem mem_namedAlong_cons (S : Schema) (ty : Option TypeRef) (acc : Path) (pe : PE) (r0 : Path)
    (q : Path) :
    q ∈ namedAlong S acc ty (pe :: r0) ↔
    (r0 ≠ [] ∧ q = acc ++ [pe] ∧ ∃ n fs e rel, pe = .field n ∧
      ty.bind (fun t => S.find t.name) = some (.map fs e rel) ∧ (lookupKV n fs).isSome = true) ∨
    q ∈ namedAlong S (acc ++ [pe]) (childType S ty pe) r0 := by
  simp only [namedAlong, List.mem_append]
  apply or_congr_left
  cases r0 with
  | nil => simp
  | cons x r =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    cases hb : ty.bind (fun t => S.find t.name) with
    | none => simp
    | some A =>
      cases A with
      | scalar _ => simp
      | list _ _ _ => simp
      | map fs e rel =>
        cases pe with
        | field n =>
          by_cases hl : (lookupKV n fs).isSome = true
          · simp [hl]
          · simp [hl]
        | key _ => simp
        | value _ => simp
        | index _ => simp

theorem mem_namedAlong (S : Schema) : ∀ (x acc : Path) (ty : Option TypeRef) (q : Path),
    q ∈ namedAlong S acc ty x ↔ ∃ p n r, x = p ++ .field n :: r ∧ r ≠ [] ∧
      q = acc ++ p ++ [.field n] ∧ ∃ fs e rel,
        (typeAlong S ty p).bind (fun t => S.find t.name) = some (.map fs e rel) ∧
        (lookupKV n fs).isSome = true
  | [], acc, ty, q => by simp [namedAlong]
  | pe :: r0, acc, ty, q => by
      rw [mem_namedAlong_cons, mem_namedAlong S r0 (acc ++ [pe])]
      constructor
      · rintro (⟨hr, rfl, n, fs, e, rel, rfl, hb, hl⟩ | ⟨p, n, r, rfl, hr, rfl, fs, e, rel, hb, hl⟩)
        · exact ⟨[], n, r0, by simp, hr, by simp, fs, e, rel, hb, hl⟩
        · exact ⟨pe :: p, n, r, by simp, hr, by simp, fs, e, rel, hb, hl⟩
      · rintro ⟨p, n, r, hx, hr, rfl, fs, e, rel, hb, hl⟩
        cases p with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact Or.inl ⟨hr, by simp, n, fs, e, rel, rfl, hb, hl⟩
        | cons y p' =>
          simp only [List.cons_append, List.cons.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact Or.inr ⟨p', n, r, rfl, hr, by simp, fs, e, rel, hb, hl⟩

end LawProofs

open LawProofs

theorem ensureNamed_mem_law_holds : ensureNamed_mem.law := by
  intro S t s q
  unfold ensureNamed
  rw [FSet.mem_union', FSet.mem_bind']
  simp only [mem_namedAlong, List.nil_append]
  constructor
  · rintro (h | ⟨x, hx, p, n, r, rfl, hr, rfl, fs, e, rel, hb, hl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, n, rfl, ⟨r, hr, by simpa using hx⟩, fs, e, rel, hb, hl⟩
  · rintro (h | ⟨p, n, rfl, ⟨r, hr, hx⟩, fs, e, rel, hb, hl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p ++ [.field n] ++ r, hx, p, n, r, by simp, hr, rfl, fs, e, rel, hb, hl⟩

theorem atomicNodes_mem_law_holds : atomicNodes_mem.law := by
  intro S t s p
  unfold atomicNodes
  rw [FSet.mem_filter', FSet.mem_bind']
  constructor
  · rintro ⟨⟨q, hq, hp⟩, hc⟩
    obtain ⟨r, hr, rfl⟩ := (mem_strictPrefixes q p).1 hp
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    refine ⟨hc.1, ⟨r, hr, hq⟩, ?_⟩
    revert hc
    cases reconAt S t p with
    | none => intro hc; simp at hc
    | some t' => intro hc; exact ⟨t', rfl, hc.2⟩
  · rintro ⟨hne, ⟨r, hr, hq⟩, t', ht', ha⟩
    refine ⟨⟨p ++ r, hq, (mem_strictPrefixes _ p).2 ⟨r, hr, rfl⟩⟩, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, ht']
    exact ⟨hne, ha⟩

theorem reconcile_mem_law_holds : reconcile_mem.law := by
  intro S t s q
  unfold reconcile
  simp only
  rw [FSet.mem_union', FSet.mem_filter', Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    FSet.any_iff']
  simp only [List.isPrefixOf_iff_prefix]

theorem reconcile_id_law_holds : reconcile_id.law := by
  intro S t s h
  unfold schemaConsistent at h
  rw [FSet.isEmpty_iff'] at h
  apply PathSet_ext_law_holds
  intro q
  rw [reconcile_mem_law_holds]
  constructor
  · rintro (⟨hq, -⟩ | hq)
    · exact hq
    · exact absurd hq (h q)
  · intro hq
    exact Or.inl ⟨hq, fun ⟨p, hp, _⟩ => h p hp⟩

end smd
end EtcdGrove
end Perennial
