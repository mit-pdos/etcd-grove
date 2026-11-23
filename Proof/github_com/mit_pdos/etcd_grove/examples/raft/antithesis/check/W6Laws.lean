/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): pure laws of W6's proofs (`Garbage`,
`OldVotes`, `StaleLed`, `GC`'s loops, and the budget laws of `Ready` .. `Step`, `GC`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

namespace W6Laws

set_option linter.unusedSimpArgs false

/-- `filterM`'s step. -/
def fstep {α : Type} (f : α → EvalM Bool) (out : List α) (x : α) : EvalM (List α) :=
  do if (← f x) then pure (out ++ [x]) else pure out

theorem filterM_eq {α : Type} (xs : List α) (f : α → EvalM Bool) :
    filterM xs f = xs.foldlM (fstep f) [] := rfl

/-- One iteration of `filterM`'s loop, at position `k`. -/
theorem fold_step {α : Type} {xs : List α} {f : α → EvalM Bool} {k : Nat} {acc r : List α}
    (hk : k < xs.length) (H : (xs.drop k).foldlM (fstep f) acc = .ok r) :
    ∃ c, f xs[k] = .ok c ∧ (xs.drop (k + 1)).foldlM (fstep f) (if c then acc ++ [xs[k]] else acc) = .ok r := by
  rw [List.drop_eq_getElem_cons hk, List.foldlM_cons] at H
  obtain ⟨o, ho, H⟩ := bind_ok H
  unfold fstep at ho
  obtain ⟨c, hc, ho⟩ := bind_ok ho
  refine ⟨c, hc, ?_⟩
  cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_ok, Except.ok.injEq] at ho <;> subst ho <;> simpa using H

/-- The end of `filterM`'s loop. -/
theorem fold_end {α : Type} {xs : List α} {g : List α → α → EvalM (List α)} {acc r : List α}
    (H : (xs.drop xs.length).foldlM g acc = .ok r) : acc = r := by
  rw [List.drop_length] at H; simpa using H

/-- A relation between two lists survives appending one related pair. -/
theorem forall₂_append_one {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B} {a : A} {b : B}
    (h : List.Forall₂ R l1 l2) (hab : R a b) : List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) :=
by
  induction h with
  | nil => exact .cons hab .nil
  | cons h _ ih => exact .cons h ih

/-- `filter` keeps `Forall₂` when the predicates agree on related elements. -/
theorem forall₂_filter {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B} {p : A → Bool} {q : B → Bool}
    (h : List.Forall₂ R l1 l2) (hpq : ∀ a b, R a b → p a = q b) :
    List.Forall₂ R (l1.filter p) (l2.filter q) := by
  induction h with
  | nil => exact .nil
  | @cons a b l1 l2 hab _ ih =>
    rw [List.filter_cons, List.filter_cons, hpq a b hab]
    split
    · exact .cons hab ih
    · exact ih

end W6Laws

end AntCheck
end EtcdGrove
end Perennial
