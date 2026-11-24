/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): pure laws of the small actions' loops
(`ReadGiven`'s filter and search over a node's reads).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem filterM_pure {α : Type} (xs : List α) (p : α → Bool) :
    filterM xs (fun x => pure (p x)) = .ok (xs.filter p) := by
  unfold filterM
  suffices h : ∀ acc : List α, xs.foldlM (fun out x => do if (← (pure (p x) : EvalM Bool)) then pure (out ++ [x]) else pure out) acc
      = .ok (acc ++ xs.filter p) by simpa using h []
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    rw [List.foldlM_cons]
    have e : ((do if (← (pure (p x) : EvalM Bool)) then pure (acc ++ [x]) else pure acc) : EvalM (List α)) =
        .ok (if p x then acc ++ [x] else acc) := by cases p x <;> rfl
    rw [e, ok_bind, ih]
    cases hx : p x <;> simp [List.filter_cons, hx]

/-- `filterM` errs on a list whose elements all err. -/
theorem filterM_error {α : Type} (x : α) (xs : List α) (f : α → EvalM Bool) (e : String)
    (hf : ∀ y, f y = .error e) : ∃ e', filterM (x :: xs) f = .error e' := by
  unfold filterM
  rw [List.foldlM_cons]
  simp [hf]

theorem anyM_cons {α : Type} (x : α) (xs : List α) (f : α → EvalM Bool) :
    anyM (x :: xs) f = (do if (← f x) then pure true else anyM xs f) := rfl

theorem logWithin_chgSum {b E : Nat} {l : List Entry} (h : logWithin b E l) : (l.map Entry.chgSize).sum ≤ b * E := by
  obtain ⟨hl, he⟩ := h
  have : (l.map Entry.chgSize).sum ≤ l.length * E := by
    clear hl
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := (he x List.mem_cons_self).2
      have h2 := ih (fun e he' => he e (List.mem_cons_of_mem _ he'))
      rw [Nat.succ_mul]; omega
  exact Nat.le_trans this (Nat.mul_le_mul_right _ hl)

/-- `ConfOf(chain, k, InitConf)`'s premise, from the budget. -/
theorem confOf_bounded_init {s : State} {b E w : Nat} (hW : s.Within b E)
    (hE : ((s.cfg.initVoters.length + (b + w + 1) * E : Nat) : Int) < 2 ^ 61) :
    ConfOf.Bounded s.chain s.initConf := by
  unfold ConfOf.Bounded State.initConf Config.initConf
  have h := logWithin_chgSum hW.2.2.2.2.2.2.2.2.2.2.1
  have : b * E ≤ (b + w + 1) * E := Nat.mul_le_mul_right _ (by omega)
  simp only [List.length_nil, Nat.add_zero]
  omega

theorem atE_mem {l : List Entry} {k : Int} {e : Entry} (h : atE l k = .ok e) : e ∈ l := by
  unfold atE at h
  split at h
  · cases h
  · cases h
    rename_i hk
    have : (k - 1).toNat < l.length := by omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact List.getElem_mem this

/-- `Legal`'s and `NextConf`'s premise: a configuration within budget changed by an entry of a log
within budget. -/
theorem legal_bounds {V b E w : Nat} {c : Conf} {e : Entry} (hc : confWithin V b E c) (he : e.chgSize ≤ E)
    (hE : ((V + (b + w + 1) * E : Nat) : Int) < 2 ^ 61) :
    (c.cin.length : Int) + e.value.add.length < 2 ^ 61 ∧ (e.value.remove.length : Int) < 2 ^ 61 := by
  unfold confWithin at hc; unfold Entry.chgSize at he
  have h1 : b * E + E ≤ (b + w + 1) * E := by
    rw [show (b + w + 1) * E = b * E + w * E + E by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]]; omega
  constructor <;> omega

section rel
variable [GooseExts] [go_gctx : GoGlobalContext]

theorem readRel_filter {gs : List G.ReadRec} {rs : List ReadRec} (c : Str) (h : List.Forall₂ readRel gs rs) :
    List.Forall₂ readRel (gs.filter (fun g => g.Ctx' != c)) (rs.filter (fun r => r.ctx != c)) := by
  induction h with
  | nil => exact .nil
  | @cons a b l1 l2 hab _ ih =>
    have : a.Ctx' = b.ctx := hab.1
    by_cases hc : b.ctx = c
    · simp [this, hc, ih]
    · simp [this, hc]; exact ⟨hab, ih⟩

end rel

end AntCheck
end EtcdGrove
end Perennial
