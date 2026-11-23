/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): pure laws of W6's proofs (`Garbage`,
`OldVotes`, `StaleLed`, `GC`'s loops, and the budget laws of `Ready` .. `Step`, `GC`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

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

theorem fold_length_le {α : Type} {f : α → EvalM Bool} :
    ∀ {xs acc r : List α}, xs.foldlM (fstep f) acc = .ok r → r.length ≤ acc.length + xs.length
  | [], acc, r, h => by simp at h; subst h; simp
  | x :: xs, acc, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨o, ho, h⟩ := bind_ok h
    have := fold_length_le h
    unfold fstep at ho
    obtain ⟨c, -, ho⟩ := bind_ok ho
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_ok, Except.ok.injEq] at ho <;>
      subst ho <;> simp at this ⊢ <;> omega

/-- `filterM`'s result is no longer than its list. -/
theorem filterM_length_le {α : Type} {xs ys : List α} {f : α → EvalM Bool} (h : filterM xs f = .ok ys) :
    ys.length ≤ xs.length := by
  have := fold_length_le (f := f) h; simpa using this

/-- **`OnDisk` keeps the fields it does not give** (`State.onDisk_keeps`, H4's; taken as a hypothesis
named `onDisk_keeps` by `Write`, `Flush`, `Ready` and their budget laws until it is proved). -/
abbrev OnDiskKeeps : Prop :=
  ∀ (s : State) (n : Nat) (q : QItem) (more : Bool) (ro : List Str) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet) (ns : State),
    s.onDisk n q more ro ld ll ch tl vi = .ok (some ns) →
    ns.cfg = s.cfg ∧ ns.queue = s.queue ∧ ns.pending = s.pending ∧ ns.i = s.i

/-- **`InMemory`'s per-server results have the state's per-server lengths** (`State.inMemory_lengths`;
taken as a hypothesis named `inMemory_lengths` by `Mem`, `Ready` until it is proved): `Mem` and
`Ready` store `r.role`, `r.config`, `r.confAt` in the successor, whose setters ask one entry per
server. -/
abbrev InMemoryLengths : Prop :=
  ∀ (s : State) (n : Nat) (ev : Event) (r : MemResult), s.inMemory n ev = .ok r →
    r.role.length = s.role.length ∧ r.config.length = s.config.length ∧ r.confAt.length = s.confAt.length

/-- A non-empty `l[n]!` is an element of `l`. -/
theorem getElem!_cons_mem {α : Type} {l : List (List α)} {n : Nat} {q : α} {rest : List α}
    (h : l[n]! = q :: rest) : n < l.length ∧ (q :: rest) ∈ l := by
  by_cases hn : n < l.length
  · refine ⟨hn, ?_⟩
    rw [← h, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn]; exact List.getElem_mem hn
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h; cases h

/-- `Write`'s and `Flush`'s `OnDisk` arguments (the state's own fields and its first queued item)
within the state's budget. -/
theorem onDisk_within_self {s : State} {b E n : Nat} {q : QItem} {rest : List QItem} (more : Bool)
    (hW : s.Within b E) (hq : s.queue[n]! = q :: rest) :
    OnDisk.Within b E (OnDisk.mk s n q more s.role s.leaders s.ledLog s.chain s.termLen s.viol) := by
  obtain ⟨-, hm⟩ := getElem!_cons_mem hq
  obtain ⟨-, hit⟩ := hW.queue _ hm
  obtain ⟨h1, h2, h3⟩ := hit q List.mem_cons_self
  exact ⟨hW, h1, h2, h3, hW.leaders_len, hW.leaders, hW.ledLog_len, hW.ledLog, hW.chain, hW.termLen,
    by have := hW.viol; simp only; omega⟩

theorem subslice_tail {α : Type} (q : α) (rest : List α) :
    subslice 1 (q :: rest).length (q :: rest) = rest := by simp [subslice]

/-- `s.Within b E` with its queue replaced by one within the budget. -/
theorem within_set_queue {s : State} {b E : Nat} (hW : s.Within b E) {Q : List (List QItem)}
    (hQ : ∀ q ∈ Q, q.length ≤ b ∧ ∀ it ∈ q, it.ev.Within b E ∧ it.m.length ≤ b ∧ ∀ m ∈ it.m, m.Within b E) :
    ({ s with queue := Q } : State).Within b E := by
  obtain ⟨hc, hi1, hi2, h1, h2, h3, h4, h5, h6, hlog, hch, hll1, hll2, hcf, hlc1, hlc2, hla, hel,
    htl, hm1, hm2, hv1, hv2, hl1, hl2, hu, hp, -, hr, hvi⟩ := hW
  exact ⟨hc, hi1, hi2, h1, h2, h3, h4, h5, h6, hlog, hch, hll1, hll2, hcf, hlc1, hlc2, hla, hel,
    htl, hm1, hm2, hv1, hv2, hl1, hl2, hu, hp, hQ, hr, hvi⟩

/-- The queue after `Write`/`Flush` drops node `n`'s first item, within the state's budget. -/
theorem queue_set_tail {s : State} {b E n : Nat} {q : QItem} {rest : List QItem} (hW : s.Within b E)
    (hq : s.queue[n]! = q :: rest) :
    ∀ x ∈ s.queue.set n rest, x.length ≤ b ∧ ∀ it ∈ x, it.ev.Within b E ∧ it.m.length ≤ b ∧ ∀ m ∈ it.m, m.Within b E := by
  obtain ⟨-, hm⟩ := getElem!_cons_mem hq
  intro x hx
  rcases mem_set_or hx with h | h
  · subst h
    obtain ⟨h1, h2⟩ := hW.queue _ hm
    exact ⟨by simp at h1; omega, fun it hit => h2 it (List.mem_cons_of_mem _ hit)⟩
  · exact hW.queue x h

end W6Laws

end AntCheck
end EtcdGrove
end Perennial
