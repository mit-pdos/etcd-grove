/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): pure laws of `Boot` and `Send` for their
budget laws (`Within/Boot.lean`, `Within/Send.lean`) and proofs: `ConfOf`'s and `LastConf`'s
results from a log within budget, `SubSeq`'s elements and length, and the budget of a state with
`msgs`, `confirmed` or `undo` updated as `Send` updates them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-- `SubSeq(l, m, k)`'s elements are `l`'s. -/
theorem bootSend_subSeq_mem {l r : List Entry} {a c : Int} (h : subSeq l a c = .ok r) {e : Entry}
    (he : e ∈ r) : e ∈ l := by
  unfold subSeq at h
  split at h
  · cases h; simp at he
  split at h
  · cases h
  cases h
  exact List.mem_of_mem_drop (List.mem_of_mem_take he)

/-- `SubSeq(l, 1, k)` has `k` entries when `k ≥ 1`, none otherwise. -/
theorem bootSend_subSeq_one_length {l r : List Entry} {k : Int} (h : subSeq l 1 k = .ok r) :
    (r.length : Int) ≤ max k 0 := by
  unfold subSeq at h
  split at h
  · cases h; simp; omega
  split at h
  · cases h
  cases h
  simp only [List.length_take, List.length_drop]; omega

/-- `ConfOf(l, a)` from `c0`: each of the `a` steps adds at most `E` names to the larger set. -/
theorem bootSend_confOf_length {l : List Entry} {a : Int} {c0 c : Conf} {E K : Nat}
    (hl : ∀ e ∈ l, e.chgSize ≤ E) (h0 : c0.cin.length ≤ K ∧ c0.cout.length ≤ K)
    (h : confOf l a c0 = .ok c) :
    c.cin.length ≤ K + a.toNat * E ∧ c.cout.length ≤ K + a.toNat * E := by
  unfold confOf at h
  split at h
  · cases h
  have H : ∀ (is : List Nat) (c1 c2 : Conf) (j : Nat),
      c1.cin.length ≤ K + j * E → c1.cout.length ≤ K + j * E →
      is.foldlM (fun c (i : Nat) => do let e ← atE l ((i : Int) + 1); if isConf e then nextConf c e.value else pure c) c1 = .ok c2 →
      c2.cin.length ≤ K + (j + is.length) * E ∧ c2.cout.length ≤ K + (j + is.length) * E := by
    intro is
    induction is with
    | nil => intro c1 c2 j h1 h2 h; cases h; simpa using ⟨h1, h2⟩
    | cons i t ih =>
      intro c1 c2 j h1 h2 h
      rw [List.foldlM_cons] at h
      obtain ⟨c3, hc3, h⟩ := bind_ok h
      obtain ⟨e, he, hc3⟩ := bind_ok hc3
      have hE := hl e (atE_mem he)
      have hj : K + j * E + E = K + (j + 1) * E := by rw [Nat.add_mul, Nat.one_mul]; omega
      have h3 : c3.cin.length ≤ K + (j + 1) * E ∧ c3.cout.length ≤ K + (j + 1) * E := by
        split at hc3
        · have := nextConf_length hc3
          unfold Entry.chgSize at hE
          constructor <;> omega
        · cases hc3; constructor <;> omega
      have := ih c3 c2 (j + 1) h3.1 h3.2 h
      simp only [List.length_cons]
      rw [show j + (t.length + 1) = j + 1 + t.length by omega]
      exact this
  have := H _ c0 c 0 (by simpa using h0.1) (by simpa using h0.2) h
  simpa using this

/-- `LastConf(l, a)` is between `0` and `a`. -/
theorem bootSend_lastConf_bounds {l : List Entry} {a x : Int} (h : lastConf l a = .ok x) :
    0 ≤ x ∧ x ≤ a.toNat := by
  unfold lastConf at h
  have H : ∀ (is : List Nat) (x0 x1 : Int), 0 ≤ x0 → x0 ≤ a.toNat → (∀ i ∈ is, i < a.toNat) →
      is.foldlM (fun (last : Int) (i : Nat) => (atE l ((i : Int) + 1) >>= fun e =>
        pure (if isConf e then ((i + 1 : Nat) : Int) else last) : EvalM Int)) x0 = Except.ok x1 →
      0 ≤ x1 ∧ x1 ≤ a.toNat := by
    intro is
    induction is with
    | nil => intro x0 x1 h1 h2 _ h; cases h; exact ⟨h1, h2⟩
    | cons i t ih =>
      intro x0 x1 h1 h2 hi h
      rw [List.foldlM_cons] at h
      obtain ⟨x3, hx3, h⟩ := bind_ok h
      obtain ⟨e, -, hx3⟩ := bind_ok hx3
      have hia := hi i List.mem_cons_self
      have h3 : 0 ≤ x3 ∧ x3 ≤ a.toNat := by
        cases hx3; split <;> omega
      exact ih x3 x1 h3.1 h3.2 (fun j hj => hi j (List.mem_cons_of_mem _ hj)) h
  exact H _ 0 x (Int.le_refl _) (by omega) (fun i hi => List.mem_range.1 hi) h

/-- `lset.add`'s length. -/
theorem bootSend_lsetAdd_length {α : Type} [DecidableEq α] (s : List α) (x : α) :
    (lset.add s x).length ≤ s.length + 1 := by
  unfold lset.add; split <;> simp

theorem bootSend_mem_lsetAdd {α : Type} [DecidableEq α] {s : List α} {x y : α} (h : y ∈ lset.add s x) :
    y = x ∨ y ∈ s := by
  unfold lset.add at h; split at h
  · exact .inr h
  · rcases List.mem_append.1 h with h | h
    · exact .inr h
    · exact .inl (List.mem_singleton.1 h)

theorem bootSend_mem_lsetMinus {α : Type} [DecidableEq α] {s t : List α} {y : α} (h : y ∈ lset.minus s t) :
    y ∈ s := by
  unfold lset.minus at h; exact (List.mem_filter.1 h).1

theorem bootSend_lsetMinus_length {α : Type} [DecidableEq α] (s t : List α) :
    (lset.minus s t).length ≤ s.length := by
  unfold lset.minus; exact List.length_filter_le _ _

/-! ## `Send`'s updates within budget -/

/-- A fact added to `msgs`: the budget one more. -/
theorem bootSend_within_msgsAdd {s : State} {b E : Nat} {f : Fact} (h : s.Within b E) (hf : f.NumsOk) :
    ({ s with msgs := lset.add s.msgs f } : State).Within (b + 1) E := by
  have h' := State.Within.mono' (b' := b + 1) (E' := E) (by omega) (Nat.le_refl _) h
  refine ⟨h'.cfg, h'.i_pos, h'.i_le, h'.currentTerm, h'.voteTerm, h'.commitIndex, h'.lastApplied, h'.confAt, h'.confirmed, h'.log, h'.chain, h'.ledLog_len, h'.ledLog, h'.config, h'.ledConf_len, h'.ledConf, h'.ledAt, h'.elAt, h'.termLen, ?_, ?_, h'.votes_len, h'.votes, h'.leaders_len, h'.leaders, h'.undo, h'.pending, h'.queue, h'.reads, h'.viol⟩
  · show (lset.add s.msgs f).length ≤ 2 * (b + 1)
    have := bootSend_lsetAdd_length s.msgs f; have := h.msgs_len; omega
  · intro g hg
    rcases bootSend_mem_lsetAdd hg with hg | hg
    · subst hg; exact hf
    · exact h.msgs g hg

/-- `confirmed[n]` replaced by numbers within budget. -/
theorem bootSend_within_confirmedSet {s : State} {b E n : Nat} {c : Confirmed} (h : s.Within b E)
    (hc : bigOk c.term ∧ bigOk c.index) :
    ({ s with confirmed := s.confirmed.set n c } : State).Within b E :=
  ⟨h.cfg, h.i_pos, h.i_le, h.currentTerm, h.voteTerm, h.commitIndex, h.lastApplied, h.confAt, forall_mem_set h.confirmed hc, h.log, h.chain, h.ledLog_len, h.ledLog, h.config, h.ledConf_len, h.ledConf, h.ledAt, h.elAt, h.termLen, h.msgs_len, h.msgs, h.votes_len, h.votes, h.leaders_len, h.leaders, h.undo, h.pending, h.queue, h.reads, h.viol⟩

/-- `undo[n]` cleared. -/
theorem bootSend_within_undoNone {s : State} {b E n : Nat} (h : s.Within b E) :
    ({ s with undo := s.undo.set n none } : State).Within b E :=
  ⟨h.cfg, h.i_pos, h.i_le, h.currentTerm, h.voteTerm, h.commitIndex, h.lastApplied, h.confAt, h.confirmed, h.log, h.chain, h.ledLog_len, h.ledLog, h.config, h.ledConf_len, h.ledConf, h.ledAt, h.elAt, h.termLen, h.msgs_len, h.msgs, h.votes_len, h.votes, h.leaders_len, h.leaders, forall_mem_set h.undo (fun u hu => by cases hu), h.pending, h.queue, h.reads, h.viol⟩

end AntCheck
end EtcdGrove
end Perennial
