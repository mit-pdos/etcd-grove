/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): `State.Within`'s parts by name (its
thirty conjuncts, in `Rep.lean`'s order), for the budget laws and the actions' arithmetic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

namespace State.Within
variable {b E : Nat} {s : State}

theorem cfg (h : s.Within b E) : Config.Bounded s.cfg := h.1
theorem i_pos (h : s.Within b E) : 1 ≤ s.i := h.2.1
theorem i_le (h : s.Within b E) : s.i ≤ b := h.2.2.1
theorem currentTerm (h : s.Within b E) : ∀ x ∈ s.currentTerm, bigOk x := h.2.2.2.1
theorem voteTerm (h : s.Within b E) : ∀ x ∈ s.voteTerm, bigOk x := h.2.2.2.2.1
theorem commitIndex (h : s.Within b E) : ∀ x ∈ s.commitIndex, bigOk x := h.2.2.2.2.2.1
theorem lastApplied (h : s.Within b E) : ∀ x ∈ s.lastApplied, bigOk x := h.2.2.2.2.2.2.1
theorem confAt (h : s.Within b E) : ∀ x ∈ s.confAt, bigOk x := h.2.2.2.2.2.2.2.1
theorem confirmed (h : s.Within b E) : ∀ c ∈ s.confirmed, bigOk c.term ∧ bigOk c.index := h.2.2.2.2.2.2.2.2.1
theorem log (h : s.Within b E) : ∀ l ∈ s.log, logWithin b E l := h.2.2.2.2.2.2.2.2.2.1
theorem chain (h : s.Within b E) : logWithin b E s.chain := h.2.2.2.2.2.2.2.2.2.2.1
theorem ledLog_len (h : s.Within b E) : s.ledLog.length ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem ledLog (h : s.Within b E) : ∀ p ∈ s.ledLog, bigOk p.1 ∧ logWithin b E p.2 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem config (h : s.Within b E) : ∀ c ∈ s.config, confWithin s.cfg.initVoters.length b E c := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ledConf_len (h : s.Within b E) : s.ledConf.length ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ledConf (h : s.Within b E) : ∀ p ∈ s.ledConf, bigOk p.1 ∧ confWithin s.cfg.initVoters.length b E p.2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ledAt (h : s.Within b E) : termIntsWithin b s.ledAt := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem elAt (h : s.Within b E) : termIntsWithin b s.elAt := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem termLen (h : s.Within b E) : termIntsWithin b s.termLen := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem msgs_len (h : s.Within b E) : s.msgs.length ≤ 2 * b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem msgs (h : s.Within b E) : ∀ f ∈ s.msgs, f.NumsOk := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem votes_len (h : s.Within b E) : s.votes.length ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem votes (h : s.Within b E) : ∀ v ∈ s.votes, bigOk v.term := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem leaders_len (h : s.Within b E) : s.leaders.length ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem leaders (h : s.Within b E) : ∀ l ∈ s.leaders, bigOk l.term := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem undo (h : s.Within b E) : ∀ o ∈ s.undo, ∀ u, o = some u → u.Within b E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pending (h : s.Within b E) : ∀ ms ∈ s.pending, ms.length ≤ b ∧ ∀ m ∈ ms, m.Within b E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem queue (h : s.Within b E) : ∀ q ∈ s.queue, q.length ≤ b ∧ ∀ it ∈ q, it.ev.Within b E ∧ it.m.length ≤ b ∧ ∀ m ∈ it.m, m.Within b E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem reads (h : s.Within b E) : ∀ r ∈ s.reads, r.length ≤ b ∧ ∀ x ∈ r, bigOk x.floor := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem viol (h : s.Within b E) : s.viol.length ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- `s.Within b E` from its thirty parts. -/
theorem intro (h0 : Config.Bounded s.cfg) (h1 : 1 ≤ s.i) (h2 : s.i ≤ b) (h3 : ∀ x ∈ s.currentTerm, bigOk x) (h4 : ∀ x ∈ s.voteTerm, bigOk x) (h5 : ∀ x ∈ s.commitIndex, bigOk x) (h6 : ∀ x ∈ s.lastApplied, bigOk x) (h7 : ∀ x ∈ s.confAt, bigOk x) (h8 : ∀ c ∈ s.confirmed, bigOk c.term ∧ bigOk c.index) (h9 : ∀ l ∈ s.log, logWithin b E l) (h10 : logWithin b E s.chain) (h11 : s.ledLog.length ≤ b) (h12 : ∀ p ∈ s.ledLog, bigOk p.1 ∧ logWithin b E p.2) (h13 : ∀ c ∈ s.config, confWithin s.cfg.initVoters.length b E c) (h14 : s.ledConf.length ≤ b) (h15 : ∀ p ∈ s.ledConf, bigOk p.1 ∧ confWithin s.cfg.initVoters.length b E p.2) (h16 : termIntsWithin b s.ledAt) (h17 : termIntsWithin b s.elAt) (h18 : termIntsWithin b s.termLen) (h19 : s.msgs.length ≤ 2 * b) (h20 : ∀ f ∈ s.msgs, f.NumsOk) (h21 : s.votes.length ≤ b) (h22 : ∀ v ∈ s.votes, bigOk v.term) (h23 : s.leaders.length ≤ b) (h24 : ∀ l ∈ s.leaders, bigOk l.term) (h25 : ∀ o ∈ s.undo, ∀ u, o = some u → u.Within b E) (h26 : ∀ ms ∈ s.pending, ms.length ≤ b ∧ ∀ m ∈ ms, m.Within b E) (h27 : ∀ q ∈ s.queue, q.length ≤ b ∧ ∀ it ∈ q, it.ev.Within b E ∧ it.m.length ≤ b ∧ ∀ m ∈ it.m, m.Within b E) (h28 : ∀ r ∈ s.reads, r.length ≤ b ∧ ∀ x ∈ r, bigOk x.floor) (h29 : s.viol.length ≤ b) : s.Within b E :=
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

end State.Within

/-- A list's element, by membership (`l[n]!` of an in-bounds `n`). -/
theorem getElem!_mem {α : Type} [Inhabited α] {l : List α} {n : Nat} (h : n < l.length) : l[n]! ∈ l := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

/-- Every element of `l.set n x` is `x` or one of `l`'s. -/
theorem mem_set_or {α : Type} {l : List α} {n : Nat} {x y : α} (h : y ∈ l.set n x) : y = x ∨ y ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons a t ih =>
    cases n with
    | zero => simp at h; rcases h with h | h; exact .inl h; exact .inr (List.mem_cons_of_mem _ h)
    | succ m =>
      simp at h; rcases h with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases ih h with h' | h'; exact .inl h'; exact .inr (List.mem_cons_of_mem _ h')

end AntCheck
end EtcdGrove
end Perennial
