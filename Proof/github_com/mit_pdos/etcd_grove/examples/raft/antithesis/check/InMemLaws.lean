/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): pure laws of `InMem`'s methods for
their proofs and for `inMemory_within`: the report's term and entries, and the leader logs `ll1`,
`ll2` and the log `L` within the budget, so that the Go's `int` arithmetic on them does not
overflow.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-- `f[t]`, where defined, is one of `f`'s pairs. -/
theorem TermFn.mem_of_get {α : Type} {f : TermFn α} {t : Int} {v : α} (h : f.get t = .ok v) : (t, v) ∈ f := by
  unfold TermFn.get at h
  split at h
  · rename_i p hp
    simp only [pure_ok, Except.ok.injEq] at h
    have hm := List.mem_of_find?_eq_some hp
    have ht := List.find?_some hp
    simp only [beq_iff_eq] at ht
    obtain ⟨a, c⟩ := p
    simp only at ht h
    subst ht h
    exact hm
  · cases h

theorem logWithin_nil (b E : Nat) : logWithin b E [] := by simp [logWithin]

theorem logWithin_append {b b' E : Nat} {l l' : List Entry} (h : logWithin b E l) (h' : logWithin b' E l') :
    logWithin (b + b') E (l ++ l') := by
  refine ⟨by simp; have := h.1; have := h'.1; omega, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h.2 e he
  · exact h'.2 e he

namespace InMem
variable {x : InMem} {b E : Nat}

theorem T_bigOk (hN : x.ev.NumsOk) {t : Int} (h : x.T = .ok t) : bigOk t := by
  unfold InMem.T at h
  have h1 := hN.1
  rw [need_ok h] at h1
  exact bigOk_of_numOk h1

/-- The report's entries (`es`): no more than its size, each within the budget's numbers and
change size. -/
theorem es_within (hN : x.ev.NumsOk) (hC : x.ev.ChgOk E) {es : List Entry} (h : x.es = .ok es) :
    logWithin x.ev.size E es := by
  unfold InMem.es at h
  split at h
  · have he := need_ok h
    refine ⟨by unfold Event.size; rw [he]; simp; omega, fun e hm => ⟨?_, ?_⟩⟩
    · exact bigOk_of_numOk (hN.2.2.2.2.2.2.2.2.2.2.1 es he e hm)
    · exact hC (x.ev.entries.getD []) (by simp [Event.entryLists]) e (by rw [he]; simpa using hm)
  · simp only [pure_ok, Except.ok.injEq] at h
    subst h
    exact logWithin_nil _ _

/-- `ll1`: the leader logs, with the winner's log at `T`. -/
theorem ll1_within (hW : x.s.Within b E) (hN : x.ev.NumsOk) {l : TermFn (List Entry)} (h : x.ll1 = .ok l) :
    l.length ≤ b + 1 ∧ ∀ q ∈ l, bigOk q.1 ∧ logWithin b E q.2 := by
  unfold InMem.ll1 at h
  obtain ⟨w, -, h⟩ := bind_ok h
  cases w
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at h
    subst h
    exact ⟨by have := hW.ledLog_len; omega, hW.ledLog⟩
  · simp only [ite_true] at h
    obtain ⟨t, ht, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    refine ⟨by have := TermFn.with_length_le x.s.ledLog t (x.s.log[x.n]!); have := hW.ledLog_len; omega,
      fun q hq => ?_⟩
    rcases TermFn.mem_with hq with h' | h'
    · subst h'
      exact ⟨T_bigOk hN ht, getElem!_mem' hW.log (logWithin_nil b E)⟩
    · exact hW.ledLog q h'

theorem ll1_get_within (hW : x.s.Within b E) (hN : x.ev.NumsOk) {l : TermFn (List Entry)} (h : x.ll1 = .ok l)
    {t : Int} {v : List Entry} (hg : l.get t = .ok v) : logWithin b E v :=
  ((ll1_within hW hN h).2 _ (TermFn.mem_of_get hg)).2

/-- `app` holds only with entries reported. -/
theorem app_es (h : x.app = .ok true) {es : List Entry} (he : x.es = .ok es) : es.length ≠ 0 := by
  unfold InMem.app at h
  obtain ⟨l, -, ht, hf⟩ := andM_ok h
  cases l
  · cases hf rfl
  · obtain ⟨es', he', h⟩ := bind_ok (ht rfl)
    rw [he] at he'
    cases he'
    simp only [pure_ok, Except.ok.injEq, bne_iff_ne, ne_eq] at h
    exact h

/-- `ll2`: `ll1` with the leader's entries appended at `T`. -/
theorem ll2_within (hW : x.s.Within b E) (hN : x.ev.NumsOk) (hC : x.ev.ChgOk E) {l : TermFn (List Entry)}
    (h : x.ll2 = .ok l) :
    l.length ≤ b + x.ev.size + 1 ∧ ∀ q ∈ l, bigOk q.1 ∧ logWithin (b + x.ev.size) E q.2 := by
  unfold InMem.ll2 at h
  obtain ⟨c, hc, h⟩ := bind_ok h
  cases c
  · simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨h1, h2⟩ := ll1_within hW hN h
    exact ⟨by omega, fun q hq => ⟨(h2 q hq).1, logWithin.mono' (by omega) (Nat.le_refl _) (h2 q hq).2⟩⟩
  · simp only [ite_true] at h
    obtain ⟨l1, hl1, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨g, hg, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    obtain ⟨a, ha, hat, haf⟩ := andM_ok hc
    cases a
    · cases haf rfl
    have hesw := es_within hN hC hes
    have hne := app_es ha hes
    obtain ⟨h1, h2⟩ := ll1_within hW hN hl1
    refine ⟨by have := TermFn.with_length_le l1 t (g ++ es); have := hesw.1; omega, fun q hq => ?_⟩
    rcases TermFn.mem_with hq with h' | h'
    · subst h'
      exact ⟨T_bigOk hN ht, logWithin_append (ll1_get_within hW hN hl1 hg) hesw⟩
    · exact ⟨(h2 q h').1, logWithin.mono' (by omega) (Nat.le_refl _) (h2 q h').2⟩

/-- `L`: the leader's log at `T` after its appends. -/
theorem L_within (hW : x.s.Within b E) (hN : x.ev.NumsOk) (hC : x.ev.ChgOk E) {l : List Entry}
    (h : x.L = .ok l) : logWithin (b + x.ev.size) E l := by
  unfold InMem.L at h
  obtain ⟨l2, hl2, h⟩ := bind_ok h
  obtain ⟨t, -, h⟩ := bind_ok h
  split at h
  · exact ((ll2_within hW hN hC hl2).2 _ (TermFn.mem_of_get h)).2
  · simp only [pure_ok, Except.ok.injEq] at h
    subst h
    exact logWithin_nil _ _

end InMem

end AntCheck
end EtcdGrove
end Perennial
