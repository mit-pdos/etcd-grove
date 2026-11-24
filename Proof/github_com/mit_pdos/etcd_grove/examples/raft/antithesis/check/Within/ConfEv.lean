/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `ConfEv` (`State.confEv_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.confEv_within : ActionWithin State.confEv := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.confEv at ho
  obtain ⟨k, hk, ho⟩ := bind_ok ho
  have hkn : numOk k := by have := hNO.2.2.2.2.2.2.2.2.1; rw [need_ok hk] at this; exact this
  try dsimp only at ho
  split at ho
  · cases ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨e, he, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  try dsimp only at ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨e3, he3, ho⟩ := bind_ok ho
  rw [he] at he3; cases he3
  obtain ⟨c, hc, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  try dsimp only at ho
  -- the new configuration within budget
  have hlog : logWithin b E (s.log[n]!) :=
    getElem!_mem' (α := List Entry) (P := fun l => logWithin b E l) hW.log ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  have heb : e.chgSize ≤ E := (hlog.2 e (atE_mem he)).2
  have hcw : confWithin s.cfg.initVoters.length b E (s.config[n]!) :=
    getElem!_mem' (α := Conf) (P := fun c => confWithin s.cfg.initVoters.length b E c) hW.config
      ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hnc := nextConf_length hc
  have hcw' : confWithin s.cfg.initVoters.length (b + ev.weight) E c := by
    unfold confWithin at hcw ⊢; unfold Entry.chgSize at heb
    have : b * E + E ≤ (b + ev.weight) * E := by
      rw [Nat.add_mul]; have := Nat.mul_le_mul_right E hw2; omega
    constructor <;> omega
  have hct : bigOk (s.currentTerm[n]!) :=
    getElem!_mem' (α := Int) (P := bigOk) hW.currentTerm ⟨by decide, by decide⟩
  have hcf := forall_mem_set (n := n) (x := c) hW'.config hcw'
  have hca := forall_mem_set (n := n) (x := k) hW'.confAt (bigOk_of_numOk hkn)
  split at ho <;> simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho <;> subst ho
  · refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, ?_, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, ?_, ?_, ?_, ?_, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, hW'.undo, hW'.pending, hW'.queue, hW'.reads, hW'.viol⟩
    · intro x hx; exact hca x hx
    · intro x hx; exact hcf x hx
    · show (s.ledConf.with (s.currentTerm[n]!) c).length ≤ b + ev.weight
      have := TermFn.with_length_le s.ledConf (s.currentTerm[n]!) c; have := hW.ledConf_len; omega
    · intro q hq
      rcases TermFn.mem_with hq with h | h
      · subst h; exact ⟨hct, hcw'⟩
      · exact hW'.ledConf q h
    · exact termIntsWithin.mono' (by omega) (termIntsWithin_with hW.ledAt hct (bigOk_of_numOk hkn))
  · refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, ?_, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, ?_, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, hW'.undo, hW'.pending, hW'.queue, hW'.reads, hW'.viol⟩
    · intro x hx; exact hca x hx
    · intro x hx; exact hcf x hx

end AntCheck
end EtcdGrove
end Perennial
