/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `ApplyEv` (`State.applyEv_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.applyEv_within : ActionWithin State.applyEv := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.applyEv at ho
  obtain ⟨fi, hfi, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨fi2, hfi2, ho⟩ := bind_ok ho
  rw [hfi] at hfi2; cases hfi2
  obtain ⟨es, hes, ho⟩ := bind_ok ho
  have hfin : numOk fi := by have := hNO.2.2.1; rw [need_ok hfi] at this; exact this
  have hesz : es.length ≤ ev.size := by unfold Event.size; rw [need_ok hes]; simp; omega
  unfold numOk numBound at hfin
  have hlast : bigOk (fi + (es.length : Int) - 1) := by unfold bigOk Event.weight at *; omega
  generalize fi + (es.length : Int) - 1 = last at ho hlast
  try dsimp only at ho
  split at ho
  · cases ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  obtain ⟨_, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  try dsimp only at ho
  have hla := forall_mem_set (n := n) (x := last) hW'.lastApplied hlast
  cases ha : ev.a <;> simp only [ha, Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true] at ho <;>
    obtain ⟨mc, -, ho⟩ := bind_ok ho <;> split at ho <;>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho <;> subst ho
  · exact absurd hv (setAdd_ne_nil _ _)
  · refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, ?_, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, ?_, hW'.pending, hW'.queue, hW'.reads, hW'.viol⟩
    · exact hla
    · exact forall_mem_set hW'.undo (fun u' h => by cases h)
  · exact absurd hv (setAdd_ne_nil _ _)
  · refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, ?_, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, hW'.undo, hW'.pending, hW'.queue, hW'.reads, hW'.viol⟩
    exact hla

end AntCheck
end EtcdGrove
end Perennial
