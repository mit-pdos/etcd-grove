/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `ReadGiven` (`State.readGiven_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.readGiven_within : ActionWithin State.readGiven := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.readGiven at ho
  obtain ⟨kept, hkept, ho⟩ := bind_ok ho
  obtain ⟨stale, -, ho⟩ := bind_ok ho
  have hr : (s.reads[n]!).length ≤ b ∧ ∀ x ∈ s.reads[n]!, bigOk x.floor :=
    getElem!_mem' (α := List ReadRec) (P := fun (r : List ReadRec) => r.length ≤ b ∧ ∀ x ∈ r, bigOk x.floor) hW.reads
      ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  obtain ⟨hk1, hk2⟩ := filterM_sub hkept
  cases stale
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, hW'.undo, hW'.pending, hW'.queue, ?_, hW'.viol⟩
    exact forall_mem_set hW'.reads ⟨by omega, fun x hx => hr.2 x (hk2 x hx)⟩
  · simp only [ite_true, pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    exact absurd hv (setAdd_ne_nil _ _)

end AntCheck
end EtcdGrove
end Perennial
