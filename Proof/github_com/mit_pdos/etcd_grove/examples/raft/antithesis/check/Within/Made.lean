/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `Made` (`State.made_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.made_within : ActionWithin State.made := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.made at ho
  cases hu : s.undo[n]! with
  | none => rw [hu] at ho; cases ho
  | some u =>
    rw [hu] at ho
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    have huw := hW'.undo _ (getElem!_some_mem hu) u rfl
    refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, ?_, hW'.pending, hW'.queue, hW'.reads, hW'.viol⟩
    exact forall_mem_set hW'.undo (fun u' h => by cases h; unfold Pre.Within at huw ⊢; exact huw)

end AntCheck
end EtcdGrove
end Perennial
