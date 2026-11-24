/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `Net` (`State.net_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.net_within : ActionWithin State.net := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.net at ho
  cases hu : s.undo[n]! with
  | none => rw [hu] at ho; cases ho
  | some u =>
    rw [hu] at ho
    dsimp only at ho
    have huw := hW'.undo _ (getElem!_some_mem hu) u rfl
    have key : s' = { s with undo := s.undo.set n (some { u with low := 0 }) } := by
      obtain ⟨c, -, ho⟩ := bind_ok ho
      split at ho
      · cases ho
      obtain ⟨es, -, ho⟩ := bind_ok ho
      split at ho
      · split at ho
        · cases ho
        · cases ho; rfl
      · try dsimp only at ho
        obtain ⟨c2, -, ho⟩ := bind_ok ho
        split at ho
        · cases ho
        · cases ho; rfl
    subst key
    refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, ?_, hW'.pending, hW'.queue, hW'.reads, hW'.viol⟩
    refine forall_mem_set hW'.undo (fun u' h => ?_)
    cases h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := huw
    exact ⟨h1, h2, h3, h4, h5, h6, (show bigOk 0 from ⟨by decide, by decide⟩), h8, h9, h10, h11, h12, h13, h14, h15⟩

end AntCheck
end EtcdGrove
end Perennial
