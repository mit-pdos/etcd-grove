/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `Recv` (`State.recv_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.recv_within : ActionWithin State.recv := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.recv at ho
  obtain ⟨m, hm, ho⟩ := bind_ok ho
  have hmsg := need_ok hm
  have hmn : m.NumsOk := hNO.2.2.2.2.2.2.2.2.2.2.2.1 m hmsg
  have hms : m.size ≤ ev.size := by unfold Event.size; rw [hmsg]; simp; omega
  have hmc : m.ChgOk E := by
    intro l hl e he
    exact hCh l (by unfold Event.entryLists; rw [hmsg]; simp; exact .inr (.inl hl)) e he
  have key : s' = { s with pending := s.pending.set n [m] } := by
    obtain ⟨dst, -, ho⟩ := bind_ok ho
    split at ho
    · cases ho
    obtain ⟨c, -, ho⟩ := bind_ok ho
    split at ho
    · obtain ⟨c2, -, ho⟩ := bind_ok ho
      split at ho
      · cases ho
      · cases ho; rfl
    · cases ho; rfl
  subst key
  refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, hW'.undo, ?_, hW'.queue, hW'.reads, hW'.viol⟩
  refine forall_mem_set hW'.pending ⟨by simp; omega, fun m' hm' => ?_⟩
  rw [List.mem_singleton] at hm'; subst hm'
  exact ⟨hmn, by unfold Event.weight; omega, hmc⟩

end AntCheck
end EtcdGrove
end Perennial
