/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the budget law of `Flush`
(`State.flush_within_of`, over `OnDisk`'s, `State.onDisk_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.flush_within_of (onDisk_within : OnDiskWithin) : ActionWithin State.flush := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold State.flush at ho
  cases hq : s.queue[n]! with
  | nil => rw [hq] at ho; cases ho
  | cons q rest =>
    rw [hq] at ho
    dsimp only at ho
    obtain ⟨mv, -, ho⟩ := bind_ok ho
    obtain ⟨o, hod, ho⟩ := bind_ok ho
    cases o with
    | none => cases ho
    | some ns =>
      simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
      subst ho
      have hns := onDisk_within s n q _ s.role s.leaders s.ledLog s.chain s.termLen s.viol b E ns hn
        (W6Laws.onDisk_within_self _ hW hq) (by omega) hod hv
      have hns' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hns
      have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
      exact W6Laws.within_set_queue hns' (W6Laws.queue_set_tail hW' hq)

end AntCheck
end EtcdGrove
end Perennial
