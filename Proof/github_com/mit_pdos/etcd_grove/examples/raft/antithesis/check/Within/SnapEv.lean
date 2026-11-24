/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `SnapEv` (`State.snapEv_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.snapEv_within : ActionWithin State.snapEv := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.snapEv at ho
  obtain ⟨c, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  obtain ⟨i, -, ho⟩ := bind_ok ho
  obtain ⟨t, -, ho⟩ := bind_ok ho
  split at ho
  · cases ho
  cases ho
  exact hW'

end AntCheck
end EtcdGrove
end Perennial
