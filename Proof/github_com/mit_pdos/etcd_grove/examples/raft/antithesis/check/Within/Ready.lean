/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the budget law of `Ready`
(`State.ready_within_of`, over `InMemory`'s and `OnDisk`'s, and `OnDisk` keeping `cfg`): `InMemory`'s
result within `b + ev.size + 1`, `OnDisk`'s successor one more.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.ready_within_of (onDisk_keeps : W6Laws.OnDiskKeeps) (inMemory_within : InMemoryWithin)
    (onDisk_within : OnDiskWithin) : ActionWithin State.ready := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hw2 : ev.weight = ev.size + 2 := rfl
  unfold State.ready at ho
  split at ho
  · cases ho
  obtain ⟨r, hr, ho⟩ := bind_ok ho
  have hrW := inMemory_within s n ev b E r hn hW hNO hCh hb hr
  split at ho
  · cases ho
  obtain ⟨qi, hqi, ho⟩ := bind_ok ho
  obtain ⟨o, hod, ho⟩ := bind_ok ho
  cases o with
  | none => cases ho
  | some ns =>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    have hW1 := State.Within.mono' (b' := b + ev.size + 1) (E' := E) (by omega) (Nat.le_refl _) hW
    have hqW := W6Laws.queued_within hW1 ⟨hNO, by omega, hCh⟩ hqi
    have hns := onDisk_within s n qi false r.role r.leaders r.ledLog r.chain r.termLen r.viol (b + ev.size + 1) E ns hn
      (W6Laws.onDisk_within_ready hW1 hrW hW1.viol hqW) (by rw [show b + ev.size + 1 + 1 = b + ev.weight by omega]; exact hb)
      hod hv
    rw [show b + ev.size + 1 + 1 = b + ev.weight by omega] at hns
    exact W6Laws.within_ready hns (onDisk_keeps _ _ _ _ _ _ _ _ _ _ _ hod).1
      (W6Laws.MemResult.Within.mono (by omega) hrW)

end AntCheck
end EtcdGrove
end Perennial
