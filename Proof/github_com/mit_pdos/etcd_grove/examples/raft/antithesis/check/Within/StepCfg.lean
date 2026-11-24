/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): no action writes `cfg`
(`State.step_cfg`, for W7): `Step`'s successor has its state's configuration. The actions of other
groups are taken as hypotheses (`<act>_cfg : W6Laws.KeepsCfg State.<act>`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-- An action keeps `cfg`. -/
abbrev W6Laws.KeepsCfg (act : State → Nat → Event → EvalM (Option State)) : Prop :=
  ∀ (s : State) (n : Nat) (ev : Event) (s' : State), act s n ev = .ok (some s') → s'.cfg = s.cfg

theorem State.mem_cfg : W6Laws.KeepsCfg State.mem := by
  intro s n ev s' h
  unfold State.mem at h
  obtain ⟨r, -, h⟩ := bind_ok h
  split at h
  · simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  obtain ⟨w, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨q, -, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at h; subst h; rfl
  · simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at h; subst h; rfl

theorem State.flush_cfg_of (onDisk_keeps : W6Laws.OnDiskKeeps) : W6Laws.KeepsCfg State.flush := by
  intro s n ev s' h
  unfold State.flush at h
  split at h
  · simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨o, hod, h⟩ := bind_ok h
  cases o with
  | none => simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  | some ns =>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at h; subst h
    exact (onDisk_keeps _ _ _ _ _ _ _ _ _ _ _ hod).1

theorem State.write_cfg_of (onDisk_keeps : W6Laws.OnDiskKeeps) : W6Laws.KeepsCfg State.write := by
  intro s n ev s' h
  unfold State.write at h
  split at h
  · simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  obtain ⟨o, hod, h⟩ := bind_ok h
  cases o with
  | none => simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  | some ns =>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at h; subst h
    exact (onDisk_keeps _ _ _ _ _ _ _ _ _ _ _ hod).1

theorem State.ready_cfg_of (onDisk_keeps : W6Laws.OnDiskKeeps) : W6Laws.KeepsCfg State.ready := by
  intro s n ev s' h
  unfold State.ready at h
  split at h
  · simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  obtain ⟨r, -, h⟩ := bind_ok h
  split at h
  · simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨o, hod, h⟩ := bind_ok h
  cases o with
  | none => simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  | some ns =>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at h; subst h
    exact (onDisk_keeps _ _ _ _ _ _ _ _ _ _ _ hod).1

theorem State.bind_cfg_of (onDisk_keeps : W6Laws.OnDiskKeeps)
    (boot_cfg : W6Laws.KeepsCfg State.boot)
    (recv_cfg : W6Laws.KeepsCfg State.recv)
    (wrote_cfg : W6Laws.KeepsCfg State.wrote)
    (net_cfg : W6Laws.KeepsCfg State.net)
    (made_cfg : W6Laws.KeepsCfg State.made)
    (send_cfg : W6Laws.KeepsCfg State.send)
    (applyEv_cfg : W6Laws.KeepsCfg State.applyEv)
    (restoreEv_cfg : W6Laws.KeepsCfg State.restoreEv)
    (confEv_cfg : W6Laws.KeepsCfg State.confEv)
    (snapEv_cfg : W6Laws.KeepsCfg State.snapEv)
    (readAsked_cfg : W6Laws.KeepsCfg State.readAsked)
    (readGiven_cfg : W6Laws.KeepsCfg State.readGiven) :
    W6Laws.KeepsCfg State.bind := by
  intro s n ev s' h
  unfold State.bind at h
  by_cases h_boot : (ev.e == go!"boot") = true
  · simp only [h_boot, ↓reduceIte] at h; exact boot_cfg s n ev s' h
  simp only [h_boot, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_recv : (ev.e == go!"recv") = true
  · simp only [h_recv, ↓reduceIte] at h; exact recv_cfg s n ev s' h
  simp only [h_recv, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_ready : (ev.e == go!"ready") = true
  · simp only [h_ready, ↓reduceIte] at h; exact State.ready_cfg_of onDisk_keeps s n ev s' h
  simp only [h_ready, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_mem : (ev.e == go!"mem") = true
  · simp only [h_mem, ↓reduceIte] at h; exact State.mem_cfg s n ev s' h
  simp only [h_mem, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_write : (ev.e == go!"write") = true
  · simp only [h_write, ↓reduceIte] at h; exact State.write_cfg_of onDisk_keeps s n ev s' h
  simp only [h_write, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_wrote : (ev.e == go!"wrote") = true
  · simp only [h_wrote, ↓reduceIte] at h; exact wrote_cfg s n ev s' h
  simp only [h_wrote, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_flush : (ev.e == go!"flush") = true
  · simp only [h_flush, ↓reduceIte] at h; exact State.flush_cfg_of onDisk_keeps s n ev s' h
  simp only [h_flush, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_net : (ev.e == go!"net") = true
  · simp only [h_net, ↓reduceIte] at h; exact net_cfg s n ev s' h
  simp only [h_net, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_made : (ev.e == go!"made") = true
  · simp only [h_made, ↓reduceIte] at h; exact made_cfg s n ev s' h
  simp only [h_made, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_send : (ev.e == go!"send") = true
  · simp only [h_send, ↓reduceIte] at h; exact send_cfg s n ev s' h
  simp only [h_send, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_apply : (ev.e == go!"apply") = true
  · simp only [h_apply, ↓reduceIte] at h; exact applyEv_cfg s n ev s' h
  simp only [h_apply, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_restore : (ev.e == go!"restore") = true
  · simp only [h_restore, ↓reduceIte] at h; exact restoreEv_cfg s n ev s' h
  simp only [h_restore, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_conf : (ev.e == go!"conf") = true
  · simp only [h_conf, ↓reduceIte] at h; exact confEv_cfg s n ev s' h
  simp only [h_conf, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_snap : (ev.e == go!"snap") = true
  · simp only [h_snap, ↓reduceIte] at h; exact snapEv_cfg s n ev s' h
  simp only [h_snap, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_readreq : (ev.e == go!"readreq") = true
  · simp only [h_readreq, ↓reduceIte] at h; exact readAsked_cfg s n ev s' h
  simp only [h_readreq, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h_read : (ev.e == go!"read") = true
  · simp only [h_read, ↓reduceIte] at h; exact readGiven_cfg s n ev s' h
  simp only [h_read, Bool.false_eq_true, ↓reduceIte] at h
  simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h

/-- **`Step`'s successor has its state's configuration** (W7's `CheckLaws.StepCfg`). -/
theorem State.step_cfg_of (onDisk_keeps : W6Laws.OnDiskKeeps)
    (boot_cfg : W6Laws.KeepsCfg State.boot)
    (recv_cfg : W6Laws.KeepsCfg State.recv)
    (wrote_cfg : W6Laws.KeepsCfg State.wrote)
    (net_cfg : W6Laws.KeepsCfg State.net)
    (made_cfg : W6Laws.KeepsCfg State.made)
    (send_cfg : W6Laws.KeepsCfg State.send)
    (applyEv_cfg : W6Laws.KeepsCfg State.applyEv)
    (restoreEv_cfg : W6Laws.KeepsCfg State.restoreEv)
    (confEv_cfg : W6Laws.KeepsCfg State.confEv)
    (snapEv_cfg : W6Laws.KeepsCfg State.snapEv)
    (readAsked_cfg : W6Laws.KeepsCfg State.readAsked)
    (readGiven_cfg : W6Laws.KeepsCfg State.readGiven) :
    ∀ (s : State) (ev : Event) (s' : State), s.step ev = .ok (some s') → s'.cfg = s.cfg := by
  intro s ev s' h
  unfold State.step at h
  split at h
  · cases h
  obtain ⟨n, -, h⟩ := bind_ok h
  obtain ⟨o, hob, h⟩ := bind_ok h
  cases o with
  | none => simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at h
  | some ns =>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at h; subst h
    exact State.bind_cfg_of onDisk_keeps boot_cfg recv_cfg wrote_cfg net_cfg made_cfg send_cfg applyEv_cfg restoreEv_cfg confEv_cfg snapEv_cfg readAsked_cfg readGiven_cfg s n ev ns hob

end AntCheck
end EtcdGrove
end Perennial
