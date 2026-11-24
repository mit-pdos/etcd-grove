/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the budget law of `Step`
(`State.step_within_of`, from `Bind`'s): `I` one more.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Bind

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

theorem State.step_within_of (onDisk_keeps : W6Laws.OnDiskKeeps) (inMemory_within : InMemoryWithin)
    (onDisk_within : OnDiskWithin) (boot_within : ActionWithin State.boot)
    (send_within : ActionWithin State.send) : StepWithin := by
  intro s ev b E s' hW hNO hCh hb ho hv
  have hw2 : ev.weight = ev.size + 2 := rfl
  unfold State.step at ho
  split at ho
  · cases ho
  obtain ⟨n, hn, ho⟩ := bind_ok ho
  have hnl : n < s.cfg.server.length := by
    unfold State.idx at hn
    split at hn
    · rename_i k hk
      simp only [pure_ok, Except.ok.injEq] at hn
      subst hn
      exact (List.findIdx?_eq_some_iff_getElem.1 hk).1
    · cases hn
  obtain ⟨o, hob, ho⟩ := bind_ok ho
  cases o with
  | none => cases ho
  | some ns =>
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    have hns := State.bind_within_of onDisk_keeps inMemory_within onDisk_within boot_within send_within
      s n ev b E ns hnl hW hNO hCh hb hob hv
    obtain ⟨h0, -, -, h1, h2, h3, h4, h5, h6, hlog, hch, hll1, hll2, hcf, hlc1, hlc2, hla, hel,
      htl, hm1, hm2, hv1, hv2, hl1, hl2, hu, hp, hq, hrd, hvi⟩ := hns
    have := hW.i_pos; have := hW.i_le
    exact ⟨h0, by simp only; omega, by simp only; omega, h1, h2, h3, h4, h5, h6, hlog, hch, hll1, hll2, hcf,
      hlc1, hlc2, hla, hel, htl, hm1, hm2, hv1, hv2, hl1, hl2, hu, hp, hq, hrd, hvi⟩

end AntCheck
end EtcdGrove
end Perennial
