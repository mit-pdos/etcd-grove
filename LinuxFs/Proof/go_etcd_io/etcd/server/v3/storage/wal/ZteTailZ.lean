/- Lean-first (no Rocq counterpart).

# `ZeroToEnd`'s post gives the tail's `TailZ` back (I3b, `wal-tc12`; pure)

`ZeroToEnd.specAu`'s success post carries `ZteMeta m m'` (`DefsAu.lean`): with the tail's `TailZ m` (the zeros
known from `z ≥ size`, the page cache zero to `z`'s page, the candidates of `[size, z)` known), and the size
unchanged, `TailZ m'`: `m.pc` is known at every byte past the size, so `m'.pc` is (`PcKeep`), and below
`m'`'s known zeros that is `m'.tc`; `ZeroPg` is the rest. For `ZeroToEnd.specWalTail`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.DefsAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs

/-- **`TailZ` through `ZeroToEnd`** (see the file header). -/
theorem TailZ.zte {m m' : OsMeta} (h : TailZ m) (hsz : m'.size = m.size) (hz : ZteMeta m m') :
    TailZ m' := by
  obtain ⟨z, hzf, hs, -, hk⟩ := h
  obtain ⟨z', hz', hs', hp'⟩ := hz.2 ⟨z, hzf, hs⟩
  refine ⟨z', hz', hs', hp', fun b hb hbz => ?_⟩
  have hpm : (m.pc b).isSome := by
    unfold OsMeta.pc
    by_cases hbz0 : b < z
    · obtain ⟨c, hc⟩ := hk b (by omega) hbz0
      rw [hc]; rfl
    · cases hc : m.tc !! b with
      | some c => rfl
      | none => simp [hzf, show z ≤ b by omega]
  have hpc := hz.1 b (by omega) (by omega) hpm
  unfold OsMeta.pc at hpc
  cases hc : m'.tc !! b with
  | some c => exact ⟨c, rfl⟩
  | none =>
    simp [hc, hz', show ¬ z' ≤ b by omega] at hpc

end WalFs
end EtcdGrove
end Perennial

end
