/- Lean-first (no Rocq counterpart).

# The truncate's first step from a pending tail (I3b, `wal-tc18`; pure)

`ZeroToEnd`'s truncate at the write position of the tail `ReadAll` registered, once the lent token
says F-Z or `TailPend` (`walLentRes_pendStop`, `TailZK.zp`): its first step's crash condition is
`crashOkA_tailPend` when the tail is pending (nothing written past the start's frames, the length word
at `wr` zero), `tailCrashStep_rzStart` (F-Z) otherwise.

* `rzSeg_zf`: the announced tail's known zeros past its bytes, from the start's `TcZ`;
(P6 item 2: the pending first step is `rzStart_pureR`'s, `TailCrashRep.lean`: `TailPend` is `RepOld`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSupPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashPend

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **The announced tail's known zeros are past its bytes** (the start's `TcZ`: `zf` at least the
size; `announce` only raises it). -/
theorem rzSeg_zf {g0 : SegG} {tr : Bool} {tg n : Nat} (hlen : g0.bs.length = g0.om.size)
    (htcz : g0.om.TcZ) : ∀ z, (rzSeg g0 tr tg n).om.zf = some z → (rzSeg g0 tr tg n).bs.length ≤ z := by
  intro z hz
  rw [rzSeg_length, hlen]
  simp only [rzSeg, rzMeta, OsMeta.announce, Option.map_eq_some_iff] at hz
  obtain ⟨z0, hz0, rfl⟩ := hz
  have := htcz.1 z0 hz0
  split <;> omega

end pure

end WalFs
end EtcdGrove
end Perennial

end
