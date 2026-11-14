/- Lean-first (no Rocq counterpart).
# The open handle's lock token (W4 of `notes/wal-fsext-plan.md`, twenty-fifth session)

`walOpenW_lockedTok`: the sealed ghost handle `walOpenW` holds the lock token `walLockedTok` (what a
`Close` whose `sync` failed still holds: `WAL.sync.specC`'s error arm; ledger 2026-11-14).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode

section ghost
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- **The open handle holds the lock token.** -/
theorem walOpenW_lockedTok (w : Loc) (dir : GoString) :
    walOpenW (W := W) w dir ⊢ walLockedTok (W := W) := by
  unfold walOpenW
  iintro ⟨-, Hl⟩
  iexact Hl

end ghost

end WalFs
end EtcdGrove
end Perennial

end
