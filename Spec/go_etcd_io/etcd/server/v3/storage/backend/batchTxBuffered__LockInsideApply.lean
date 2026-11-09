/-
## `(*batchTxBuffered).LockInsideApply()` (promoted `batchTx.LockInsideApply`, `batch_tx.go:118-128`): translated

**Users.** The apply thread's writers: mvcc's write transactions (`kvstore_txn.go:177`,
`store.go:38` `SetScheduledCompact`), the lessor (`lease.go:58` `persistTo`), the schema's apply
writers (`membership.go:58, 77, 152, 166`, `alarm.go:54, 70`, `auth.go:109`). Snippet `parts.go`
(`ReqWriteThenRead` with a hook).

**Proof sketch.** `t.lock()` (the session, `Pk`); the hook field read under the lock (its
authority agrees with the caller's share: `f`); if non-nil, `ValidateCalledInsideApply` (a no-op:
`envOk`) and `f()` by `hookRun γ q Pk f Pre Q`, holding the session (round 1, T6: the server's
hook reads the consistent index through `ReadTx()` without `RLock`, `cindex.go:102-110`,
`beSess_rd`); with `nil`, the caller's view shift.

**Changes** (from `specs-ref`'s `plHookAt`): unchanged in shape (mvcc's contract row's). **Margin.**
None.

**Changes** (verify-round: A10-provability B1): the post also gives the session's turn
`beTurn γ` (exclusive), which `Unlock`'s second update takes back: a client parks it with what it
took out at the lock, so that a later session refutes a stale parked state (`beTurn_excl`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`t.LockInsideApply()`**: the batch lock, a session at the batch image, and the post-lock
hook run under it from `Pk ∗ Pre` to `Q`. -/
def batchTxBuffered.LockInsideApply.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (dq : DFrac) (f : GoFunc)
    (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ beHook γ dq f ∗ Pre ∗ hookRun γ q Pk f Pre Q }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"LockInsideApply")) (Val #()))
  {{ RET #(); ∃ I : Image, beSess γ q Fp.none (Sess.init I) ∗ beTurn γ ∗ beLive γ (btLoc γ) 1 ∗ beHook γ dq f ∗ Q }}

end spec

end Backend
end EtcdGrove
end Perennial
