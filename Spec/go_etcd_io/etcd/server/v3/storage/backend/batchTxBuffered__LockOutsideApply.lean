/-
## `(*batchTxBuffered).LockOutsideApply()` (promoted `batchTx.LockOutsideApply`, `batch_tx.go:130-133`): translated

**Users.** mvcc's compaction batches and `NewStore` (`kvstore_compaction.go:56`, `kvstore.go:121`),
the lessor's recovery (`lessor.go:811`), the schema's writers outside an apply (4b:
`schema.go:54`, `auth.go:52`, `alarm.go:47`, `membership.go:67, 127, 173`, `migration.go:54`,
`cindex.go:31`), the consistent index (`cindex.go:175`), `VerifyBackendConsistency`. Snippet
`parts.go`.

**Proof sketch.** `ValidateCalledOutSideApply` (a no-op: `envOk`'s `ETCD_VERIFY` unset);
`t.lock()`: the batch mutex's invariant gives the session authority at the batch image `I` (with
the visible image equal to it: the last `Unlock` wrote back and committed every delete) and `Pk`.
The open share goes into the session.

**Changes** (from `specs-ref`'s, over `batchLocked`/`W`): a session at the batch image, no
footprint yet (it widens as the session publishes). **Margin.** None.

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

/-- **`t.LockOutsideApply()`**: the batch lock, a session at the batch image, and `Pk`. -/
def batchTxBuffered.LockOutsideApply.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"LockOutsideApply")) (Val #()))
  {{ RET #(); ∃ I : Image, beSess γ q Fp.none (Sess.init I) ∗ beTurn γ ∗ beLive γ (btLoc γ) 1 ∗ Pk }}

end spec

end Backend
end EtcdGrove
end Perennial
