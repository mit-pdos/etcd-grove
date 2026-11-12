/-
## `(*backend).SetTxPostLockInsideApplyHook(hook)` (`backend.go:270-277`): translated

**Users.** `NewServer` (`server.go:409`), 2d's `applySnapshot` (`server.go:1098`, the new backend),
each with the server's `getTxPostLockInsideApplyHook()`.

**Proof sketch.** `b.batchTx.lock()` (the batch lock: `Pk`, an empty session); the hook field
written (its authority, in the lock's invariant, with the full share); `b.batchTx.Unlock()`
(`batchTxBuffered.Unlock.spec` with nothing to publish).

**Changes** (from `specs-ref`'s): over `beHook`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`b.SetTxPostLockInsideApplyHook(f)`**: the post-lock hook is `f`. -/
def backend.SetTxPostLockInsideApplyHook.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (f0 f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ beHook γ (DFrac.own 1) f0 }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"SetTxPostLockInsideApplyHook")) (Val #f))
  {{ RET #(); beOpen γ q ∗ beHook γ (DFrac.own 1) f }}

end spec

end Backend
end EtcdGrove
end Perennial
