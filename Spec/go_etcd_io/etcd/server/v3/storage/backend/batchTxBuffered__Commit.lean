/-
## `(*batchTxBuffered).Commit()` (`batch_tx.go:363-367`): translated

**Users.** `backend.ForceCommit`, `backend.Snapshot`, the run loop (`backend.go:472`),
`newBatchTxBuffered`. **Proof sketch.** `t.lock()` (`Pk`, a session), `commit(false)`
(`batchTxBuffered.commit.spec`: the hooks, the client's commit step, then the caller's per-call
step with the committed image), `t.Unlock()` (nothing to publish). **Changes.** As `ForceCommit`.
**Margin.** As `ForceCommit`.
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

/-- **`t.Commit()`**: the batch committed, the caller's per-call step at it. -/
def batchTxBuffered.Commit.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ X ∗ beReq γ Pk X Y }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"Commit")) (Val #()))
  {{ RET #(); beOpen γ q ∗ Y }}

end spec

end Backend
end EtcdGrove
end Perennial
