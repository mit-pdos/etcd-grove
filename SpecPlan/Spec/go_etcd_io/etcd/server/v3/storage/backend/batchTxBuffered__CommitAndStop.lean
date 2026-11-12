/-
`t.CommitAndStop()` (`batch_tx.go:369-373`): translated; internal (the run loop's last act, in
`Close`). `lock()`, `commit(true)`, `Unlock()`. Changes: over `btStopped`. Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

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

/-- **`t.CommitAndStop()`**: the final commit, no write transaction left. -/
def batchTxBuffered.CommitAndStop.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beRun γ }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"CommitAndStop")) (Val #()))
  {{ RET #(); btStopped γ ∗ ∃ I : Image, beCommitted γ I }}

end spec

end Backend
end EtcdGrove
end Perennial
