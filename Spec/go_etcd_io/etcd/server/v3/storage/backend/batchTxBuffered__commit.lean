/-
`t.commit(stop)` (`batch_tx.go:375-379`): translated; internal. `readTx.Lock()`, `unsafeCommit`,
`readTx.Unlock()`. Changes: over `btPhys`. Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

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

/-- **`t.commit(stop)`** on the batch transaction: `unsafeCommit` under `readTx.Lock`. -/
def batchTxBuffered.commit.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (n d : Nat) (stop : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗ Pk ∗ btPhys γ I n d }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"commit")) (Val #stop))
  {{ RET #(); btHeld γ ∗ Pk ∗ ∃ I' : Image, beCommitted γ I' ∗
      (if stop then btStopped γ else btPhys γ I' 0 0) }}

end spec

end Backend
end EtcdGrove
end Perennial
