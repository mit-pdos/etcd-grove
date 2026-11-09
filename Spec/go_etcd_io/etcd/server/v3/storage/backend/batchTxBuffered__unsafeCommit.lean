/-
`t.unsafeCommit(stop)` (`batch_tx.go:381-404`): translated; internal (under the batch mutex and
`readTx.Lock`). The hooks (`hookOk`); the old read transaction handed to a rollback goroutine (it
waits for the interval's wait group, then rolls back; a thread from `envOk`'s pool) and the read
side reset; `batchTx.commit`; `pendingDeleteOperations := 0`; unless stopping, a new read
transaction. The published updates (the session's second, the hooks') fire at bbolt's commit update (the outer update of 4c's nested `commitAU`; the
settling update follows when the commit ends).
Changes: over `btPhys`. Margin: none.
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

/-- **`t.unsafeCommit(stop)`**: the hooks, then the commit of the batch image. -/
def batchTxBuffered.unsafeCommit.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (n d : Nat) (stop : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗ rtHeld γ ∗ Pk ∗ btPhys γ I n d }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"unsafeCommit")) (Val #stop))
  {{ RET #(); btHeld γ ∗ rtHeld γ ∗ Pk ∗ ∃ I' : Image, beCommitted γ I' ∗
      (if stop then btStopped γ else btPhys γ I' 0 0) }}

end spec

end Backend
end EtcdGrove
end Perennial
