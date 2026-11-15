/-
`t.commit(stop)` (`batch_tx.go:282-305`): translated; internal (under the batch mutex and
`readTx.Lock`, after the hooks). Nothing pending and not stopping: nothing. Else bbolt's `Commit`
(4c's `Tx.Commit` over its nested `commitAU`, built from the whole `boltState` the batch lock's
invariant holds (`boltState_commit_au`): the commit update, at the meta page write, is where the
client's commit step `commitOk` (from `isBackend`) and the published updates fire; its commit gives
the settling update, fired when the commit ends (synced, or a failure); an error is `lg.Fatal`), the metrics, `pending := 0`; unless stopping, a new write transaction
(`begin(true)`). Changes: over `btPhys`. Margin: none.
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

/-- **`t.commit(stop)`**: the write transaction's image committed (`beCommitted`); a new one
begun unless stopping. -/
def batchTx.commit.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (n d : Nat) (stop : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗ rtHeld γ ∗ Pk ∗ btPhys γ I n d }}
    (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"commit")) (Val #stop))
  {{ RET #(); btHeld γ ∗ rtHeld γ ∗ Pk ∗ beCommitted γ I ∗
      (if stop then btStopped γ else btPhys γ I 0 d) }}

end spec

end Backend
end EtcdGrove
end Perennial
