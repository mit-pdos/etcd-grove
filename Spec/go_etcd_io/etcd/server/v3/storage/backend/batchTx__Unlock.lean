/-
`t.Unlock()` (`batch_tx.go:135-140`): translated; internal (the end of `batchTxBuffered.Unlock`,
which committed what it must, so nothing is pending: the `pending ≥ batchLimit` commit finds
nothing). The mutex released with its content. Changes: over `btHeld`. Margin: none.
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

/-- **`t.Unlock()`** on the embedded `batchTx`, nothing pending: the mutex released. -/
def batchTx.Unlock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (d : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗ Pk ∗ btPhys γ I 0 d }}
    (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); True }}

end spec

end Backend
end EtcdGrove
end Perennial
