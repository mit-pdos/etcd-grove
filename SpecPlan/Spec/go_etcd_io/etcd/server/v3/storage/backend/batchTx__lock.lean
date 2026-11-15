/-
`t.lock()` (`batch_tx.go:114-116`): translated; internal. The mutex: its content (`Pk`, the
physical session). Changes: over `btHeld`. Margin: none.
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

/-- **`t.lock()`**: the batch mutex, `Pk`, bbolt's write transaction. -/
def batchTx.lock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk }}
    (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"lock")) (Val #()))
  {{ RET #(); btHeld γ ∗ Pk ∗ ((∃ I n d, btPhys γ I n d) ∨ btStopped γ) }}

end spec

end Backend
end EtcdGrove
end Perennial
