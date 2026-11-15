/-
`rt.reset()` (`read_tx.go:134-139`): translated; internal (under `readTx.Lock`, in `unsafeCommit`).
The read buffer emptied, a fresh bucket cache and wait group, no transaction. Changes: over
`rtHeld`. Margin: none.
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

/-- **`rt.reset()`**: the read side emptied. -/
def readTx.reset.spec : Prop :=
  ∀ (γ : BeNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rtHeld γ }}
    (App (Val ((rtLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty @!! go!"reset")) (Val #()))
  {{ RET #(); rtHeld γ }}

end spec

end Backend
end EtcdGrove
end Perennial
