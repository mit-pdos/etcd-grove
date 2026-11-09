/-
`t.LockInsideApply()` (`batch_tx.go:118-128`): translated; internal (the embedded receiver).
Changes: as `batchTxBuffered.LockInsideApply`. Margin: none.
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

/-- **`t.LockInsideApply()`** on the embedded `batchTx`: as `batchTxBuffered`'s. -/
def batchTx.LockInsideApply.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (dq : DFrac) (f : GoFunc)
    (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ beHook γ dq f ∗ Pre ∗ hookRun γ q Pk f Pre Q }}
    (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"LockInsideApply")) (Val #()))
  {{ RET #(); ∃ I : Image, beSess γ q Fp.none (Sess.init I) ∗ beHook γ dq f ∗ Q }}

end spec

end Backend
end EtcdGrove
end Perennial
