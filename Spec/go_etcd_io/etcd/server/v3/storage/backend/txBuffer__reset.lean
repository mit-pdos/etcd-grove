/-
`txb.reset()` (`tx_buffer.go:32-40`): translated; internal. Every bucket buffer emptied; one
already empty removed. Changes: over `txbAt`. Margin: which empty buckets stay.
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

/-- **`txb.reset()`**: every bucket's entries gone. -/
def txBuffer.reset.spec : Prop :=
  ∀ (t : Loc) (B : TxB),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ txbAt t B }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txBuffer.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ∃ B' : TxB, txbAt t B' ∗ ⌜∀ id, B' id = none ∨ B' id = some []⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
