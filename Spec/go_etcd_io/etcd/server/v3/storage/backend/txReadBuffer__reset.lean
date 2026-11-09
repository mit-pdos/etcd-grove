/-
`txr.reset()` (promoted `txBuffer.reset`): translated; internal. Changes: unchanged. Margin: as
`txBuffer.reset`.
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

/-- **`txr.reset()`**: every bucket's entries gone, the version kept. -/
def txReadBuffer.reset.spec : Prop :=
  ∀ (t : Loc) (R : TxB) (ver : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ trbAt t R ver }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ∃ R' : TxB, trbAt t R' ver ∗ ⌜∀ id, R' id = none ∨ R' id = some []⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
