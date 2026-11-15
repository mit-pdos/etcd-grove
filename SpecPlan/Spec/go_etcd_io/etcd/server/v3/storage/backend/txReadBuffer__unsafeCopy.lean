/-
`txr.unsafeCopy()` (`tx_buffer.go:141-153`): translated; internal (under `readTx.RLock`). A fresh
buffer of each bucket's used entries (`CopyUsed`), version `0`. Changes: `envOk`. Margin: none.
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

/-- **`txr.unsafeCopy()`**: a fresh copy, at version `0`. -/
def txReadBuffer.unsafeCopy.spec : Prop :=
  ∀ (t : Loc) (R : TxB) (ver : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk ∗ trbAt t R ver }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer.ty @!! go!"unsafeCopy")) (Val #()))
  {{ (c : go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer), RET #c; trbAt t R ver ∗
      ∀ l : Loc, l ↦ c -∗ trbAt l R (W64 0) }}

end spec

end Backend
end EtcdGrove
end Perennial
