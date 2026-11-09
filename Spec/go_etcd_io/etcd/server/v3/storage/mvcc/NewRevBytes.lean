/-
`NewRevBytes()` (`revision.go:79`): a fresh slice of 17 zero bytes, capacity 18. Internal.
**Changes**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `NewRevBytes()`. -/
def NewRevBytes.spec : Prop :=
  {{ pkgInit }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes)) (Val #()))
  {{ (s : GoSlice), RET #s; s ↦* List.replicate 17 (W8 0) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      ⌜s.cap = W64 18⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
