/-
`bb.Len()` (`tx_buffer.go:238`): translated; internal (`sort.Interface`). Changes: unchanged.
Margin: none.
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

/-- **`bb.Len()`**: the used count. -/
def bucketBuffer.Len.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l w }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"Len")) (Val #()))
  {{ (n : w64), RET #n; bbAt bb l w ∗ ⌜sint.nat n = l.length⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
