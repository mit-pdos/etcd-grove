/-
`bb.Swap(i, j)` (`tx_buffer.go:242`): translated; internal (`sort.Interface`). Changes: unchanged.
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

/-- **`bb.Swap(i, j)`**: entries `i` and `j` exchanged. -/
def bucketBuffer.Swap.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (i j : w64) (x y : GoString × GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l ∗ ⌜l[sint.nat i]? = some x ∧ l[sint.nat j]? = some y ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ }}
    (App (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); bbAt bb ((l.set (sint.nat i) y).set (sint.nat j) x) }}

end spec

end Backend
end EtcdGrove
end Perennial
