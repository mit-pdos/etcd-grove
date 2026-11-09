/-
`(*kvSort).Swap(i, j)` (`range.go`), internal (the sorters' `Swap`, through `sort.Sort`): mirrors the
code. Old spec: same.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `s.Swap(i, j)`: the `i`-th and `j`-th pointers exchanged. -/
def kvSort.Swap.spec : Prop :=
  ∀ (s : Loc) (sl : GoSlice) (ps : List Loc) (i j : w64) (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ s.[go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort, go!"kvs"] ↦□ sl ∗ sl ↦* ps ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ps[sint.nat i]? = some a ∧ ps[sint.nat j]? = some b⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* ((ps.set (sint.nat i) b).set (sint.nat j) a) }}

end spec
end Txn
end EtcdGrove
end Perennial
