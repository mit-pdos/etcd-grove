/-
`(*kvSort).Len()` (`range.go`), internal: mirrors the code. Old spec: same.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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

/-- `s.Len()`: the slice's length. -/
def kvSort.Len.spec : Prop :=
  ∀ (s : Loc) (sl : GoSlice) (dq : DFrac) (ps : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ s.[go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort, go!"kvs"] ↦□ sl ∗ sl ↦*{dq} ps }}
    (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort.ty @!! go!"Len"))
  {{ RET #(W64 ps.length); sl ↦*{dq} ps }}

end spec
end Txn
end EtcdGrove
end Perennial
