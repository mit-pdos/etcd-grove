/-
`isNil(msg)` (`util.go`), internal (the warnings): `msg == nil || reflect.ValueOf(msg).IsNil()`
(reflect's names-only `ValueOf`/`IsNil`: trust boundary, a pointer's nil test). Old spec: same.
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

open Classical in
/-- `isNil(msg)` of a `proto.Message`: `nil`, or a `nil` pointer. -/
def isNil.spec : Prop :=
  ∀ (msg : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜msg = GoInterface.nil ∨ ∃ (t : go.GoType) (p : Loc), msg = Proto.msgVal t p⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.isNil)) (Val #msg))
  {{ RET #(decide (msg = GoInterface.nil ∨ ∃ t : go.GoType, msg = Proto.msgVal t null)); True }}

end spec
end Txn
end EtcdGrove
end Perennial
