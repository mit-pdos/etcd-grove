/-
`compareInt64(a, b)` (`txn.go`), internal (`compareKV`): mirrors the code. Old spec: same.
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

/-- `compareInt64(a, b)`: `-1`, `0` or `1` by the signed order. -/
def compareInt64.spec : Prop :=
  ∀ (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.compareInt64)) (Val #a)) (Val #b))
  {{ RET #(W64 (if sint.Z a < sint.Z b then -1 else if sint.Z b < sint.Z a then 1 else 0)); True }}

end spec
end Txn
end EtcdGrove
end Perennial
