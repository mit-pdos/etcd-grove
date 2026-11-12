/-
`clientv3.backoffLinearWithJitter` (`client/v3/retry_interceptor.go`).

Users: `defaultOptions` (the package's initial globals).

Proof sketch: a closure over `jitterUp` (W0's spec).

Changes: new (no old spec).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `backoffLinearWithJitter(w, j)`: a backoff function. -/
def backoffLinearWithJitter.spec : Prop :=
  ∀ (w j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.backoffLinearWithJitter)) (Val #w)) (Val #j))
  {{ (f : GoFunc), RET #f; backoffOk f }}

end spec

end ClientV3
end EtcdGrove
end Perennial
