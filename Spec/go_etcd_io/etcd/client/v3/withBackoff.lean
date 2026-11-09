/-
`clientv3.withBackoff` (`client/v3/retry_interceptor.go`).

Users: `dialSetupOpts`.

Proof sketch: a `retryOption` whose closure stores the function (`backoffOk`).

Changes: new (no old spec).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `withBackoff(f)`: its retry option. -/
def withBackoff.spec : Prop :=
  ∀ (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ backoffOk f }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withBackoff)) (Val #f))
  {{ (v : go_etcd_io.etcd.client.v3.retryOption), RET #v; backoffOptAt v }}

end spec

end ClientV3
end EtcdGrove
end Perennial
