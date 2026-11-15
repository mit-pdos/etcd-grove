/-
`clientv3.withRepeatablePolicy` (`client/v3/retry_interceptor.go`).

Users: `retry.go`'s wrappers of the repeatable RPCs (`Range`, the lease, list and alarm RPCs).

Proof sketch: a `retryOption` whose `applyFunc` closure writes the field (`retryOptAt`'s intended
realization: the closure's triple on an `*options` modelled by `o`).

Changes: new (no old spec; W0 asked for it).

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

/-- `withRepeatablePolicy(...)`: its retry option. -/
def withRepeatablePolicy.spec : Prop :=
  ∀ (_u : Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withRepeatablePolicy)) (Val #()))
  {{ (v : go_etcd_io.etcd.client.v3.retryOption), RET #v; repOptAt v }}

end spec

end ClientV3
end EtcdGrove
end Perennial
