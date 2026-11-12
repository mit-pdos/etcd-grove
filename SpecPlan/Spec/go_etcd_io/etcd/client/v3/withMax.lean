/-
`clientv3.withMax` (`client/v3/retry_interceptor.go`).

Users: `dialSetupOpts` (`withMax(0)` for streams, the unary limit), `lessor.resetRecv` (`withMax(0)`).

Proof sketch: a `retryOption` whose `applyFunc` closure writes the field (`retryOptAt`'s intended
realization: the closure's triple on an `*options` modelled by `o`).

Changes: from `specs-ref`.

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

/-- `withMax(...)`: its retry option. -/
def withMax.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withMax)) (Val #n))
  {{ (v : go_etcd_io.etcd.client.v3.retryOption), RET #v; maxOptAt v n }}

end spec

end ClientV3
end EtcdGrove
end Perennial
