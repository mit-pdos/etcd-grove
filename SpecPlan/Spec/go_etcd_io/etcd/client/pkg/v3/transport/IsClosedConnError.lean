/-
`transport.IsClosedConnError` (`client/pkg/v3/transport/listener_tls.go`).

Users: the server's listeners (2e, 2f).

Proof sketch: `err.Error()` (`errStrOk`), `strings.Contains`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/transport/IsClosedConnError.lean`.

Margin: the result is not described.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.pkg.v3.transport.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Transport

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.transport.Assumptions]

/-- `IsClosedConnError(err)`: no panic. -/
def IsClosedConnError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport ∗ errStrOk err }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.transport.IsClosedConnError)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end Transport
end EtcdGrove
end Perennial
