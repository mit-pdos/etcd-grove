/-
`endpoint.Interpret` (`client/v3/internal/endpoint/endpoint.go`).

Users: the resolver (`EtcdManualResolver.state`: each endpoint's address and server name).

Proof sketch: `translateEndpoint` (as `RequiresCredentials`).

Changes: new (no old spec).

Margin: the address is not described (what it dials is 2a's: `dialTargetOk`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.internal.endpoint
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.internal.endpoint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Endpoint

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Interpret(ep)`: no panic. -/
def Interpret.spec : Prop :=
  ∀ (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint }}
    (App (Val (@! go_etcd_io.etcd.client.v3.internal.endpoint.Interpret)) (Val #ep))
  {{ (a s : GoString), RET (PairV #a #s); True }}

end spec

end Endpoint
end EtcdGrove
end Perennial
