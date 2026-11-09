/-
`clientv3.NewAuthFromAuthClient` (`client/v3`).

Users: no user in scope (the gRPC proxy, tests).

Proof sketch: the given remote; a client's `callOpts` (or none: `callOptsOk_nil`).

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

/-- `NewAuthFromAuthClient(remote, c)`: a `*authClient` over `remote`. -/
def NewAuthFromAuthClient.spec : Prop :=
  ∀ (remote : GoInterface) (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ remoteAuthAt remote γ who ∗ (⌜c = null⌝ ∨ clientCore c γ who) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewAuthFromAuthClient)) (Val #remote)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ a : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #a⌝ ∗ authHandle a γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
