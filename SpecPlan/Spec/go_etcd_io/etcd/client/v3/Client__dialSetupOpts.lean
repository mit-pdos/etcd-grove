/-
`(*clientv3.Client).dialSetupOpts` (`client/v3/client.go`).

Users: `dial`.

Proof sketch: keepalive parameters (grpc's `WithKeepaliveParams`), the caller's options, the
transport credentials (or `insecure.NewCredentials()`), the retry limits and backoff from the
configuration (`roundRobinQuorumBackoff`, `withBackoff`, `withMax`), the interceptors
(`streamClientInterceptor(withMax(0), backoff)`, `unaryClientInterceptor(withMax(n), backoff)`: their
specs, `siOk`, `uiOk`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__dialSetupOpts.lean`: over `clientPre`.

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

/-- `c.dialSetupOpts(creds, dopts...)`: the client's dial options. -/
def Client.dialSetupOpts.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (creds : GoInterface) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ transportCredsOk creds ∗ dialTargetOk sl γ }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialSetupOpts")) (Val #creds)) (Val #sl))
  {{ (opts : GoSlice), RET #opts; clientDialOpts opts c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
