/-
`(*clientv3.retryLeaseClient).LeaseKeepAlive` (`client/v3/retry.go`).

Users: `lessor.resetRecv`, `lessor.keepAliveOnce` (through `remoteLeaseAt_keepAlive`).

Proof sketch: appends `withRepeatablePolicy()` and opens the stream with the stub (through the stream
interceptor: `siOk_call`, whose token fetch may fail first), 2a's stream spec giving the halves.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryLeaseClient__LeaseKeepAlive.lean`:
restated over the stream halves.

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

/-- `r.LeaseKeepAlive(ctx, opts...)`: the keep-alive stream's halves, or an error. -/
def retryLeaseClient.LeaseKeepAlive.spec : Prop :=
  ∀ (r c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (p : Principal) (opts : GoSlice)
    (rep : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryLeaseHandle r c γ who ∗ clientReady c ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗
      callOptsOk opts rep }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty @!!
      go!"LeaseKeepAlive")) (Val #ctx)) (Val #opts))
  {{ (sc err : GoInterface), RET (PairV #sc #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ g, kaSendAt sc g [] ∗ kaRecvAt sc g) ∨
      (⌜sc = GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
