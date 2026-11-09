/-
`(*clientv3.Client).streamClientInterceptor` (`client/v3/retry_interceptor.go`).

Users: `dialSetupOpts` (`withMax(0)`: every stream: watch, lease keep-alive, range stream, snapshot).

Proof sketch: the closure: `withVersion(ctx)`, `getToken` (its spec; an error returned: `siOk_call`'s
error disjunct), `filterCallOptions`, `reuseOrNewWithCallOptions`: the limit `0` (the interceptor's
and no per-call option raises it: `callOptsOk_append`), so the streamer is called once and its
result returned. The retrying stream (`serverStreamingRetryingStream`) is never built.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean`.

Margin: with a limit above `0` the interceptor would wrap the stream (not specified: no caller
asks).
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

/-- `c.streamClientInterceptor(optFuncs...)` with a limit of `0`: the client's stream interceptor
(`siOk`). -/
def Client.streamClientInterceptor.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (sl : GoSlice) (fs : List (RetryOptsM → RetryOptsM)),
  (applyRetry fs RetryOptsM.default).max = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ retryOptsAt sl fs }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"streamClientInterceptor")) (Val #sl))
  {{ (si : val), RET si; siOk si c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
