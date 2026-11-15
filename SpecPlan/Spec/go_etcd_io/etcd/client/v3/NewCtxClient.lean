/-
`clientv3.NewCtxClient` (`client/v3/client.go`).

Users: `v3client.New` (`server/etcdserver/api/v3client/v3client.go`: the in-process client of
v3lock and v3election, `NewCtxClient(ctx, WithZapLogger(lg))` then each field set by a
`New*From*Client` over an adapter); snippet `clientv3client/inproc.go` (`ReqInProcClient`).

Proof sketch: a cancellable child of `ctx` (Perennial's `WithCancel`: `ctxOk`, `ctxPrin_child`), a
fresh `RWMutex`, each option applied (`clientOptAt`: stores a logger), then `zap.NewNop()` if none
(W0's zap: `isLogger`). The six interface fields `nil`, given to the caller; no connection.

Changes: new (round 1: the completeness review's F3; it was left out).

Margin: the client's default principal is none (no credentials); each call's principal is its
context's (`ctxPrin none ctx p`: a forwarded token's user, `ctxPrin_token`).
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

/-- `NewCtxClient(ctx, opts...)`: a bare client (`clientBase`, its six interface fields `nil`). -/
def NewCtxClient.spec : Prop :=
  ∀ (ctx : GoInterface) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx ∗ ctxPrin none ctx none ∗
      (∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f ∈ fs, clientOptAt f) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewCtxClient)) (Val #ctx)) (Val #sl))
  {{ (c : Loc), RET #c; clientBare c none ∗
      c.[go_etcd_io.etcd.client.v3.Client, go!"KV"] ↦ GoInterface.nil ∗
      c.[go_etcd_io.etcd.client.v3.Client, go!"Watcher"] ↦ GoInterface.nil ∗
      c.[go_etcd_io.etcd.client.v3.Client, go!"Lease"] ↦ GoInterface.nil ∗
      c.[go_etcd_io.etcd.client.v3.Client, go!"Auth"] ↦ GoInterface.nil ∗
      c.[go_etcd_io.etcd.client.v3.Client, go!"Cluster"] ↦ GoInterface.nil ∗
      c.[go_etcd_io.etcd.client.v3.Client, go!"Maintenance"] ↦ GoInterface.nil }}

end spec

end ClientV3
end EtcdGrove
end Perennial
