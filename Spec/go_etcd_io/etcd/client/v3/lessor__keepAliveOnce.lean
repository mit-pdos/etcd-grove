/-
`(*clientv3.lessor).keepAliveOnce` (`client/v3/lease.go`).

Users: `KeepAliveOnce`.

Proof sketch: a cancellable child context (Perennial's `WithCancel`; `ctxOk`), `l.remote.LeaseKeepAlive`
(`remoteLeaseAt_keepAlive`: the two halves, or an error), `Send` of one request
(`kaSendAt_send`: `kaSendAt sc [id]`), `Recv` (`kaRecvAt_recv`: a fresh message with `kaSent sc
id'`; `kaSent_sent` against `kaSendAt sc [id]` gives `id' = id`: the stream carries one request), the
deferred `CloseSend` (an error replaces a `nil` result with `ContextError`'s), the deferred cancel.

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

/-- `l.keepAliveOnce(ctx, id)`: one response about `id` (owned), or an error. -/
def lessor.keepAliveOnce.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (p : Principal) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"keepAliveOnce")) (Val #ctx)) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ ttl, kaRespOwn resp id ttl) ∨
      (⌜resp = null⌝ ∗ ∃ k, callErr err k) ∨
      (∃ ttl, kaRespOwn resp id ttl ∗ ∃ k, callErr err k) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
