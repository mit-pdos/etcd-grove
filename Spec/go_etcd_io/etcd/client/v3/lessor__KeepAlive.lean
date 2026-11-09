/-
`(*clientv3.lessor).KeepAlive` (`client/v3/lease.go`).

Users: `concurrency.NewSession` (`session.go:58`: `for range keepAlive`, then `close(donec)`),
leasing and recipes through sessions; snippet `clientv3lease/session.go` (`ReqSessionLifecycle`,
`ReqKeepAliveValues`).

Proof sketch: a fresh channel of capacity `LeaseResponseChSize` (the package variable: `init.spec`'s
value 16 is not needed, any capacity); under `l.mu` (the lessor's invariant): if `donec` is closed,
closes the channel (its close token is fresh) and returns it with `ErrKeepAliveHalted`; else adds the
channel (its `kaChan` invariant allocated, its close token into the entry) and `ctx` (wrapped by
`context.WithValue` when `ctx.Done() != nil`: W0's context API) to the lease's entry (a new one, its
`donec` fresh, if none); then the context closer goroutine (`keepAliveCtxCloser`) if the context can
be done, and the first time (`firstKeepAliveOnce`) the receive and deadline loops.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__KeepAlive.lean` (an `isChanAny`
channel, any error): the channel's values (`kaChan`: about `id`, positive TTL, read-only), no server
fact needed (the old spec took the keep-alive stream's address facts).

Margin: the error's value (`ErrKeepAliveHalted{loopErr}`) and that the channel is closed then are
not stated (no user reads them); that the channel closes once the lease is lost or `ctx` is done is
liveness.
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

/-- `l.KeepAlive(ctx, id)`: a keep-alive channel of lease `id` (`kaChan`), and `nil` or a halted
error (the channel then closed). -/
def lessor.KeepAlive.spec : Prop :=
  ∀ (l : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who ∗ Context.ctxOk ctx }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"KeepAlive")) (Val #ctx)) (Val #id))
  {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err); ⌜ch ≠ null⌝ ∗ kaChan ch id }}

end spec

end ClientV3
end EtcdGrove
end Perennial
