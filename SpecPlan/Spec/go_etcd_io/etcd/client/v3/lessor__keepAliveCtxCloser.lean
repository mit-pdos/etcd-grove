/-
`(*clientv3.lessor).keepAliveCtxCloser` (`client/v3/lease.go`).

Users: `KeepAlive` (a goroutine per call whose context can be done).

Proof sketch: a `select` on the entry's `donec`, the lessor's `donec`, `ctx.Done()` (each a channel
whose receive is safe: `kaDonec`, the lessor's invariant, `ctxOk`); then under `l.mu`: if the lease's
current entry holds this call's context (compared by the `keepAliveCtxKey` value, unique per
`KeepAlive` call), closes its channel (the close token the entry holds: never closed twice, since
every closer removes the channel from the entry under `l.mu`) and removes it; drops an empty entry.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__keepAliveCtxCloser.lean`: restated
over `lessorHandle`.

verify-round: the comparison `c.Value(keepAliveCtxKey{}) == ctx.Value(keepAliveCtxKey{})` by
`Context.Value.spec` on both contexts, each a `WithValue` context of `KeepAlive` recorded by
`ctxValueIs` at that key (its value `&ctx`, a pointer: comparable, so the `==` cannot panic; the
same pointer exactly when it is this call's context): A1-completeness F5, the callee spec was missing.

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

/-- `l.keepAliveCtxCloser(ctx, id, donec)`: closes this call's channel once `ctx` is done (unless
the entry or the lessor is done first). -/
def lessor.keepAliveCtxCloser.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (id : w64) (donec : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ Context.ctxOk ctx ∗ kaDonec donec }}
    (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"keepAliveCtxCloser")) (Val #ctx)) (Val #id)) (Val #donec))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
