/-
`(*clientv3.lessor).keepAliveCtxCloser(ctx, id, donec)` (`client/v3/lease.go`; item 1, the client
lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.keepAliveCtxCloser(ctx, id, donec)` on a lessor (`lessorAt`), for a context and a
keep-alive's `donec`: once `ctx` is done (unless `donec` or the lessor's `donec` is closed first),
under the lock, closes and removes the channel of the lease `id`'s keep-alive whose context is
`ctx`'s (by their values at `keepAliveCtxKey{}`), removing the keep-alive if it has no channel
left; it returns. It keeps the lock invariant's alignment (`kaPaired`: it removes the same index
from `chs` and `ctxs`), so the channel it closes is the one registered with the context it found.
That this context is `ctx` (and so the channel `KeepAlive` returned for `ctx`) is not stated:
`Value`'s trust-boundary spec (`context.ValueKeepAlive`) says only that it returns `nil` or some
pointer, not `WithValue`'s `&ctx`. -/
abbrev lessor.keepAliveCtxCloser.spec : Prop :=
  ∀ (l : Loc) (addr : GoString) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64) (kd : GoChan) (γkd : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l addr ∗
      context.isContext ctx cd ∗ ownBroadcastChan kd γkd iprop(True) .Unknown }}
    (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"keepAliveCtxCloser"))
      (Val #(GoInterface.ok ctx))) (Val #id)) (Val #kd))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
