/-
`clientv3.streamKeyFromCtx(ctx)` (`client/v3/watch.go`; names only: grpc's `metadata.FromOutgoingContext` and `fmt.Sprintf` of a map; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.StreamKey
public import Proof.context.WatchCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `streamKeyFromCtx(ctx)`, for a context `ctx` (`isContext`: Go's body calls `ctx.Value`, which
panics on a nil context; until G2, 2026-10-30, the spec took any `ctx`, a latent bug of the trust
base, `notes/audit.md`), returns the key of its outgoing metadata (`streamKeyOf`):
`FromOutgoingContext(ctx)` then `fmt.Sprintf("%+v", ...)` of the map, `""` with none. Since premise
fixes 8 (approved by etcd-grove-81) `watchCtx` carries `metadata.outgoingCtxOkC`: `Value(mdOutgoingKey{})`
returns one value on every call, and a stored `rawMD` is `builtRawMD` (no two keys equal up to case),
which were this spec's margins (`notes/axiom-review/g2-streamkey.md`). -/
abbrev streamKeyFromCtx.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ EtcdGrove.context.watchCtx ctx cd }}
    (App (Val (@! go_etcd_io.etcd.client.v3.streamKeyFromCtx)) (Val #(GoInterface.ok ctx)))
  {{ RET #(streamKeyOf (metadata.outgoingOf (GoInterface.ok ctx))); True }}

end spec

end EtcdGrove
end Perennial
