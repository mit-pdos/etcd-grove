/-
`(*clientv3.watcher).RequestProgress(ctx)` (`client/v3/watch.go`; unit K2e-9). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

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

/-- **`w.RequestProgress(ctx)`**: asks the gRPC stream of `ctx` for a progress notification (a
`*progressRequest` on its `reqc`, which `run` forwards to the server; `reqP`), with no logical
effect for the caller; returns `nil`, `ctx`'s error, the stream's close error or `errors.New`'s,
each one grpc's `status` accepts. -/
abbrev watcher.RequestProgress.spec : Prop :=
  ∀ (V : WEnv GF) (w : Loc) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ∗
      context.isContext ctx cs }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"RequestProgress")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; statusErrOk err }}

end spec

end EtcdGrove
end Perennial
