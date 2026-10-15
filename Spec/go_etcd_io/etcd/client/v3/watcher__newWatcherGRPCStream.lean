/-
`(*clientv3.watcher).newWatcherGRPCStream(inctx)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.newWatcherGRPCStream(inctx)` (a model context): a new gRPC watch stream of `w` (`isWGS`,
over the watcher's call options), its context `WithCancel(&valCtx{inctx})`, its key some string,
its channels made, with its `run` started. -/
abbrev watcher.newWatcherGRPCStream.spec : Prop :=
  ∀ (V : WEnv GF) (w : Loc) (inctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ∗ context.isContext inctx cs }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"newWatcherGRPCStream")) (Val #(GoInterface.ok inctx)))
  {{ (wgs : Loc), RET #wgs; ∃ (G : WgsPrm GF) (callSl : GoSlice),
      ⌜G.wgs = wgs ∧ G.w = w⌝ ∗ watcherF w go!"callOpts" ↦□ callSl ∗ isWGS V G callSl }}

end spec

end EtcdGrove
end Perennial
