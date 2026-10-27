/-
`(*clientv3.watcher).closeStream(wgs)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.closeStream(wgs)` (by `run`, once, its close error published): closes the stream's `donec`,
cancels its context and removes its key from the streams map (unless the watcher is closed). -/
abbrev watcher.closeStream.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClientWatcher V G.w ∗
      isWGS V G callSl ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending ∗
      closeErrPub G.wgs }}
    (App (Val (G.w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"closeStream")) (Val #G.wgs))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
