/-
`(*clientv3.watchGRPCStream).startBufWait(ws)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.startBufWait(ws)`: with a logger and a buffer logger, notes the time the buffer's head
started waiting (unless it already did). -/
abbrev watchGRPCStream.startBufWait.spec : Prop :=
  ∀ (wgs ws : Loc) (lg bl : Loc) (dq : DFrac) (t : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsF wgs go!"lg" ↦□ lg ∗
      wsF ws go!"bufLogger" ↦{dq} bl ∗ bufLogOk ws bl ∗ wsF ws go!"bufWaitStartTime" ↦ t }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"startBufWait")) (Val #ws))
  {{ RET #(); wsF ws go!"bufLogger" ↦{dq} bl ∗
      ∃ t' : _root_.Perennial.time.Time, wsF ws go!"bufWaitStartTime" ↦ t' }}

end spec

end EtcdGrove
end Perennial
