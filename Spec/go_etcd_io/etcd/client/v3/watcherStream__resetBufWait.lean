/-
`(*clientv3.watcherStream).resetBufWait()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `ws.resetBufWait()`: the buffer's wait start time zero. -/
abbrev watcherStream.resetBufWait.spec : Prop :=
  ∀ (ws : Loc) (t : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wsF ws go!"bufWaitStartTime" ↦ t }}
    (App (Val (ws @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcherStream.ty @!! go!"resetBufWait")) (Val #()))
  {{ RET #(); wsF ws go!"bufWaitStartTime" ↦ (zero_val _root_.Perennial.time.Time) }}

end spec

end EtcdGrove
end Perennial
