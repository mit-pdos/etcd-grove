/-
`(*clientv3.watchGRPCStream).addSubstream(resp, ws)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.addSubstream(resp, ws)` for a created response (its id, canceled flag and reason read):
if it refuses the response (`addFails`: the invalid id, or canceled with a reason), the stream's
`closeErr` becomes `rpctypes.Error` of the reason (an error grpc's `status` accepts) and the
substream's `recvc` is closed (its producer's side, given); otherwise the substream gets the id and
is registered under it in `substreams`. -/
abbrev watchGRPCStream.addSubstream.spec : Prop :=
  ∀ (V : WEnv GF) (wgs resp ws : Loc) (id : w64) (ca : Bool) (rs : GoString) (dq dq' : DFrac)
    (wid0 : w64) (m : Loc) (M : GMap w64 Loc) (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ watchConnFacts V ∗
      structFieldRef etcdserverpb.WatchResponse go!"WatchId" resp ↦{dq} id ∗
      structFieldRef etcdserverpb.WatchResponse go!"Canceled" resp ↦{dq} ca ∗
      structFieldRef etcdserverpb.WatchResponse go!"CancelReason" resp ↦{dq} rs ∗
      wsF ws go!"id" ↦ wid0 ∗ wgsF wgs go!"substreams" ↦{dq'} m ∗ ownMap m (DFrac.own 1) M ∗
      wgsF wgs go!"closeErr" ↦ e ∗ (⌜addFails id ca rs⌝ -∗ recvcCloser V ws) }}
    (App (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"addSubstream")) (Val #resp)) (Val #ws))
  {{ RET #(); structFieldRef etcdserverpb.WatchResponse go!"WatchId" resp ↦{dq} id ∗
      structFieldRef etcdserverpb.WatchResponse go!"Canceled" resp ↦{dq} ca ∗
      structFieldRef etcdserverpb.WatchResponse go!"CancelReason" resp ↦{dq} rs ∗
      wgsF wgs go!"substreams" ↦{dq'} m ∗
      (if decide (addFails id ca rs) then
        iprop(wsF ws go!"id" ↦ wid0 ∗ ownMap m (DFrac.own 1) M ∗
          ∃ e' : GoInterface, wgsF wgs go!"closeErr" ↦ e' ∗ statusErrOk e')
      else
        iprop(wsF ws go!"id" ↦ id ∗ ownMap m (DFrac.own 1) (<[id := ws]> M) ∗
          wgsF wgs go!"closeErr" ↦ e)) }}

end spec

end EtcdGrove
end Perennial
