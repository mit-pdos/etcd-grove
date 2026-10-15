/-
`(*clientv3.watchGRPCStream).closeSubstream(ws)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.closeSubstream(ws)` of a substream that stopped (`closingc`'s message: the producer's side
of its `outc`, its `retc` field), with its `id` and the stream's `closeErr` (an error grpc's
`status` accepts): sends the substream's channel on its `retc` if it can (with the caller's
resources, if it never sent it), publishes a canceled response with the close error before closing
`outc` (in a goroutine, if there is a close error and the watch's context is not done) or closes
it; then unregisters the substream: from `substreams` if it has an id, otherwise its first place
in `resuming` set to nil. -/
abbrev watchGRPCStream.closeSubstream.spec : Prop :=
  ∀ (V : WEnv GF) (wgs ws : Loc) (id : w64) (e : GoInterface) (dq1 dq2 dq3 : DFrac) (m : Loc)
    (M : GMap w64 Loc) (s : GoSlice) (l : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ closingP V ws ∗
      wsF ws go!"id" ↦ id ∗ wgsF wgs go!"closeErr" ↦{dq1} e ∗ statusErrOk e ∗
      wgsF wgs go!"substreams" ↦{dq2} m ∗ ownMap m (DFrac.own 1) M ∗
      wgsF wgs go!"resuming" ↦{dq3} s ∗ s ↦* l }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"closeSubstream")) (Val #ws))
  {{ RET #(); wsF ws go!"id" ↦ id ∗ wgsF wgs go!"closeErr" ↦{dq1} e ∗
      wgsF wgs go!"substreams" ↦{dq2} m ∗ wgsF wgs go!"resuming" ↦{dq3} s ∗
      (if decide (id = W64 (-1)) then iprop(ownMap m (DFrac.own 1) M ∗ s ↦* nilOut l ws)
       else iprop(ownMap m (DFrac.own 1) (GMap.delete id M) ∗ s ↦* l)) }}

end spec

end EtcdGrove
end Perennial
