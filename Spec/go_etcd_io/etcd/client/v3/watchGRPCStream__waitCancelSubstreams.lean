/-
`(*clientv3.watchGRPCStream).waitCancelSubstreams(stopc)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- **`w.waitCancelSubstreams(stopc)` with no substream resuming** (its only call under
`noRetryableStreamErr`, `newWatchClient`'s first): returns a channel that will be closed (a
goroutine closes it after its wait group, empty, is done). -/
abbrev watchGRPCStream.waitCancelSubstreams.spec : Prop :=
  ∀ (wgs : Loc) (s : GoSlice) (stopc : GoChan) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"resuming" ↦{dq} s ∗ s ↦* ([] : List Loc) }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"waitCancelSubstreams")) (Val #stopc))
  {{ (donec : GoChan), RET #donec; wgsF wgs go!"resuming" ↦{dq} s ∗ s ↦* ([] : List Loc) ∗
      ∃ γ : ChanNames, ownBroadcastChan donec γ iprop(True) .Unknown }}

end spec

end EtcdGrove
end Perennial
