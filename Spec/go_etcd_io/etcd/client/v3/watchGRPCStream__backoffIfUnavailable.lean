/-
`(*clientv3.watchGRPCStream).backoffIfUnavailable(backoff, err)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.backoffIfUnavailable(backoff, err)` (the stream's context a model one, an error grpc's
`status` accepts): sleeps for some time if the error is `Unavailable`, returns some backoff. -/
abbrev watchGRPCStream.backoffIfUnavailable.spec : Prop :=
  ∀ (wgs : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (backoff : _root_.Perennial.time.Duration) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"ctx" ↦□ (GoInterface.ok ci) ∗ context.isContext ci cd ∗ statusErrOk err ∗
      clientWatchVars }}
    (App (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"backoffIfUnavailable")) (Val #backoff)) (Val #err))
  {{ (d : _root_.Perennial.time.Duration), RET #d; True }}

end spec

end EtcdGrove
end Perennial
