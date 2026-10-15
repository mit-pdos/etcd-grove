/-
`v3rpc.isClientCtxErr` (`util.go`): the trust boundary (names only: it classifies an error
for the logs, through grpc's `status.FromError` and the status's code and message). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`isClientCtxErr(ctxErr, err)`** returns (a boolean the caller only logs by). -/
abbrev v3rpc.isClientCtxErr.spec : Prop :=
  ∀ (ctxErr err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc }}
    (App (App (Val (@! v3rpc.isClientCtxErr)) (Val #ctxErr)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
