/-
`v3rpc.isClientCtxErr` (`util.go`): it classifies an error for the logs, through grpc's
`status.FromError` and the status's code and message. Proved over its body (prove-grpcext,
2026-11-20, `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/isClientCtxErr.lean`; an axiom
until then). Lean-first (no Rocq counterpart); the vocabulary is `v3rpc/InvWatchStream.lean` and
`v3rpc/InvWatch.lean`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`isClientCtxErr(ctxErr, err)`** of an error grpc's `status` accepts (`statusErrOk`) returns (a
boolean the caller only logs by). (prove-grpcext, 2026-11-20) The premise `statusErrOk err` is new: the
spec had none, which was false (`notes/specs-only/ledger.md`, 2026-11-20, "`v3rpc.isClientCtxErr` calls
`status.FromError` without its premise"): with `ctxErr == nil` the body calls `status.FromError(err)`,
which calls `err.Error()` (and `GRPCStatus()`), so an error whose `Error()` panics makes it panic. Every
caller passes a stream's error, which grpc's `status` accepts (`srvStreamIs`'s `Recv` and `Send`), as
the spec plan's `errView err` (`SpecPlan/.../v3rpc/isClientCtxErr.lean`). -/
abbrev v3rpc.isClientCtxErr.spec : Prop :=
  ∀ (ctxErr err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      go_etcd_io.etcd.cache.v3.statusErrOk err }}
    (App (App (Val (@! v3rpc.isClientCtxErr)) (Val #ctxErr)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
