/-
`v3rpc.quotaKVServer.Put` (`v3rpc/quota.go`; unit P3b). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota

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

/-- **`q.Put(ctx, r)`** on a `*quotaKVServer` over a service `kv` whose `Put` meets `Spec` with
the resource `S` (`grpcHandlerOk`), for the server `s` (its request-path view and id budget, for
the alarm): the quota check, then `kv.Put(ctx, r)`: `S` and the reader slot of `leadTimeMu` come
back, and on success the response is `kv.Put`'s (at some `m'` with `Φ m'`). -/
abbrev v3rpc.quotaKVServer.Put.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (q s : Loc) (kv : GoInterfaceOk)
    (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (m : Req.M) (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaKVServerAt q kv s ∗ grpcHandlerOk #(methods kv.ty go!"Put" kv.v) S Spec ∗
      isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗ S ∗ srvLeadTimeReader s ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Spec m Φ }}
    (App (App (Val (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ srvLeadTimeReader s ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') }}

end spec

end EtcdGrove
end Perennial
