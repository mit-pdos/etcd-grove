/-
`v3rpc.quotaLeaseServer.LeaseGrant` (`v3rpc/quota.go`; the client lease's stage (c)). Lean-first
(no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvLease.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease

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

/-- **`q.LeaseGrant(ctx, r)`** on a `*quotaLeaseServer` over a service `ls` whose `LeaseGrant`
meets `Spec` with the resource `S` (`grpcHandlerOk`), for the server `s`: the quota check, then
`ls.LeaseGrant(ctx, r)`: `S` and the check's reader slots (`quotaRd`) come back, and on success the
response is `ls.LeaseGrant`'s (at some `m'` with `Φ m'`); as `quotaKVServer.Put`. -/
abbrev v3rpc.quotaLeaseServer.LeaseGrant.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (q s : Loc) (ls : GoInterfaceOk)
    (S : IProp GF) (m : Req.M) (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaLeaseServerAt q ls s ∗ grpcHandlerOk #(methods ls.ty go!"LeaseGrant" ls.v) S Spec ∗
      S ∗ v3rpc.quotaRd s ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Spec m Φ }}
    (App (App (Val (q @!! go.GoType.PointerType v3rpc.quotaLeaseServer.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ v3rpc.quotaRd s ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') }}

end spec

end EtcdGrove
end Perennial
