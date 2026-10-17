/-
`v3rpc.LeaseServer.LeaseKeepAlive` (`lease.go`): the keep-alive stream's handler (since
etcd-io/etcd#21960 it runs the loop `leaseKeepAlive` itself). Lean-first (no Rocq
counterpart); the vocabulary is `v3rpc/InvLease.lean` (etcd-io/etcd#21960).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`ls.LeaseKeepAlive(stream)`** (the gRPC method): on the server end of a keep-alive stream (`srvStreamIs`),
with the receiver's token at the requests `Lq` received and the sender's at the responses `Lr`
sent, as many (each request answered), and the stream's content of the responses the handler's
(`lkStreamSpec`: the `j`th response answers the `j`th request): it returns with both tokens (the
handler is done with the stream). -/
abbrev v3rpc.LeaseServer.LeaseKeepAlive.spec : Prop :=
  ∀ (p : Loc) (S : v3rpc.LSrv GF) (st : GoInterface) (γs : v3rpc.StreamNames)
    (Up : Nat → w64 → IProp GF) (Dn : Nat → v3rpc.LKRespM → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (Lq : List w64) (Lr : List v3rpc.LKRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.isLeaseServer p S ∗
      v3rpc.srvStreamIs st γs v3rpc.pbLeaseKeepAliveRequest v3rpc.pbLeaseKeepAliveResponse Up Dn ci cd ∗
      v3rpc.lkStreamSpec γs S Dn ∗
      v3rpc.srvRecvTok (Req := v3rpc.pbLeaseKeepAliveRequest) γs Lq ∗
      v3rpc.srvSendTok (Rep := v3rpc.pbLeaseKeepAliveResponse) γs Lr ∗
      ⌜Lr.length = Lq.length⌝ ∗ S.A.revR }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseKeepAlive")) (Val #st))
  {{ (err : GoInterface), RET #err; v3rpc.lkDone γs S }}

/-- **The handler's specification before etcd-io/etcd#21960** (the watch handler's shape,
`watchServer.Watch.spec`): the same premises, and it returns, nothing given back. Before the PR,
`LeaseKeepAlive` ran `leaseKeepAlive` in a goroutine of its own and returned either with its
result or as soon as the stream's context was done, the goroutine possibly still in `Recv`,
`LeaseRenew` or `Send` and holding the tokens: in this model, whose `Recv`/`Send` may succeed
after the handler returned, the tokens cannot come back with the return (not proved: the old code
is not translated). In real grpc, which cancels the stream when the handler returns, that
goroutine's `Recv`/`Send` fail at once: the difference is the model's, not a leak. Neither spec
says the handler returns when the stream's context is canceled (partial correctness). -/
abbrev v3rpc.LeaseServer.LeaseKeepAlive.spec_old : Prop :=
  ∀ (p : Loc) (S : v3rpc.LSrv GF) (st : GoInterface) (γs : v3rpc.StreamNames)
    (Up : Nat → w64 → IProp GF) (Dn : Nat → v3rpc.LKRespM → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (Lq : List w64) (Lr : List v3rpc.LKRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.isLeaseServer p S ∗
      v3rpc.srvStreamIs st γs v3rpc.pbLeaseKeepAliveRequest v3rpc.pbLeaseKeepAliveResponse Up Dn ci cd ∗
      v3rpc.lkStreamSpec γs S Dn ∗
      v3rpc.srvRecvTok (Req := v3rpc.pbLeaseKeepAliveRequest) γs Lq ∗
      v3rpc.srvSendTok (Rep := v3rpc.pbLeaseKeepAliveResponse) γs Lr ∗
      ⌜Lr.length = Lq.length⌝ ∗ S.A.revR }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseKeepAlive")) (Val #st))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
