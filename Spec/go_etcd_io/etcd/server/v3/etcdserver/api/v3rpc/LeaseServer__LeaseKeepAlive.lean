/-
`v3rpc.LeaseServer.LeaseKeepAlive` (`lease.go`): the keep-alive stream's handler. Lean-first (no Rocq
counterpart); the vocabulary is `v3rpc/InvLeaseKeepAlive.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseKeepAlive

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

/-- **`ls.LeaseKeepAlive(stream)`**: `leaseKeepAlive`'s premises; it runs the loop on a goroutine
and returns the loop's error, or the stream's context's error if the context is done first (the
goroutine then keeps running, with `S' ∗ A.revR`). It returns with the stream specification, as
`watchServer.Watch`. -/
abbrev v3rpc.LeaseServer.LeaseKeepAlive.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (E : apply.AEnv GF) (γl : GName)
    (S' : IProp GF) (st : GoInterface) (γs : StreamNames)
    (Up : Nat → KaReqM → IProp GF) (Dn : Nat → (w64 × w64) → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.leaseServerAt p s A cid mid ∗ v3rpc.raftLeaseRenew s E γl S' ∗
      srvStreamIs st γs pbLeaseKeepAliveRequest pbLeaseKeepAliveResponse Up Dn ci cd ∗
      v3rpc.kaStreamSpec s E γl γs (auth.ctxTokenOf (GoInterface.ok ci)) Dn ∗
      v3rpc.kaUpOk E γl Up ∗
      srvRecvTok (Req := pbLeaseKeepAliveRequest) γs [] ∗
      srvSendTok (Rep := pbLeaseKeepAliveResponse) γs [] ∗ S' ∗ A.revR }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseKeepAlive")) (Val #st))
  {{ (err : GoInterface), RET #err;
      v3rpc.kaStreamSpec s E γl γs (auth.ctxTokenOf (GoInterface.ok ci)) Dn }}

end spec

end EtcdGrove
end Perennial
