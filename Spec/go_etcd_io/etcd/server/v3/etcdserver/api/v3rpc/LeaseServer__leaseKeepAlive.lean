/-
`v3rpc.LeaseServer.leaseKeepAlive` (`lease.go`): the keep-alive stream's loop. Lean-first (no Rocq
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

/-- **`ls.leaseKeepAlive(stream)`** on the `*LeaseServer` `ls` over the server `s`
(`leaseServerAt`), whose renewals meet the contract `raftLeaseRenew s E γl S'`, on a fresh server
end of a keep-alive stream (`srvStreamIs`, both tokens at `[]`) whose responses' content is the
keep-alive's (`kaStreamSpec` at the run's token) and whose requests' content gives their bounds
(`kaUpOk`), with the renewals' per-call resources `S'` and the header's revision reader `A.revR`:
the loop of receive, fill, renew, send. It returns `S' ∗ A.revR` when the loop ends (the stream's
tokens spent), with the stream specification. -/
abbrev v3rpc.LeaseServer.leaseKeepAlive.spec : Prop :=
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
    (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"leaseKeepAlive")) (Val #st))
  {{ (err : GoInterface), RET #err; S' ∗ A.revR ∗
      v3rpc.kaStreamSpec s E γl γs (auth.ctxTokenOf (GoInterface.ok ci)) Dn }}

end spec

end EtcdGrove
end Perennial
