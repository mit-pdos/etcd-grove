/-
`v3rpc.LeaseServer.LeaseRevoke` (`v3rpc/lease.go`; the client lease's stage (c)). Lean-first (no
Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvLease.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseOn

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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`ls.LeaseRevoke(ctx, r)`** on the `*LeaseServer` `ls` over the server `s`
(`leaseServerAt`), whose `LeaseRevoke` meets the contract `lessorRevokeOkM on s E ρ S`, in a gRPC run (its
context, the resource `S`), on a decoded request: `ls.le.LeaseRevoke(ctx, r)`, then the header
filled: `S` back, and the server's response with its header filled by the cluster `cid` and the
member `mid`, its revision not `0` and reached (and nothing else), or `nil` and a non-nil error
(`leaseGrantOut`, `leaseRevokeOut`). (Auth-lease S3c, decision D6/C5′, 2026-11-15: the revocation
contract alone, at the auth mode `on` (until then the auth-off `raftLessor s E S`, deleted by the
C5′ merge, of which only the revocation is called), with the client's `Q` and the server's permit at the request
context's token, handed through, and on success the client's result `leaseRevokeResT`.) (Auth-lease S4, Freeze §7 R4-1, D-h) For the caller's lower bound `n` of the published auth index, a
success also carries `requireAuthInfo`'s check at the request context's token relative to `n`
(`leaseCheckFrom … n (fun _ => True)`). -/
abbrev v3rpc.LeaseServer.LeaseRevoke.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) (ci : GoInterfaceOk) (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64)
    (Q : KVState → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.leaseServerAt p s A cid mid ∗ v3rpc.lessorRevokeOkM on s E ρ S ∗ S ∗
      auth.authPubLbM E.authMode n ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ □ (⌜on = true⌝ → auth.ctxToken (GoInterface.ok ci) tok) ∗ v3rpc.leaseRevokeReqIs r m ∗
      leaseRevokePermitM on ρ.raft ρ.kv (v3rpc.hdrBoundT (srvTLSId s) E.authMode tok) m Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseRevoke"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ v3rpc.leaseRevokeOut E cid mid resp err ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ (v3rpc.leaseRevokeResT on (srvTLSId s) E ρ tok m Q ∗
        leaseCheckFrom (srvTLSId s) E tok n (fun _ => iprop(True)))) ∗
      go_etcd_io.etcd.cache.v3.srvErrOk err }}

end spec

end EtcdGrove
end Perennial
