/-
**The gRPC Lease service's keep-alive stream, over the server's renewals** (item 6's second stage,
2026-11-01; `notes/lease-keepalive-plan.md`). Lean-first (no Rocq counterpart).

`lease.go`'s `LeaseServer.LeaseKeepAlive` runs `leaseKeepAlive(stream)` on a goroutine: a loop that
receives a request, fills a response's header, renews the request's lease through the server
(`ls.le.LeaseRenew`, `ErrLeaseNotFound` turned into TTL `0`) and sends the response. The `j`th
response answers the `j`th request.

**The contract** (`raftLeaseRenew s E γl S'`, persistent; K3): the triple of `*EtcdServer`'s
`LeaseRenew(ctx, id)` at the per-call resources `S'`, given back, at any context and lower bounds
`n` (the auth store's published index) and `m` (the lessor's history `γl`); its answer the server's
(`renewAns`): `nil` and the key check's verdict (`.write`), or a non-nil `applyErrIs` error. The
server meets it with `S' := E.RD ∗ levelTok 0 ∗ srvLgReader s ∗ srvReadReader s γr`
(`raftLeaseRenew_of_server`, `ServerLeaseRead.lean`).

**The stream specification** (`kaStreamSpec`, K4): the `j`th response `(id, ttl)` answers the `j`th
request `q` (`id = q.id`) and, unless its TTL is `0`, carries the renewal's verdict at the
request's ghost bounds (`q.nb`, `q.mb`, vouched for by the client's content `kaUp`) for the run's
token (`leaseCheckFrom`, the check over a token, as the watch stream's `watchAuthed`: registrable at
the stream's metadata). **Margins**: the response's header is not stated (the shared wire model
keeps none of it, so nothing of its revision); a TTL of `0` carries nothing; nothing of the
renewal itself (that the lease was renewed, its TTL); the verdict is the local member's lessor's,
which on a follower can lag the leader's (`nonissues/etcd-lease-renew-keys-follower-lag.md`); a failed
`Send` may have delivered its response.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseRead
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Proof.net.http.NetCtx
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The stream -/

/-- **The client's content of a keep-alive request** (the registration's `Up`, persistent): its
ghost bounds vouched for, the auth store's published index `q.nb` (in the server's mode) and the
lessor's history index `q.mb`. -/
def kaUp (E : apply.AEnv GF) (γl : GName) (_j : Nat) (q : KaReqM) : IProp GF :=
  iprop(□ auth.authPubLbM E.authMode q.nb ∗ □ lease.lessorLb γl q.mb)

instance kaUp_persistent (E : apply.AEnv GF) (γl : GName) (j : Nat) (q : KaReqM) :
    Persistent (kaUp (GF := GF) E γl j q) := by
  unfold kaUp; infer_instance

/-- **What the client's content gives the server** (persistent): the bounds of each request. -/
def kaUpOk (E : apply.AEnv GF) (γl : GName) (Up : Nat → KaReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (q : KaReqM), Up j q -∗ kaUp E γl j q)

instance kaUpOk_persistent (E : apply.AEnv GF) (γl : GName) (Up : Nat → KaReqM → IProp GF) :
    Persistent (kaUpOk (GF := GF) E γl Up) := by
  unfold kaUpOk; infer_instance

/-- **The `j`th response `r` of a keep-alive stream** (persistent; K4): it answers the `j`th request
`q` (its ID) and, unless its TTL is `0`, carries the renewal's verdict at `q`'s bounds for the
token `tok`. -/
def kaDn (s : Loc) (E : apply.AEnv GF) (γl : GName) (γs : StreamNames) (tok : Option GoString)
    (j : Nat) (r : w64 × w64) : IProp GF :=
  iprop(∃ q : KaReqM, upAt (Req := pbLeaseKeepAliveRequest) γs j q ∗ ⌜r.1 = q.id⌝ ∗
    (⌜r.2 = W64 0⌝ ∨ leaseCheckFrom (srvTLSId s) E tok q.nb
      (fun info => leaseKeysVerdictFrom E.authMode q.nb info γl q.mb q.id .write)))

instance kaDn_persistent (s : Loc) (E : apply.AEnv GF) (γl : GName) (γs : StreamNames)
    (tok : Option GoString) (j : Nat) (r : w64 × w64) :
    Persistent (kaDn (GF := GF) s E γl γs tok j r) := by
  unfold kaDn upAt; infer_instance

/-- **The keep-alive stream's specification** (persistent): the handler's `Dn` is `kaDn`. -/
def kaStreamSpec (s : Loc) (E : apply.AEnv GF) (γl : GName) (γs : StreamNames)
    (tok : Option GoString) (Dn : Nat → (w64 × w64) → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (r : w64 × w64), Dn j r ∗-∗ kaDn s E γl γs tok j r)

instance kaStreamSpec_persistent (s : Loc) (E : apply.AEnv GF) (γl : GName) (γs : StreamNames)
    (tok : Option GoString) (Dn : Nat → (w64 × w64) → IProp GF) :
    Persistent (kaStreamSpec (GF := GF) s E γl γs tok Dn) := by
  unfold kaStreamSpec; infer_instance

/-! ## The contract -/

/-- **The server's `LeaseRenew` answer** for a caller with the token `tok`, with the lower bounds `n`, `m`, for
the lease `id`: `nil` and the key check's verdict (`.write`), or a non-nil `applyErrIs` error
(`EtcdServer.LeaseRenew.spec`'s). -/
def renewAns (s : Loc) (E : apply.AEnv GF) (γl : GName) (tok : Option GoString) (n m : Nat)
    (id : w64) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ leaseCheckFrom (srvTLSId s) E tok n
      (fun info => leaseKeysVerdictFrom E.authMode n info γl m id .write)) ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err))

/-- **The server's `LeaseRenew`** (the keep-alive's contract, persistent; see the file header). (k8s
7f-4, Addendum T-k) At a weak context (`srvCtxWeak`, the caller lending `levelTok v3rpc.ctxErrLvl`,
returned) whose causes are context errors or etcd's no-leader error (`v3rpc.ctxCauseOk`), as
`EtcdServer.LeaseRenew.spec`. -/
def raftLeaseRenew (s : Loc) (E : apply.AEnv GF) (γl : GName) (S' : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (id : w64)
      (n m : Nat),
    {{ S' ∗ srvCtxWeak ci cd ∗ levelTok v3rpc.ctxErrLvl ∗ context.libCtxOk ci ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) tok) ∗ http.netCtxOkC ci ∗
        v3rpc.ctxCauseOk ci ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m }}
      (App (App (Val (srvM s go!"LeaseRenew")) (Val #(GoInterface.ok ci))) (Val #id))
    {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); S' ∗ levelTok v3rpc.ctxErrLvl ∗
        renewAns s E γl tok n m id err }})

instance raftLeaseRenew_persistent (s : Loc) (E : apply.AEnv GF) (γl : GName) (S' : IProp GF) :
    Persistent (raftLeaseRenew s E γl S') := by
  unfold raftLeaseRenew; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open Iris.ProofMode

end lemmas

end v3rpc
end EtcdGrove
end Perennial
