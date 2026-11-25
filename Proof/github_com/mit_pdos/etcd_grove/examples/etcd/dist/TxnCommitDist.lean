/-
`(*txn).Commit()` by a client of members at other machines, at the cluster view: an interim trust-boundary axiom
(`notes/etcd-dist-plan.md` §18.4). The real Go is translated; the cross-machine proof needs #24's S2 client
side, which retires it. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`(*txn).Commit()` across machines** (interim trust boundary until #24's S2 client side; see the spec). What
it asserts of clientv3 v3.6 and grpc-go v1.84 (the model) over the net extension.

**Why it is an axiom** (the standing rule's order): the real Go is translated (clientv3 v3.6 with bodies,
grpc-go v1.84's model `models/grpc`), and in one process it is proved (`txn.Commit.spec`, over `Invoke`'s
registration, `isGrpcRpcsMd`/`kvRegsAt`). Across machines the call goes through grpc's `Invoke` over the
net extension: the S2 interface exists (`grpcAddrAt`, the opaque `grpcCliPI`/`grpcSrvPI`), but no proof
establishes the protocols of any bytes and `etcdSvc` has no law, so nothing can be proved over it yet: the
cross-machine proof needs #24's S2 client side (`notes/phase7-plan.md` §1.3, §2.4). A Go model with the same
behaviour is the grpc model itself (the same gap), and a trusted stand-in for clientv3 and grpc would still
need the wire proof and trust more than a contract per function (`notes/etcd-dist-plan.md` §18.4).

**Why it is true.** It is `txn.Commit.spec` with `isKv api Γ.kv false` replaced by `kvClientAt` (the address
facts at `Γ`) and the builder's state (`txnObjAt`, what `kv.Txn`, `If`, `Then`, `Else` give, proved, no call) over the client's endpoints, the error arm without `kvErr`, for a cluster with auth off (`Γ.auth = false`):
* *Who answers.* The client dials the endpoints themselves: `clientNoProxy` (`grpc.WithNoProxy()` in its
  configuration: grpc-go never wraps the resolver in its proxy-resolving `delegatingresolver` nor dials
  through an HTTP `CONNECT` proxy named by `HTTPS_PROXY`; review F1, `TestProxyRogue`, `TestWithNoProxyFix`).
  Each endpoint's table is set once by the start (`etcdAddr_set` spends `addrUnset`) and served only by
  `Serve_dist` at a member whose KV names are `kvCongr` to `Γ.kv`; `bridge.New` consumes `netAddrLeft`
  (review 4). So every reply is a real member's handler, at KV names `kvSame` to `Γ.kv` (what `isKv_intro`
  asks of each member), and the handler's spec is the one its in-process proof meets.
* *Errors, timeouts, retries are the error arm.* A read-only transaction is retried as a range (its
  update persistent), a writing one only after a refusal, which an auth-off member never sends: it is sent
  at most once and its one-shot update fires at most once.
* *What a success claims* is `txn.Commit.spec`'s post, which the in-process proof derives from the member's
  handler spec at its names through `kvSame`: the reply's fields as functions of the state the update fired
  at, whether the comparisons succeeded, the branch's responses and the header revision, and the revision lower bound of the cluster's requested log (`txnRevLb`).

Retired by #24's S2 client side: `etcdSvc` defined (each entry the member's handler spec at its names),
`Invoke` over the net model, and this statement proved from `txn.Commit.spec` over an `isKv` built from the
registration (`isKv_intro`, `kvSame` from `Serve_dist`'s `kvCongr`). The statement does not change. -/
axiom Txn_Commit_dist.wp_proof : Txn_Commit_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
