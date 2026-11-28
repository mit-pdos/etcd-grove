/-
`etcdstart.Serve` on a member machine of a distributed deployment: a trust-boundary axiom until
#24's S2 (`notes/putget-dist-plan.md` §12). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`etcdstart.Serve` on a member machine** (trust boundary until #24's S2;
`notes/putget-dist-plan.md` §12). What it asserts of etcd v3.6's `v3rpc.Server` and grpc-go
v1.84's `Server.Serve` (the model, `models/grpc`), over the net extension: `Serve` builds the gRPC
server from the started member (`v3rpc.Server`), listens at `a` (`net.Listen`), starts
`gs.Serve(l)` on its own goroutine and returns, and no thread it starts gets stuck or panics on
the connections to `a`, each of which carries the calls a client deposits under `a`'s protocol for
etcd's table `etcdSvc Γ mid` (`etcdAddrAt`): with auth off, etcd's KV methods at their view entries
(`etcdKvSvc Γ.kv`; the client's `kv.Put.spec`, ... through `isKv_of_kvClientAt`); with auth on, the calls
of `KV_PutOn_dist`, `KV_DeleteOn_dist`, `KV_GetOn_dist`, `Txn_CommitOn_dist`, `New_user_dist`'s
`Authenticate`, the five `Auth_*_dist` admin calls and the `Lease_*On_dist`/F2 lease calls, whose handlers
are the `etcd*SpecOn` ones at `T := False` (`f9-auth-combined-review.md` D4); in both, the watch streams of
`Watch_dist`/`RequestProgress_dist`/`WatchOn_dist` (the clientv3 watcher's create, cancel and progress
requests, under `watcher.Watch.spec`'s preconditions; with auth on, the stream carries the client's own token
or none, and metadata meeting `outTokOkS`; the handler's refusal path is `isWatchPermitted`'s, proved in
process: `watchon-dist.md` F5, `f9-auth-combined-review.md` D1), which the member's watch handler meets as in
its in-process proof (`watchUp`), and raw writes, which establish no protocol (grpc-go closes a connection
on a bad preface). `etcdAddrAt`'s `addrProto` lets another program dial, listen and accept at `a` or serve an
empty grpc server there, none of which answers a call successfully (not an HTTP server: `http.register`
needs the `addrUnset` the start spent; not a bridge: `bridge.New` also consumes `netAddrLeft a`).

**The member is the view's.** Its KV names agree with the view's (`kvCongr ρ.rd.kv Γ.kv`: one KV state,
model and requested log for the cluster, what the view specs' conversions `etcdPutSpecV_M`, ... need, through
`kvSame`), its auth mode, auth names, lessor name and lease mode are the view's (`memberUpL`/`memberUpOnL` at
`Γ.kv.lm`, `Γ.ls mid` and, with auth on, `Γ.au mid`; F7 and F2's P-L1, `notes/axiom-review/f7-combined.md`), and
it is `mid` (`memberUpL`'s id), so every call meets the spec the member's handlers are proved against.

**The KV entries never refuse** (stage B′, 2026-11-28; `notes/etcdsvc-b.md`). With auth off, serving a flagged
entry (`grpcServesEnt`) means the member's KV handler, through etcd's unary chain, meets `grpcRunNRMd`: no error
it returns has a description among `refusalDescs`. True of etcd at the pin (`etcd_noRefusal`'s argument):
* the three auth refusals (`togRPCError`'s `ErrUserEmpty`, `ErrInvalidAuthToken`, `ErrAuthOldRevision`) come
  only from checks that return them with authentication enabled. The member's auth store starts disabled
  (`memberUpL`: `E.authOn = false`) and stays so: enabling it is an `AuthEnable` call, an Auth entry of the
  table, which for an auth-off view is `etcdSvcRest`'s (no law: no proof calls it);
* the learner refusal (`interceptor.go:54`, under `IsMemberExist(MemberID()) && IsLearner()`): the member is a
  voter for its whole life. `NewServer` built it under `bootCfgFresh` (`NewCluster`, no discovery): a member
  of a new cluster's initial membership, all voters (`NewClusterFromURLsMap`, `NewMember`). etcd has no
  voter-to-learner change: at apply, `ValidateConfigurationChange` refuses an add of an existing id
  (`ErrIDExists`) or a removed one (`ErrIDRemoved`), and the entry becomes a no-op; a promotion only clears
  `IsLearner`; `MemberUpdate`'s attributes have `IsLearner` false. A removed member fails `IsMemberExist`;
* the old balancer's two strings occur only in the client (`retry.go`); grpc's own errors (`dec`'s,
  `grpcDecOk`; unknown method, transport) carry grpc's messages.

Why it is true: today's `etcdstart.Serve.wp_proof` proves the same body in one process, through
`grpc.start`/`grpc.serve` and the handlers' run contracts (`grpcRunOkMd`, on the member's own
heap). What differs across machines is how a call's deposit reaches the run, `a`'s protocol in place of
`Invoke`'s and `acceptRun`'s pairing in one heap (the opaque `grpcCliPI Svc`/`grpcSrvPI Svc`, whose intended
reading is the defined `grpcCliP`/`grpcSrvP`), and, for the KV entries, the no-refusal conjunct above. The post
is `True`: the member's proof only branches on the error.

Retired by S2's etcd side: `grpcServes (etcdSvc Γ mid)` from the handlers' contracts (`phase7-plan.md` §2.4,
§3, "`etcdstart`"), with `grpcRunNRMd` of etcd's KV handlers and chain (a voter fact and the auth store's
disabled state carried by the server's invariants), and the remaining entries defined. **Obligation for S2's
proof (review F5):** today's `Serve.spec` returns the served member's id existentially (`grpcUpM`), while this
statement fixes the table's `mid` to `memberUpL`'s (`memberUpOnL`'s) id; S2's proof must show the id the server
registers is the member's (`mid = id`), or the statement changes at retirement. -/
axiom Serve_dist.wp_proof : Serve_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
