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
the connections to `a`, each of which carries the calls of the clientv3 contracts (`KV_Put_dist`,
`KV_Get_dist`, `KV_Delete_dist`, `KV_Compact_dist`, `Txn_Commit_dist`; review F4; since the S2 interface
switch `etcdAddrAt` is `grpcAddrAt a (etcdSvc Γ mid)`, whose
`addrProto` lets another program dial, listen and accept at `a` or serve an empty grpc server there, none of
which answers a call successfully (not an HTTP server: `http.register` needs the `addrUnset` the start spent;
not bridge it: `bridge.New` also consumes `netAddrLeft a` since review 4's fix); no proof establishes the
opaque `grpcCliPI`/`grpcSrvPI` of any bytes, and this axiom's post is `True`. Its claim that no thread of the
member gets stuck or panics covers every connection a verified program can make to `a`: the client contracts'
calls, the watch streams of `Watch_dist`/`RequestProgress_dist` (the clientv3 watcher's create, cancel and
progress requests, under `watcher.Watch.spec`'s preconditions), which the member's watch handler meets as in its
in-process proof (`watchUp`; the N3 review's F4, added with the first result resting on those axioms, F5's
compact workload, 2026-11-26), and raw writes, which establish no protocol (true of grpc-go, which closes a connection on a bad
preface; re-review after review 4, 2026-11-24; narrowed by the O1-B review's F4, 2026-11-25). Every call that reaches a handler is one a client deposited under `a`'s
protocol (the interpretation of `etcdAddrAt`): a unary call of etcd's table at `(Γ, mid)`, whose spec
is at the view's names. The member's KV names agree with the view's (`kvCongr ρ.rd.kv Γ.kv`, what
`kvInv_congr` and `isKv_intro`'s `kvSame` need: one KV state, model and requested log for the whole
cluster), its auth mode, auth names, lessor name and lease mode are the view's (`memberUpL`/`memberUpOnL` at
`Γ.kv.lm`, `Γ.ls mid` and, with auth on, `Γ.au mid`: F7 and F2's P-L1, 2026-11-26, reviews
`notes/axiom-review/f7-combined.md` §1, §3; until then auth off only and nothing tied `Γ.ls`), and the member is
`mid` (`memberUpL`'s id), so every such call meets the spec the member's handlers are proved against.

Why it is true: today's `etcdstart.Serve.wp_proof` proves the same body in one process, through
`grpc.start`/`grpc.serve` and the handlers' run contracts (`grpcRunOkMd`, on the member's own
heap). What differs across machines is only how a call's deposit reaches the run, which is
`a`'s protocol in place of `Invoke`'s and `acceptRun`'s pairing in one heap: on `lean`,
`grpcAddrAt a Svc` sets `a`'s protocols to the opaque `grpcCliPI Svc`/`grpcSrvPI Svc`
(`InvGrpcWire.lean`), whose intended reading is the defined `grpcCliP`/`grpcSrvP` (the model's
bytes and the attempt's slot). The post is `True`: the member's proof only branches on the error.

Retired by S2's `etcdSvc`. The interface switch (2026-11-24) made `etcdAddrAt` grpc's own address fact
over the axiomatized table and `Server.Serve` a trust-boundary axiom over a table
(`grpc.Server.Serve.wp_proof`, `grpcServeTok gs lis a Svc`); what is left is S2's etcd side: a member
listening at an address its deployment set (`grpcServeTok`'s branch `grpcSrvNew ∗ netListenerOpen lis a`,
from `listen_au` over `etcdAddrAt`'s `addrProto`) and `grpcServes (etcdSvc Γ mid)` from
the handlers' contracts (`phase7-plan.md` §2.4, §3, "`etcdstart`"), each at the member's names through
`kvCongr` with the view's.
Its statement needs no change, but S2's version may strengthen the post. **Obligation for S2's
proof (review F5):** today's `Serve.spec` returns the served member's id existentially (`grpcUpM`),
while this statement fixes the table's `mid` to `memberUpL`'s (`memberUpOnL`'s) id; S2's proof must show the id the
server registers is the member's (`mid = id`), or the statement changes at retirement. -/
axiom Serve_dist.wp_proof : Serve_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
