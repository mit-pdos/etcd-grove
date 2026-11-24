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
the connections to `a`, each of which carries the calls of `Client_Put_dist`/`Client_Get_dist`
(review F4; since the S2 interface switch `etcdAddrAt` is `grpcAddrAt a (etcdSvc γE mid)`, whose
`addrProto` lets another program dial, listen and accept at `a`, serve an empty grpc server there, or
bridge it, review 4; no proof establishes the opaque `grpcCliPI`/`grpcSrvPI` of any bytes, and this
axiom's post is `True`; nothing is claimed of other bytes). Every call that reaches a handler is one a client deposited under `a`'s
protocol (the interpretation of `etcdAddrAt`): a unary call of etcd's KV table at `(γE, mid)`,
whose spec is at the view published at `γE`. The member's view is that view
(`ν = memberView ρ`), and the member is `mid` (`memberUp`'s id), so every such call meets the
spec the member's handlers are proved against.

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
from `listen_au` over `etcdAddrAt`'s `addrProto`) and `grpcServes (etcdSvc γE mid)` from
the handlers' contracts (`phase7-plan.md` §2.4, §3, "`etcdstart`"), the published view converted through
`etcdPubSpec`.
Its statement needs no change, but S2's version may strengthen the post. **Obligation for S2's
proof (review F5):** today's `Serve.spec` returns the served member's id existentially (`grpcUpM`),
while this statement fixes the table's `mid` to `memberUp`'s id; S2's proof must show the id the
server registers is `memberUp`'s (`mid = id`), or the statement changes at retirement. -/
axiom Serve_dist.wp_proof : Serve_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
