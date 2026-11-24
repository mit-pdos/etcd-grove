/-
`(*Client).Put` to a member at another machine: a trust-boundary axiom until #24's S2
(`notes/putget-dist-plan.md` §12). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientPutDist

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

/-- **`(*Client).Put` to a member at another machine** (trust boundary until #24's S2;
`notes/putget-dist-plan.md` §12). What it asserts of clientv3 v3.6 (`Client.Put` → `kv.Put` →
`kv.Do` → the retry interceptor → the KV stub) and grpc-go v1.84's `ClientConn.Invoke` (the model)
over the net extension, for a client that dials with **no proxy dial path** (`clientNoProxy`: the
client's configuration carries `grpc.WithNoProxy()`, which `etcdstart.NewClients` passes, so grpc-go
sets `useProxy` false and never wraps the resolver in its proxy-resolving `delegatingresolver`, nor
dials through an HTTP `CONNECT` proxy that `HTTPS_PROXY` names; review F1, evidence `TestProxyRogue`
and `TestWithNoProxyFix`, `notes/putget-dist-plan.md` §12): each attempt dials `ep` itself,
deposits the call's request precondition in the connection's slot and writes the request under
`ep`'s protocol (`etcdAddrAt`'s interpretation). `ep`'s only acceptor is the member `mid`
publishing at `γE` (`Serve_dist`; **Known false as of 2026-11-24 (review 4, pending a decision):** `bridge.New` takes only `netListenerAt l a` (`addrClaim ∗ netListenerOpen`), so a program holding `netAddrFree ep` can listen at `ep` and set (or fabricate the view of) `etcdAddrAt ep …`, then relay `ep` to an unrelated etcd; the proposed fix is `bridge.New` also consuming `netAddrLeft a`, `notes/putget-dist-plan.md` §12.), which instantiates the deposit at its own published view, so the
caller's update runs at that view. The deposit is under a later (review F2): the member takes program
steps between reading the deposit from the connection's slot and firing the update, so it strips one
`▷`. A `nil` result is the handler's reply after the put fired once on the member's store: its
update, built from the invariant (`putAu_of_putGetInv`), set the flag.

Why it is true: it is `client.client_Put_own` (proved) at the member's `⟨ep, E, ρ.rd, cid, mid⟩`.
That proof's only cross-process step is `Invoke`'s registration (`kvRegsAt`), and the step that
replaces it is the deposit's instantiation at the published view: `envAt_agree` and
`putGetInv_st` turn the caller's invariant at `γr` into the member's at `ρ.rd`. The
`kvLogLb E.γs []` floor is free (`kvLogLb_nil`). `client_Put_own`'s `putReplied` is dropped: no
caller reads it. The deposit is persistent, so a resent attempt deposits it again, as in the
in-process proof. Without the no-proxy fact it would be false: a proxy named by the environment
receives every attempt (`TestProxyRogue`).

Retired by #24's switch (`isGrpcRpcMd := grpcSvcAt`, `etcdAddrAt` defined; `grpcSvcAt_of_addr`
gives `kvRegsPub ep γE mid`) together with clientv3's pub-form put, `client_Put_pub`, a new proved
lemma. Then it is a theorem with this statement. The deposit is an update at the full mask (`={⊤}=∗`):
the retiring proof's server must fire it with no invariant open, or this statement changes. -/
axiom Client_Put_dist.wp_proof : Client_Put_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
