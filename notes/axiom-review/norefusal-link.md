# Review: `etcd_noRefusal` and the address it speaks of (2026-11-24)

**Target.** `axiom etcd_noRefusal` and `axiom etcd_noOtherRefusal`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NoRefusal.lean`, D29 and F-S2 part 1), as they
stood on `lean` at `6425cfb74a`:

```
axiom etcd_noRefusal (addr) (gs q p s) (lis) (E) (ρ) (ics sics svcs regs sregs) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) → E.authOn = false →
  isServerReq s E ρ ∗ v3rpc.quotaKVServerAt q ⟨kvServer, #p⟩ s ∗
    grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
  grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ ⌜noRefusalAt addr⌝
```

(`etcd_noOtherRefusal` the same over `isServerReqM E.authOn`, concluding `noOtherRefusalAt addr`.)

**Finding (refuted).** Found by an axiom sweep (2026-11-24; its Go program panicked in 13 of 14 runs, the copy here 1/1). The
conclusion is a pure, global fact about the address string, `noRefusalAt addr`, which the attempt contract
(`grpcInvokerOk`, `Proof/google_golang_org/grpc/InvGrpc.lean`) reads for every call of a `kvMethod` at `addr`:
`kvMethod method ∧ noRefusalAt a → d ∉ refusalDescs`. The premises name etcd's server `gs` being built and *a*
listener at `addr`, and both come back unchanged: nothing ties `addr` to `gs`.

The route (`examples/axiomcx/norefusal/`, `Main`, `TestMainPanics`):

1. start a member (`etcdstart.StartServer`) and build etcd's gRPC server over it, `gs := v3rpc.Server(s, nil, nil)`
   (`v3rpc.Server.spec`: `grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs` with `serverRegsOk`, so
   `kvRegs q ⊆ regs`, and `quotaKVServerAt q … s`); authentication is off and the member a voter;
2. `l := net.Listen(addrA)` (`netListenerAt l addrA ∗ netAddrLeft addrA`);
3. `etcd_noRefusal addrA gs … l`: `noRefusalAt addrA`, and the listener back;
4. a second server `gs2 := grpc.NewServer()`, `RegisterKVServer(gs2, refuser{})`, whose `Put` returns
   `rpctypes.ErrGRPCNotSupportedForLearner`; `grpc.start'` on `gs2`, `l`, `addrA` (it takes `netListenerAt` and
   `netAddrLeft`, both still held), `go gs2.Serve(l)` (Serve's axiom);
5. `KVClient.Put` at `addrA` over a plain `grpc.NewClient`: the attempt contract says the error's description is no
   refusal (`noRefusalAt addrA`); Go returns `"etcdserver: rpc not supported for learner"`, and the program panics.

`gs` is never served. Go: go1.27.3, `lean`'s pins, `TestMainPanics` passes (`recovered: norefusal: a refusal at an
address etcd_noRefusal said refusal-free`), 1/1 here. `etcd_noOtherRefusal` has the same shape (the learner
description is in `otherRefusalDescs`), latent: no result uses it.

## The fix

Both axioms now take **the server listening at the address**, after its start, instead of a server being built and
some listener:

```
axiom etcd_noRefusal (addr) (γ : GName) (c : GrpcSrvCfg GF) (q p s) (E) (ρ) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ c.regs) → E.authOn = false →
  isServerReq s E ρ ∗ v3rpc.quotaKVServerAt q ⟨kvServer, #p⟩ s ∗
    grpcAddrIs addr γ ∗ grpcSrvCfg γ c ⊢ ⌜noRefusalAt addr⌝
```

and `etcd_noOtherRefusal` the same (`isServerReqM E.authOn`, `noOtherRefusalAt`). `grpcAddrIs addr γ` ("the server
listening at `addr` is `γ`") is made only by `grpc.start` (from that server's `grpcSrvNew` and the listener, both
consumed) and by `bridge.New` (an address relaying to the server at another), and is one per address
(`grpcAddrIs_agree`); `grpcSrvCfg γ c` is that server's configuration, made by the same start, one per server
(`grpcSrvCfg_agree`). So the claim is about the server that answers calls at `addr`, with etcd's KV service over `s`
registered on it. `etcdKVSrvAt addr s` bundles the four facts; `etcdKVSrvAt_of_serverAt` makes it from `grpc.start'`'s
`grpcServerAt`, and `etcd_noRefusal_at` is the axiom at it.

**Trust does not grow.** Every instance of the new statement is one of the old: `grpcAddrIs addr γ ∗ grpcSrvCfg γ c`
exist only after `grpc.start` consumed `grpcSrvNew gs c.ics c.sics _ c.regs c.sregs ∗ netListenerAt lis addr`, at
which moment the old axiom's premises held (`isServerReq` and `quotaKVServerAt` are persistent) and gave the same
`noRefusalAt addr`; for a bridged address, the old axiom at the target and the bridge's own carry
(`⌜noRefusalAt addr → noRefusalAt a⌝`, `bridge.New`'s spec) give it. The new statement only drops the instances where
the address is served by a server other than the one named. (It is not a syntactic strengthening of the premises:
the old premises are resources before the start, the new ones facts after it; the argument is per execution.) The
axiom count is unchanged.

**Call sites.** The proofs used the old axiom in the ghost step before the start (`grpcUp_noRefusal`, removed, and
five direct uses). The start happens inside `client.etcd_kv_started_with`, which now also returns `etcdKVSrvAt addr s`
(from `grpc.start'`'s `grpcServerAt`), as do `etcd_kv_started`, `kv_lease_served_core`, `kvWatch_served`,
`etcd_watch.wk_served_nd` and the new `etcdstart.kv_served_at` (`kv_served`, unchanged, is its weakening); each
call site takes `etcd_noRefusal_at` after the start. No top-level theorem's statement changed; the axiom sets per
result are unchanged (a result that did not use the axiom still does not: the started theorems return the facts, and
only the old call sites apply the axiom).

## Attacks on the fixed statement

- **The reported route.** The axiom no longer applies: its premise is the server at `addrA`, which is `gs2`, and `gs2`'s
  configuration does not register etcd's KV service over `s` (`refuser`'s handlers are not `kvRegs q`). Once `gs` is
  started at some other address, the axiom speaks of that address.
- **Two servers at one address.** Needs two `grpcAddrIs addr _`, made only by `grpc.start` (each consuming a
  `netListenerAt l addr`, whose `addrClaim addr` is exclusive and given once per address by program start) or
  `bridge.New`, which consumes `netListenerAt l a ∗ netAddrLeft a` of its own address (since 2026-11-24,
  `notes/axiom-review/bridge-addrleft.md`): a program cannot both start a server at `a` and bridge `a`.
  `grpcAddrIs_agree` is the axiom that says so; this review relies on it, as `isGrpcRpc` at an address does.
- **A bridge.** `bridge.New`'s `□ (∀ γ, grpcAddrIs addr γ -∗ grpcAddrIs a γ)` makes the axiom apply at the bridge's
  address `a` with etcd's `γ`: calls at `a` reach etcd's server unchanged, and a cut's errors are grpc's own (the
  bridge's spec already carries `noRefusalAt` from `addr` to `a`). No new instance.
- **Re-listening (`listen_au`).** After `grpc.start'` the address's protocols (`addrProto`, inside `grpcAddrAt`) are
  persistent, and with them `listen_au` lends the listening token: a second `net.Listen` at `addr` is possible in the
  logic. It succeeds only with no listener open at `addr` (the net extension's `ListenStep`, D6: `sys` while one is
  open, as Linux's `EADDRINUSE`), and the started server's listener is never closed by the program: `grpc.start`
  consumes it, and no spec gives it back or stops the server (no `Server.Stop` spec; Serve's accept loop drops the
  link only on a non-temporary `Accept` error, which a loopback listener does not produce in the target
  configuration). If a stop that frees the address is ever specified, `grpcAddrIs` (and so this axiom, and every
  `isGrpcRpc` at the address) must become a fact about a server's lifetime: the same remark as `grpcAddrIs_agree`'s
  docstring. A re-listened raw server serving `addr` while etcd's listener is open is excluded the same way.
- **A server of the deployment** (`grpcServeTok`'s second disjunct, a member whose address the deployment set): no
  `grpcAddrIs` is made, so the axiom does not apply there.

## The residual (open)

**The interceptor chain is not read.** The axiom (old and new) names the KV registrations but not the server's unary
chain `c.ics`. A program can register etcd's own KV service over the member on a server of its own behind an
interceptor that answers every call with a refusal: `gs3 := grpc.NewServer(grpc.ChainUnaryInterceptor(refuseAll))`,
`RegisterKVServer(gs3, v3rpc.NewQuotaKVServer(s))` (`NewQuotaKVServer.spec`: `quotaKVServerAt q … s`;
`RegisterKVServer.spec`: `kvRegs q` among the registrations), started and served at `addrB`. The fixed axiom applies
(`grpcAddrIs addrB γ3`, `grpcSrvCfg γ3 c3`, `kvRegs q ⊆ c3.regs`) and `Put` at `addrB` is refused
(`examples/axiomcx/norefusal/`, `MainInterceptor`, `TestMainInterceptorPanics`: panics, 1/1). The Lean side was not
built: it needs `ChainUnaryInterceptor`'s and `NewServer`'s specs to accept `refuseAll`, whose contract
(`srvInterceptorOk`) allows any non-nil, non-handler error, which `ErrGRPCNotSupportedForLearner` is (etcd's own
interceptor returns it).

Closing it needs the chain identified as `v3rpc.Server`'s: no spec says which `GoFunc`s `newLogUnaryInterceptor`,
`newUnaryInterceptor` and grpc-prometheus's `UnaryServerInterceptor` return (only their contracts, which a refusing
interceptor meets), and grpc-prometheus's is a trust-boundary axiom, so naming its value is a change to that axiom.
Two ways: (a) the constructors' specs return the closure they build (`ic = v3rpc.unaryIcOf l ∗ l ↦□ s`, provable for
etcd's two from their code; for grpc-prometheus a restated trusted spec), and the axiom requires
`c.ics = [logIcOf …, promIcOf …, unaryIcOf …]`; or (b) interceptor contracts that bound the descriptions of an
interceptor's own errors, proved for etcd's and assumed for grpc-prometheus's (transparent), with the voter fact
moved onto `IsLearner`. Neither is done here.
