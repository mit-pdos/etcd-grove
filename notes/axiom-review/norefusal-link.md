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
some listener, and **its unary chain by identity**:

```
axiom etcd_noRefusal (addr) (γ : GName) (c : GrpcSrvCfg GF) (q p s) (E) (ρ) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ c.regs) → E.authOn = false →
  isServerReq s E ρ ∗ v3rpc.quotaKVServerAt q ⟨kvServer, #p⟩ s ∗
    grpcAddrIs addr γ ∗ grpcSrvCfg γ c ∗ v3rpc.etcdUnaryIcs s c.ics ⊢ ⌜noRefusalAt addr⌝
```

and `etcd_noOtherRefusal` the same (`isServerReqM E.authOn`, `noOtherRefusalAt`). `grpcAddrIs addr γ` ("the server
listening at `addr` is `γ`") is made only by `grpc.start` (from that server's `grpcSrvNew` and the listener, both
consumed) and by `bridge.New` (an address relaying to the server at another), and is one per address
(`grpcAddrIs_agree`: each of the two consumes a `netListenerAt l addr`, whose `addrClaim addr` is exclusive and given
once per address by program start); `grpcSrvCfg γ c` is that server's configuration, made by the same start, one per
server (`grpcSrvCfg_agree`). `v3rpc.etcdUnaryIcs s c.ics` (`v3rpc/UnaryChain.lean`) says the chain is
`[il, im, iu]` with `il` the closure `newLogUnaryInterceptor(s)` returns, `iu` the closure `newUnaryInterceptor(s)`
returns (each: the function's translated code, read off by `v3rpc.icClosureOf`, over a variable `l` with
`l ↦□ s`; both constructors' proved specs now return it, `rfl` from the code) and `im` one of grpc-prometheus's
(`promUnaryIc`, opaque, made only by `ServerMetrics.UnaryServerInterceptor`'s trusted spec, restated to return it);
`v3rpc.Server`'s spec returns `etcdUnaryIcs s [il, im, iu]`. So the claim is about the server that answers calls at
`addr`, with etcd's KV service over `s` registered on it behind etcd's own chain over `s`. `etcdKVSrvAt addr s ics`
bundles the server facts (with `c.ics = ics`), `etcdKVSrv addr s` adds the chain's identity; `etcd_noRefusal_at` and
`etcd_noRefusal_srv` are the axiom at them.

**Trust does not grow beyond restating one spec.** Every instance of the new statement is one of the old:
`grpcAddrIs addr γ ∗ grpcSrvCfg γ c` exist only after `grpc.start` consumed `grpcSrvNew gs c.ics c.sics _ c.regs
c.sregs ∗ netListenerAt lis addr`, at which moment the old axiom's premises held (`isServerReq` and
`quotaKVServerAt` are persistent; the old axiom read no chain, so any chain) and gave the same `noRefusalAt addr`;
for a bridged address, the old axiom at the target and the bridge's own carry (`⌜noRefusalAt addr → noRefusalAt
a⌝`, `bridge.New`'s spec) give it. The new statement only drops instances: those where the address is served by a
server other than the one named, and those whose chain is not etcd's. (It is not a syntactic strengthening of the
premises: the old premises are resources before the start, the new ones facts after it; the argument is per
execution.) The axiom count is unchanged. The one other trusted change: grpc-prometheus's
`ServerMetrics.UnaryServerInterceptor.wp_proof` returns also `⌜promUnaryIc ic⌝`, a predicate nothing else makes or
reads but the members' axioms: it names the value Go returns (the closure `interceptors.UnaryServerInterceptor(reporter)`
builds), and its docstring's transparency claim is unchanged.

**Call sites.** The proofs used the old axiom in the ghost step before the start (`grpcUp_noRefusal`, removed, and
five direct uses). The start happens inside `client.etcd_kv_started_with`, which now also returns
`etcdKVSrvAt addr s [il, im, iu]` (from `grpc.start'`'s `grpcServerAt`), as do `etcd_kv_started` and
`etcd_watch.wk_served_nd`; `kv_lease_served_core`, `kvWatch_served` and the new `etcdstart.kv_served_at` (`kv_served`,
unchanged, is its weakening) return `etcdKVSrv addr s`, with the chain's identity from `grpcUp`, which now carries
`v3rpc.Server`'s `etcdUnaryIcs`; each call site applies `etcd_noRefusal_at`/`_srv` after the start. No top-level
theorem's statement changed; the axiom sets per result are unchanged (a result that did not use the axiom still does
not: the started theorems return the facts, and only the old call sites apply the axiom).

## Attacks on the fixed statement

- **The reported route.** The axiom no longer applies: its premise is the server at `addrA`, which is `gs2`, and `gs2`'s
  configuration does not register etcd's KV service over `s` (`refuser`'s handlers are not `kvRegs q`). Once `gs` is
  started at some other address, the axiom speaks of that address.
- **Two servers at one address.** Needs two `grpcAddrIs addr _`, made only by `grpc.start` (each consuming a
  `netListenerAt l addr`, whose `addrClaim addr` is exclusive and given once per address by program start; not
  because an address is listened on once: see re-listening below) or `bridge.New`, which consumes `netListenerAt l a ∗ netAddrLeft a` of its own address (since 2026-11-24,
  `notes/axiom-review/bridge-addrleft.md`): a program cannot both start a server at `a` and bridge `a`.
  `grpcAddrIs_agree` is the axiom that says so; this review relies on it, as `isGrpcRpc` at an address does.
- **A bridge.** `bridge.New`'s `□ (∀ γ, grpcAddrIs addr γ -∗ grpcAddrIs a γ)` makes the axiom apply at the bridge's
  address `a` with etcd's `γ`: calls at `a` reach etcd's server unchanged, and a cut's errors are grpc's own (the
  bridge's spec already carries `noRefusalAt` from `addr` to `a`). No new instance.
- **Re-listening (`listen_au`).** After `grpc.start'` the address's protocols (`addrProto`, inside `grpcAddrAt`) are
  persistent, and with them `listen_au` lends the listening token: a second `net.Listen` at `addr` is possible in the
  logic (so "one `Listen` per address per run", as `grpcAddrIs_agree`'s and `InvNet.lean`'s docstrings said until
  this review, was false; they now say what holds: the claim, not the token, is spent once). Such a listener has no
  `addrClaim`, so no `grpc.start` or `bridge.New` can take it. It succeeds only with no listener open at `addr` (the net extension's `ListenStep`, D6: `sys` while one is
  open, as Linux's `EADDRINUSE`), and the started server's listener is never closed by the program: `grpc.start`
  consumes it, and no spec gives it back or stops the server (no `Server.Stop` spec; Serve's accept loop drops the
  link only on a non-temporary `Accept` error, which a loopback listener does not produce in the target
  configuration). If a stop that frees the address is ever specified, `grpcAddrIs` (and so this axiom, and every
  `isGrpcRpc` at the address) must become a fact about a server's lifetime: the same remark as `grpcAddrIs_agree`'s
  docstring. A re-listened raw server serving `addr` while etcd's listener is open is excluded the same way.
- **A server of the deployment** (`grpcServeTok`'s second disjunct, a member whose address the deployment set): no
  `grpcAddrIs` is made, so the axiom does not apply there.

- **Etcd's KV service behind another chain** (the first fix's residual, closed): see below.

## The residual of the first fix (closed)

**The interceptor chain was not read.** The first fix (`665f2f1efa`) named the KV registrations but not the server's
unary chain `c.ics`. A program could register etcd's own KV service over the member on a server of its own behind an
interceptor that answers every call with a refusal: `gs3 := grpc.NewServer(grpc.ChainUnaryInterceptor(refuseAll))`,
`RegisterKVServer(gs3, v3rpc.NewQuotaKVServer(s))` (`NewQuotaKVServer.spec`: `quotaKVServerAt q … s`;
`RegisterKVServer.spec`: `kvRegs q` among the registrations), started and served at `addrB`. That statement applied
(`grpcAddrIs addrB γ3`, `grpcSrvCfg γ3 c3`, `kvRegs q ⊆ c3.regs`) and `Put` at `addrB` is refused
(`examples/axiomcx/norefusal/`, `MainInterceptor`, `TestMainInterceptorPanics`: panics, 1/1 here, 5/5 on an
independent review): an interceptor's contract (`srvInterceptorOk`) allows any non-nil, non-handler error, which
`ErrGRPCNotSupportedForLearner` is (etcd's own interceptor returns it at a learner), so contracts cannot tell etcd's
chain from a refusing one.

**Closed** by option (a) of this review: the chain by identity (`etcdUnaryIcs`, above). `MainInterceptor` no longer
meets the premises: `c3.ics = [refuseAll]`, not `[il, im, iu]` with those three closures, and no spec makes
`isUnaryIc`/`isLogUnaryIc` of a closure other than the constructors' (they are equalities with their code over a
variable holding `s`) or `promUnaryIc` of anything but grpc-prometheus's. A program that chains etcd's three closures
over `s`, in that order and alone, runs etcd's chain over `s`, which the claim is about. Option (b) (interceptor
contracts bounding their own errors' descriptions, with the voter fact moved onto `IsLearner`) is not done; it would
shrink the axiom further.
