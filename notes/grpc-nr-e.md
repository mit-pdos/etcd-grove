# grpc's no-refusal flag (option E, 2026-11-27)

Approved by the user (packet `etcdsvc-grpc-nr-packet`, option E). Ledger:
`notes/specs-only/ledger.md`, 2026-11-27. Branch `grpc-nr-e/2026-11-27`.

## The change

A unary entry of a service table says whether its method never refuses (`GrpcEntry.nr : Bool`). Three
pieces of trusted text use the flag:

1. **Server obligation.** `grpcServesEnt` (`InvGrpcRun.lean`): a flagged entry's handler meets
   `grpcRunNRMd` in place of `grpcRunOkMd`. `grpcRunNRMd` is the same run contract, with one more
   conjunct in the post: `⌜err = nil⌝ ∨ notDescIn refusalDescs err`.
2. **Client contract.** `grpcInvokerOk` (`InvGrpc.lean`; `ClientConn.Invoke`'s axiom): the error arm
   gains `isGrpcRpcsNR addrs method -∗ ⌜d ∉ refusalDescs⌝`. The `noRefusalAt` clause stays until it is
   retired.
3. **grpc's `dec`.** `grpcDecOk` (`InvGrpcBase.lean`; given to a run by `Server.Serve`'s axiom): the
   error arm gains `notDescIn refusalDescs err`. Without it no handler could meet (1), because the
   generated handler returns `dec`'s error unchanged.

New definitions, with no axiom and no opaque:
- `grpcSvcNRAt a name` (`InvGrpcWire.lean`, sealed): `∃ Svc e, grpcAddrAt a Svc ∗ ⌜Svc name = some (.unary e) ∧ e.nr = true⌝`.
- `isGrpcRpcNR` (sealed) and `isGrpcRpcsNR` (`InvGrpc.lean`), shaped like `isGrpcRpcMd`/`isGrpcRpcsMd`.
- The laws `grpcSvcNRAt_of_addr`, `isGrpcRpcNR_of_addr` and `grpcRunNRMd_ok` (an NR run contract is a run contract).

`grpcSvcAt` gains `∃ nr`, so a registration stays independent of the flag.

Every existing entry is unflagged (`nr := false`): `grpcGoEntry`, and the gRPC driver's `drvSvc` and
`drvSvcG`. Their obligations are the old ones.

## Why it is sound (grpc-go v1.84.0)

- **(1) is an obligation.** Whoever serves a table proves it for a flagged entry. The run is
  `methodHandlerCall mh srv ctx dec ui`: the generated handler, grpc's `dec`, and the server's composed
  interceptor `ui` over the chain `ics` (`grpcSrvChainAll`). So an interceptor's early error is
  covered, for example etcd's learner refusal (`v3rpc/interceptor.go:54`). No separate
  `srvInterceptorOk` clause is needed. A prover of a flagged entry shows that its interceptors return
  no refusal; `srvInterceptorOk` lets an interceptor return any `notHandlerErr`, so such a proof needs a
  stronger fact about that interceptor.
- **(3) `dec`.** `dec` is `serverStream.RecvMsg` (`server.go:1283`). Its errors are grpc's own
  (`stream.go:1921-1969`, `rpc_util.go:1064`):
  - the two cardinality violations;
  - `"unexpected EOF"`;
  - `toRPCErr` of `recv`'s errors (transport and context messages);
  - `"grpc: failed to unmarshal the received message: …"`.

  None of these is one of etcd's four refusal strings (`"etcdserver: …"`) or the old balancer's two
  (absent from grpc v1.84's sources, `InvGrpc.lean`'s `grpcInvokerOk` doc).
- **(2) the client.** If every address the connection may use has a flagged entry for the method, then
  every error the attempt returns is one of these:
  - a status the server sent: from a flagged run, which (1) bounds, or grpc's own server errors, which
    carry grpc's text. grpc forwards `grpc-status` and `grpc-message` unchanged.
  - an error grpc's client makes, with grpc's text.

  A bridge's address serves its target's table (`InvGrpc.lean` header), so the flag is about the
  target's server. With `addrs = []` the clause says the same as the existing `noRefusalAt` clause,
  which is vacuous there too.

The relay of S3.1 (`InvGrpcCallLib.lean`) is not changed. Its `trailerEnd` records only handler
descriptions, and nothing links it yet (`grpcAddrAt` still uses the opaque `grpcCliPI`/`grpcSrvPI`).
When S3.2 proves `Invoke`/`Serve` over the model, it must carry "flagged ⇒ not a refusal" from the
run's result to the trailer: `unaryParams.fin` with `e.nr`, through `callAdmits`.

## Trusted declarations, before → after

`GrpcEntry`: the field `nr : Bool` is added after `spec`.

`grpcSvcAt` body:
```
-- before
∃ Svc Spec₀, grpcAddrAt a Svc ∗ ⌜Svc name = some (.unary ⟨Wq, Wp, Spec₀⟩)⌝ ∗ □ ∀ md m Φ Ψe, Spec md m Φ Ψe ==∗ Spec₀ md m Φ Ψe
-- after
∃ Svc Spec₀ (nr : Bool), grpcAddrAt a Svc ∗ ⌜Svc name = some (.unary ⟨Wq, Wp, Spec₀, nr⟩)⌝ ∗ □ ∀ md m Φ Ψe, Spec md m Φ Ψe ==∗ Spec₀ md m Φ Ψe
```

`grpcServesEnt`, unary clause, inside `∀ mh srv, ⌜(name, mh, srv) ∈ regs⌝ -∗`:
```
-- before
∃ Req Rep Spec, ⌜… ∧ e = ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, Spec⟩⌝ ∗ grpcRunOkMd #mh srv ics Spec
-- after
∃ Req Rep Spec (nr : Bool), ⌜… ∧ e = ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, Spec, nr⟩⌝ ∗
  if nr then grpcRunNRMd #mh srv ics Spec else grpcRunOkMd #mh srv ics Spec
```

`grpcRunNRMd` is new. It is `grpcRunOkMd`'s triple, and its post adds
`∗ (⌜err = GoInterface.nil⌝ ∨ notDescIn refusalDescs err)`.

`grpcInvokerOk`, the error arm after `descIs err d`:
```
-- before
⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) → d ∉ refusalDescs⌝ ∗ (⌜d ∈ handlerDescs⌝ -∗ Ψe d)
-- after
⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) → d ∉ refusalDescs⌝ ∗
(isGrpcRpcsNR addrs method -∗ ⌜d ∉ refusalDescs⌝) ∗ (⌜d ∈ handlerDescs⌝ -∗ Ψe d)
```

`grpcDecOk`, the error arm (and `grpcDecOk_ty`, which restates it):
```
-- before
notHandlerErr err ∗ statusErrOk err
-- after
notHandlerErr err ∗ statusErrOk err ∗ notDescIn refusalDescs err
```

`grpcGoEntry`: the entry is unchanged, with `false` added as its flag.

## Retirement plan

Stage B′ defines `etcdSvc`. Its auth-off KV entries are `nr := true`, and `Serve_dist` proves (1) for
them, interceptors included, with a member being a voter. Then:

- **`noRefusalAt` and `noOtherRefusalAt`** (opaques, `InvGrpc.lean`) retire. Their readers move to
  `isGrpcRpcsNR`, which a client gets from `etcdSvc`'s registrations through `isGrpcRpcNR_of_addr`.
  `grpcInvokerOk`'s `noRefusalAt` clause is then deleted.
- **`etcd_noRefusal` and `etcd_noOtherRefusal`** (axioms, `v3rpc/NoRefusal.lean`) retire with them.
  What they assume becomes (1), proved of etcd's KV handlers and chain.
- **`grpcSrvAtLis`** (axiom, `InvGrpcServer.lean`) retires. It only binds a server to its listener for
  the `noRefusalAt` certificate, so `grpcServeTok`'s disjunct goes.
- **S3.2** carries the flag over the wire (above), and the trusted clause (2) then becomes a theorem
  of `Invoke`'s proof.
- **Model gap for the proof of (1)** (stage B′ review, 2026-11-28): `Serve_dist` asserts (1) for an
  auth-off member, true of Go because a member stays a voter (`notes/etcdsvc-b.md`). A proof of
  `grpcRunNRMd` for etcd's handlers needs that fact in the server's invariants: today
  `membership.IsLearner.spec` returns any boolean, so the interceptor's learner branch
  (`v3rpc/interceptor.go:54`) is not excluded by the model. The fact to add: the local member's
  membership record has `IsLearner = false` for the whole run (initial members are voters, conf-change
  validation never demotes, `MemberUpdate` keeps it false).
