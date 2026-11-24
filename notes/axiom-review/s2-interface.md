# Review: phase 7 S2's interface switch, `Server.Serve` and `ClientConn.Invoke` over a service table (2026-11-24)

**Target.** Branch `s2-switch` (off `lean` at `e7adfa1365`), option (A) of the design (dsverify-net, from
`origin/phase7-s2-core` `f361625701` and `origin/lean` `69adf61913`):

- **`axiom grpc.Server.Serve.wp_proof`** (`Proof/google_golang_org/grpc/Server__Serve.lean`; spec
  `Spec/google_golang_org/grpc/Server__Serve.lean`): `{{ grpcServeTok gs lis a Svc }} gs.Serve(lis) {{ err,
  True }}`, with `grpcServeTok` and `grpcServes` (`Proof/google_golang_org/grpc/InvGrpcRun.lean`). New (it
  was a theorem over the trusted model `Server.Serve.impl := model.Serve` and its four leaves' axioms,
  retired).
- **`axiom grpc.ClientConn.Invoke.wp_proof`** (text unchanged; its `isGrpcRpcsMd` premise now the heap-free
  `isGrpcRpcMd addr name Spec := ∃ a₀ …, grpcReach addr a₀ ∗ grpcSvcAt a₀ name Req.wire Rep.wire Spec`,
  `Proof/google_golang_org/grpc/InvGrpc.lean`).
- The trusted opaques they rest on: **`grpcCliPI`, `grpcSrvPI`** (`InvGrpcWire.lean`, on `lean` since
  `s2-vocab`), **`protoEncodes`** (`Proof/google_golang_org/protobuf/proto/Store.lean`, new, unused by the
  switch).
- Re-read beside them, text unchanged: `grpc.start`, `grpcAddrIs_agree`, `bridge.New.wp_proof`,
  `ClientConn.NewStream.wp_proof`.

Pins: grpc v1.84.0, protobuf-go v1.36.12, the model `models/grpc` (`model_transport.go`, `model_wire.go`) at
`phase7-s2-core` `f361625701`, go1.27.3.

## Verdict

- **`Server.Serve.wp_proof`: survives**, with two conditions built into the statement: the protocols of a
  grpc address are the **opaque** `grpcCliPI`/`grpcSrvPI` (C1, C2), and `grpcServes` has the clause
  **`name ∉ sregs.map Prod.fst`** (C3). Under `grpcRepliesFit` and the stream pair's argument (streams stay on
  the old pair until S3). With the defined protocols `grpcCliP`/`grpcSrvP` it is **false** (C1 against the
  model, C2 against real grpc-go); without the clause it is **false** (C3).
- **`ClientConn.Invoke.wp_proof` (new meaning): survives** with the opaque protocols. Conditions: no retry
  policy (`grpcResolverAt`), no foreign process on a grpc address (`addrsUnclaimed`, or the deployment's
  world), the registered message models. With the defined protocols **false** against real grpc-go (C2').
- **`grpcCliPI`, `grpcSrvPI`, `protoEncodes`**: trusted text with no law; nothing can produce or eliminate an
  opaque protocol's assertion, so they add no claim of their own beyond what the two axioms say through them.

C1, C2, C2' and C3 are refutations of the variants the design rejected, sketched below as programs and
proofs; they are not Go tests yet (a Go test and a Lean proof on an `axiom/s2-interface` branch are the
skill's evidence; not made here: the machine had no build capacity for a new translated project, and the
switch lands the amended statements, which block all four). They stay recorded as the reasons for the
statement's shape, and S2 must face them again when the protocols become definitions (F2 below).

## The claims

`Serve(lis)` with `grpcServeTok gs lis a Svc`:

1. Go's configuration `c` of `gs` is fixed: started (`grpc.start`'s `grpcSrvLink gs lis γ ∗ grpcAddrIs a γ ∗
   grpcSrvCfg γ c`) or being built (`grpcSrvNew gs c.ics c.sics svcs c.regs c.sregs ∗ netListenerOpen lis a`);
   its full names jointly distinct; `grpcRepliesFit`.
2. `a` serves `Svc` (`grpcAddrAt a Svc`: `addrProto a (grpcCliPI Svc) (grpcSrvPI Svc)`, set once from
   `addrUnset a`).
3. `gs` serves `Svc` (`grpcServes`): every entry names no stream; for each unary `(name, mh, srv) ∈ c.regs`
   with an entry `e`, `e = ⟨Req.wire, Rep.wire, Spec⟩` at registered `Req`, `Rep`, and `grpcRunOkMd #mh srv
   c.ics Spec` (the run contract: given the thread token, a later credit, the run's context, grpc's `dec` at
   `m`, the chain, and `Spec md m Φ Ψe` at the context's metadata, the run returns the token and `Φ m'` or
   `Ψe d`).
4. Post `True`; the axiom says every call accepted runs on a goroutine of its own as `Svc` says, every byte
   the server writes on a connection to `a` meets `grpcSrvPI Svc` given the dialer met `grpcCliPI Svc`.

`Invoke` with `isGrpcRpcsMd addrs method Spec` (inside `grpcInvokerOk`): an attempt dials some `a ∈ addrs`,
reaches `a₀` (`grpcReach`), converts `Spec md m Φ Ψe` to the entry's spec (`grpcSvcAt`'s update), writes as
`grpcCliPI` says, and on success returns `Φ m'` (that the server's protocol delivers, which `Serve`'s axiom
guarantees); an `Unavailable` dial error is not a handler's description.

## Attacks

### C1: `Serve` against the model, with the defined protocols (refuted the design's first draft)

With `grpcAddrAt a Svc := addrProto a (grpcCliP Svc) (grpcSrvP Svc) ∗ …`, `addrProto` is public through
`isGrpcRpcMd`/`grpcAddrAt`, so a raw goroutine may `dial_au` the address and write any bytes `grpcCliP`
allows. `cliRest`'s `rest = []` arm allows the preface and a head with no data frame.

```go
// examples/axiomcx/s2-c1 (sketch)
svc := grpc.NewServer()
svc.RegisterService(&grpc.ServiceDesc{ServiceName: "cx.S", HandlerType: (*any)(nil),
    Methods: []grpc.MethodDesc{{MethodName: "M", Handler: func(srv any, ctx context.Context,
        dec func(any) error, ic grpc.UnaryServerInterceptor) (any, error) { panic("ran") }}}}, struct{}{})
lis, _ := net.Listen("tcp", addr)
go svc.Serve(lis)
c, _ := net.Dial("tcp", addr)            // raw
c.Write(clientPreface)                   // the model's preface
c.Write(headFrame(":path", "/cx.S/M"))   // a head, no data frame
```

Lean: the table `Svc := fun n => if n = "/cx.S/M" then some ⟨…, fun _ _ _ _ => False⟩ else none` (the plan's
`grpcNoCall`); `grpcServes Svc` holds because the run contract at the spec `False` is vacuous (its pre holds
`grpcSpecAt False …`). The raw writes meet `grpcCliP` (the head is well formed, `rest = []`). The model's
`handle(s)` starts the unary handler before any data frame (§0a), so the handler runs and panics; the axiom
says no thread panics. The same with a real spec and a handler that relies on a deposit fact before calling
`dec` (a metadata check): today's `grpcRunOkMd` hands over the deposit when the handler starts, which only
the dec-shaped contract (§0a) avoids.

**Blocked** by the opaque protocols: a raw writer cannot prove an opaque `P cn W` for any `W`.

### C2: `Serve` against real grpc-go, with the defined protocols (any table)

```go
c, _ := net.Dial("tcp", addr)  // a raw reader of a real grpc-go server
b := make([]byte, 1)
io.ReadFull(c, b)
if b[0] != 8 { panic("not settingsBytes") }
```

`grpcSrvP Svc cn W` says the server's bytes start with `settingsBytes = [8]` (the model's frame kind);
`accept`/`read_au` give the raw reader `□ protoPrefix (grpcSrvP Svc) cn W`, so the proof discharges the `if`.
Real grpc-go writes an HTTP/2 SETTINGS frame first, whose first byte (a 24-bit length's high byte) is `0x00`:
Go panics. **Blocked** by the opaque protocols: a reader learns nothing of `□ grpcSrvPI Svc cn W`.

### C2': `Invoke` against real grpc-go, with the defined protocols

A raw program listens at the address first (`listen_au`, from `addrProto`), accepts the verified client's
connection, reads 25 bytes and checks byte 24 is `frameHead = 1` (`grpcCliP`'s head after the 24-byte
preface). Real HTTP/2 writes a SETTINGS frame there (`0x00`). **Blocked** as C2.

### C3: a table entry naming a stream (refuted a `grpcServes` without the stream clause)

Go's dispatch looks up the path in the unary methods, then the streams (`server.go`, `handleStream`): a
unary call (`Invoke`) of a name registered only as a stream runs the stream handler, whose `ServerStream`
the handler then uses. With `Svc name = some e` for a stream's `name`, `grpcServes` asks nothing of the
unary handlers (there is none), so it holds; `Invoke` at `e` deposits a unary call; the server runs the
stream handler on a stream deposit no client made (its stream registration's `isGrpcStreamAt` facts
fabricated from nothing): the handler's `RecvMsg` contract fails, and a handler that checks what it
receives panics.

```go
// a stream-only service "/cx.S/W" whose handler panics unless its first RecvMsg gets a CX
// message; a client Invokes "/cx.S/W" with any request (the codec sends it as the first message)
```

**Blocked** by `⌜name ∉ sregs.map Prod.fst⌝` in `grpcServes`.

### Attacks that fail (with the opaque protocols)

| Attack | Outcome |
|---|---|
| A handler run twice | Blocked: one stream per connection; transparent retry only of a refused, undispatched stream; no retry policy (`grpcResolverAt`) |
| A reply to the wrong call | Blocked: per connection (the protocols take the connection number `cn`) |
| A deposit without a successful `dec` | Blocked: `Invoke` gives up the deposit in its pre and only its attempt writes heads, so one run at most; on a decode failure the handler gets the deposit and its `dec` errors |
| A refused connection loses the deposit | Allowed by the spec (`Invoke`'s post never returns it): no unsoundness |
| Metadata mismatch | Unchanged: `grpcAttemptMd`, `ctxInMD` |
| Two servers at one address | Blocked: `grpcAddrAt` is set once (`addrUnset` is exclusive); one open listener at a time; in the started case `γ` is unique (`grpcAddrIs_agree`) |
| `Serve` before listening | Blocked: needs `grpc.start`'s link or the open listener |
| Wrong message types for an entry | Blocked: the registry's models (`grpcServes`' registry facts) and `e = ⟨Req.wire, …⟩`; across heaps the `pb*T_reg` axioms fix the same model, and `tree` is in the wire part |
| An entry with no registration | `Unimplemented`, not a handler's description (`handlerDescs`) |
| A bridged address | Relayed: `bridge.New`'s trusted wand gives `grpcReach`; only `bridge.New` makes such wands |
| A heap-dependent table on a client machine | Impossible: only an `addrUnset` holder sets a table, and a client machine has none for a member's address |
| A raw forwarder moving facts between connections | Blocked: the protocols are per connection number `cn` and opaque |
| Cross-world entailment (the skill's check) | None: no law gives a pure fact about an opaque function of a pointer |

Not tried: anything that needs a `Stop`/`GracefulStop` spec (none exists).

## Findings for S2

- **F2.** S2 cannot retire the world premise D7's wire half as the plan's §1.2(c) says: once the protocols
  are definitions, a program that copies the model's client code gets a proof and talks model frames to real
  HTTP/2. S2 needs a stated premise: no code but grpc's (and the trusted bridges) touches a grpc address's
  connections.
- The run contract `grpcRunOkMd` hands the deposit over when the handler starts; that is sound only with the
  opaque protocols (C1). When the protocols become definitions, the contract must hand it over through
  `dec` (§0a), which changes every `grpcServes` proof, etcd-dist's included.
- `grpcAddrIs_agree` needs no second grpc server at an address after the first's listener closes; true today
  only because nothing specifies closing a served listener. Restart's S10 should note it.
