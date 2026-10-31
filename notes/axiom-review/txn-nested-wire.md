# Review: the nested-transaction wire model of `*pb.TxnRequest` with `grpc.ClientConn.Invoke` (2026-10-30)

**Target.** Branch `txn-nested` (`4551e3f9c7` + `b45881b285` on `lean` `51b0f7adad`;
`notes/txn-nested.md`, Q4). Its D1/D2 changed no axiom's text, but the meaning of the axioms
instantiated at the trusted wire model `pbTxnRequest` (`client/v3/InvKVConn.lean:837`):

- **`grpc.ClientConn.Invoke.wp_proof`** (`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`, its
  attempt contract `grpcInvokerOk`, `InvGrpc.lean:947`): given `Req.send inp m`, an attempt returns
  the reply of the handler served for the method, run with grpc's `dec` at the *same* `m`
  (`grpcDecOk`, `InvGrpc.lean:310`: the decoded copy holds `Req.recv l m`), or an error. At
  `pbTxnRequest`: `send` is `txnReqAt` over `reqOpAt`/`reqOpsAt`, whose nested case was `False` and
  is now the nested `*pb.TxnRequest`, recursively (D1); `recv` is `txn.txnRequestIs ∗ txnWireOk`,
  whose delete facts now reach every depth (D2).
- **`grpc.serve`** (`InvGrpc.lean:741`): the server side registers the handler's
  `grpcMethodOkMd`, which takes `grpcDecOk` as given; it adds no claim of its own about the wire.
- `kVClient.Txn.wp_proof`, `retryKVClient.Txn`, `txn.Commit` (`Spec/.../kVClient__Txn.lean`,
  ...) are theorems over `Invoke` (`EtcdInvoke.lean`), not axioms; their meaning moves with it.
- Reached on the way (not in the change, but the claim "the server's decoding reproduces the
  client's tree" goes on to the raft entry): **`proto.MarshalIRR.wp_proof`**
  (`Spec/google_golang_org/protobuf/proto/MarshalIRR.lean`) with `pbutil.MustUnmarshalMessage.spec`.

Pins: etcd fork `249d76bea7` (grpc v1.84.0, protobuf-go v1.36.12, protoc-gen-go messages, no
gogoproto), Go `go1.27.3`.

**Since the review** (2026-10-31): both refutations are repaired on `lean`, as the user decided.
`Invoke`'s send side takes a generic encoded-size premise (`grpcMsgMax`, branch `invoke-size`,
`notes/invoke-size.md`; the issue `issues/grpc-codec-alloc-before-size-check.md`), and
`proto.MarshalIRR` takes the depth premise `apply.irrDepthOk rq`, discharged from `MaxTxnOps ≤ 4999`
on `NewServer` (branch `irr-depth`, `notes/irr-depth.md`; its own review
`marshalirr-depth.md` survives). The unknown-fields gap (attack 2) is still open: pinning
`unknownFields' = slice.nil` is deferred. This report landed on `lean` without the counterexample:
the program, its tests and `Attack.lean` (the "Files" below) stay on branch `axiom/txn-nested-wire`
(its Goose project would add to CI).

**Verdict.**

| claim | verdict |
|---|---|
| `Invoke` at `pbTxnRequest.send`: a request the model admits is sent (reply or error) | **refuted**, counterexample proved: shared operations make the encoding larger than `2^48` bytes and grpc's codec panics (`makeslice: len out of range`). Pre-existing: the flat `reqOpsAt` admitted it before D1 (nesting is not needed) |
| `Invoke` at `pbTxnRequest.recv`: the decoded copy denotes the client's `t` and has the delete facts at every depth | **survives** (the recursion limit gives an error, which the model allows); one gap outside translated code: unknown fields (below) |
| `proto.MarshalIRR`: the marshalled bytes of any `InternalRaftRequest` decode | **refuted on the Go side** (Lean proof not built): a 10001-deep request does not decode; reachable through the server with `--max-txn-ops` ≥ about 5000, an etcd bug: `issues/etcd-txn-nested-depth-apply-panic.md` |

## The counterexample (`Invoke` at `send`)

**The claim that is false.** `pbTxnRequest.send inp t` holds of any in-memory request whose
fields hold `t`'s operations read-only (`↦□`, `reqOpsAt` persistent), so operations may be shared:
the `Success` slice may hold `N` pointers to one `*RequestOp`, and the `*RangeRequest`s of
distinct `RequestOp`s may share one key slice (the client's own `Then(op, op, ...)` does: every
`toRequestOp` of an `Op` reuses `op.key`). Nothing bounds the size of `t`'s encoding. grpc encodes
before it checks the size against `MaxCallSendMsgSize`: `encoding/proto/proto.go:44-74`
(`codecV2.Marshal`): `size := proto.Size(vv)`; above the pooling threshold,
`mem.DefaultBufferPool().Get(size)`, which for a size beyond the largest tier makes a slice of that
length (`internal/mem/buffer_pool.go:356`, `make([]byte, size, allocSize)`); above Go's `maxAlloc`
(`2^48` on linux/amd64) `makeslice` panics with a runtime error. (With nesting, sharing doubles per
level, but the panic needs only `2^48 / keyLen` visits of `proto.Size`, nested or not.)

**The program**: `examples/axiomcx/txnwire/txnwire.go`, `Attack(ctx, cli)`: a `2^30`-byte key,
one `*RequestOp` holding a get of it, a `TxnRequest` whose `Success` holds it `2^18 + 1` times,
sent with `clientv3.RetryKVClient(cli).Txn(ctx, req)`. A read-only transaction of plain gets, so
the server's registered spec at it (`etcdTxnSpecOn`, read-only branch) asks only `txnModelIn` and
the caller's lower bounds.

**The test** (`txnwire_test.go`, `GOTOOLCHAIN=go1.27.3 go test ./axiomcx/txnwire -run 'TestAttack$'`,
an in-process member as `putget`'s; every run):

```
--- FAIL: TestAttack (0.06s)
panic: runtime error: makeslice: len out of range [recovered, repanicked]
google.golang.org/grpc/internal/mem.(*SimpleBufferPool).Get(0x194bc05ef9b0, 0x1000040480012)
google.golang.org/grpc/internal/mem.(*BinaryTieredBufferPool).Get(...)
google.golang.org/grpc/encoding/proto.(*codecV2).Marshal(...)
google.golang.org/grpc.encode(...)
google.golang.org/grpc.prepareMsg(...)
google.golang.org/grpc.(*clientStream).SendMsg(...)
google.golang.org/grpc.invoke(...)
go.etcd.io/etcd/client/v3.(*Client).unaryClientInterceptor.func1(...)
google.golang.org/grpc.(*ClientConn).Invoke(...)
go.etcd.io/etcd/api/v3/etcdserverpb.(*kVClient).Txn(...)
```

`TestAttackClientAPI` panics the same way through the public API alone:
`cli.Txn(ctx).Then(ops...).Commit()` with `ops` `2^18 + 1` copies of one `OpGet` of a `2^30`-byte
key (memory: the key twice, 2 GiB).

**The proof**: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/txnwire/Attack.lean`
(no `sorry`; the project `axiomcx-txnwire` of `etc/goose.py`, on this branch only):

```lean
abbrev Attack.spec : Prop :=
  ∀ (cl : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid c : w64) (n : Nat) (F : mvcc.Log) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit pkg_id.….axiomcx.txnwire ∗ clientKVAt cl [addr] ∗
      isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid) ∗
      committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗ ctxOk ci cd }}
    (@! ….Attack) #(GoInterface.ok ci) #cl
  {{ RET #(); True }}

theorem Attack.wp_proof (hRetry : RetryKVClient.spec) (hTxn : retryKVClient.Txn.spec) : Attack.spec
theorem Attack.wp_axioms : Attack.spec :=
  Attack.wp_proof client.v3.wp_RetryKVClient client.v3.retryKVClient.wp_Txn
```

The precondition is what the client's results take (`clientKVAt`, part of `clientv3.New`'s
`isNewClient`; the registration `etcd_kv_served_on` gives; `client_txn_on`'s lower bounds). The
proof builds `reqOpAt` of the get once, `reqOpsAt (replicate (2^18+1) p) (replicate … (.get o))` by
induction (`reqOpsAt_replicate`), the loop's slice of `2^18 + 1` copies, and discharges the
registered spec's read-only branch (`attackT_readonly`, `attackT_in`).

`#print axioms Attack.wp_axioms` (959 names): Lean's three; the gRPC vocabulary
(`grpcConn`, `grpcConn_persistent`, `grpcPeerOpt`, `grpcServes`, `grpcServes_persistent`,
`grpcWrotePeer`: opaque predicates of the boundary); the axiomatized types of the names-only
translations (`google_golang_org.*` 408, `net.*` 273, `crypto.*` 117, `etcdserverpb.*` 93,
`go_uber_org.*` 33, a few `strings`/`fmt`/`sync`/`internal`; their `underlying`/`zero_val`); and
the two claims **`grpc.ClientConn.Invoke.wp_proof`** and `grpc.StaticMethod.wp_proof` (a scalar
call option). `Attack.wp_proof` prints the same minus those two. No `sorry`, no other `.wp_proof`.

**What rests on it** (`.lake/tcb.json` of `txn-nested`): 126 results reach `Invoke`; among the
transaction's, `client_txn_any`, `client_txn_end_to_end`, `client_txn_on` (through
`txn.wp_Commit`, `retryKVClient.wp_Txn`, `kVClient.wp_Txn`), and the closed theorems over clients
(`linkvtxn_safe`, `k8setcd3_safe`, `putget*_safe`, `cache_safe`, `linkv3p_safe`, ...). The closed
theorems' programs send small requests, so their conclusions are not falsified; the client-level
triples are false as stated for a caller like `Attack`.

**Proposed restatement** (not applied; for the user). The request's encoded size must be bounded
where the sender establishes `send`, since memory does not bound it (sharing). Two options:

1. A size premise in the wire model: `pbTxnRequest.send inp t := ∃ req, inp ↦ req ∗ txnReqAt req t ∗
   ⌜txnEncLen t < 2 ^ 31⌝`, with `txnEncLen` the protobuf length of the model (or an opaque
   `encLen` with a monotonicity law: keys, values, operations), and the same field on `ProtoMsg`
   (`encOk : M → Prop`) for the other messages with repeated fields. `txn.Commit`'s callers then
   bound their keys and values (`client_txn_*` gain `txnEncLen (txnWireOf b.model) < 2^31`); the
   examples' requests are a few bytes. `2^31` is protobuf's own message limit; anything up to
   `2^48` is true of the panic, but sizes near memory are out-of-memory fatal errors, outside the
   model in any case.
2. Keep `send` and weaken `grpcInvokerOk` to "a reply, an error, *or* the size premise fails":
   not expressible as a WP (a panic is never allowed), so option 1.

Unknown fields (below) suggest adding `unknownFields' = slice.nil` to `reqOpAt`'s structs at the
same time.

## Attacks tried

1. **Protobuf's recursion limit on the server** (gRPC `codecV2.Unmarshal`, `proto.Unmarshal`,
   `protowire.DefaultRecursionLimit` 10000). Marshalling has no depth limit; a request 10002
   messages deep (a chain of 5000 nested transactions with a comparison at the bottom) is refused
   by the server's decoding: `rpc error: code = Internal desc = grpc: failed to unmarshal the
   received message: proto: exceeded maximum recursion depth` (`TestNestedDepthRefused`). An error
   with a status, not a refusal (`noRefusal` holds: its description is not one of
   `refusalDescs`), so `grpcInvokerOk`'s error branch and `txnCallOut` allow it; the server's
   handler never runs. **Fails** (partial correctness). The client's own retry interceptor does not
   retry it (a write, not a refusal).
2. **The decoded copy reproduces the client's tree** (`txn.txnRequestIs r t`). A shared nested
   `*TxnRequest` (a DAG) is encoded twice and decoded as a tree denoting the same `t`; a cycle
   cannot satisfy the finite `reqOpAt`; `RequestTxn: nil` and a `RequestOp` with no `Request` are
   excluded by `reqOpAt` (`r ≠ null`, one of the four cases); an empty `bytes` field (key, range
   end) is omitted on the wire and decoded `nil`, which `rangeReqAt`/`deleteReqAt` read by contents
   (`txn.rangeOpOf k e …` of the contents). **Survives**, with one gap out of reach of translated
   code: **unknown fields**. `reqOpAt` says nothing of a message's `unknownFields`; a Go client can
   set them with `m.ProtoReflect().SetUnknown(raw)` (public API), and marshalling appends them, so a
   `RequestOp` holding a get, with unknown bytes encoding field 2 (`request_put`), is decoded as a
   put (the last oneof field wins): `TestUnknownFieldsOverride`, "sent a
   `*etcdserverpb.RequestOp_RequestRange`; the decoded request holds a
   `*etcdserverpb.RequestOp_RequestPut`". Not a counterexample here: `ProtoReflect` and
   `SetUnknown` are not translated (the API is names-only for protobuf's plumbing), and every
   translated way to build a `RequestOp` leaves `unknownFields` `nil`. Pre-existing (the top-level
   operations too). Closing it would add `unknownFields' = slice.nil` to the sender's predicates.
3. **The `2^63` delete bound on the decoded side** (`txnWireOk`'s `delCountT … < 2^63`). The
   decoded copy is a fresh tree parsed from one buffer (at most the server's `MaxRecvMsgSize`,
   `MaxRequestBytes + 512 KiB`), each delete at least two bytes of it, at any depth. **Survives**.
   (On the client side the same count can exceed `2^63` with sharing, but `send` claims nothing of
   it, and the encoding would first hit attack 5.)
4. **Delete `RangeEnd` facts at every depth** (`delWiresAtT`). protobuf-go's proto3 `bytes` coder
   (`consumeBytesNoZero`) is the same at every depth: a zero-length field decodes to `nil`.
   **Survives**.
5. **Size: the encoding larger than any allocation.** **Succeeds** (the counterexample above).
   Note that it needs no nesting: D1 makes it cheaper (sharing doubles per level) but did not
   introduce it.
6. **Stack depth on deep trees** (marshal, decode, `checkTxnRequest`, `checkIntervals`, the
   permission checks, the apply). The depth reaching the server is at most 10000 message levels
   (attack 1) and the frames are small (34 KB requests at the boundary): no stack exhaustion; Go's
   stack grows to 1 GB, and exhausting it is a fatal error outside the model anyway. On the
   client, marshalling a 10^6-deep tree is bounded by `MaxCallSendMsgSize` only after encoding;
   not pursued (outside the model as memory exhaustion is). **Fails**.
7. **`MaxRequestBytes` / `MaxCallSendMsgSize`**: checked after encoding (client) or after decoding
   (server, `processInternalRaftRequestOnce`'s `ErrRequestTooLarge`), both errors. **Fails**.
8. **The server's checks recurse** (`checkTxnRequest`'s budget `maxTxnOps - opc` per level bounds a
   chain of one-operation transactions by about `--max-txn-ops`): with the default 128, nesting
   stays under 130 levels. With a raised `--max-txn-ops`: attack 9.
9. **The raft round trip** (beyond the gRPC boundary: the claim that what the server proposes can
   be applied). The server wraps the decoded request in an `InternalRaftRequest`, one message level
   more, and `apply.Apply` decodes it with the same limit and `pbutil.MustUnmarshalMessage`
   (panics). A request exactly 10000 levels deep passes gRPC and is proposed; its entry is 10001
   deep and does not decode (`TestDepthBoundary`: the 4999-chain decodes as a `TxnRequest`, its
   `InternalRaftRequest` gives `proto: exceeded maximum recursion depth`). End to end with
   `--max-txn-ops 10000` (`TestNestedDepthPoison`): `panic: unmarshal should never fail (proto:
   exceeded maximum recursion depth)` in `apply.Apply`; restarted from the same data directory
   (`TestNestedDepthPoisonRestart`), it panics again on replay. `proto.MarshalIRR.wp_proof` claims
   `apply.irrDecode bs = some rq'` for the bytes of *any* `InternalRaftRequest`, which is false of
   this one; `MustUnmarshalMessage.spec`'s premise is then met and excludes the panic. **Succeeds on
   the Go side**; the Lean counterexample (a program building a 5000-deep request, `proto.Marshal`,
   then `MustUnmarshalMessage`) is not built: it needs `apply.internalRaftRequestIs` of a nested
   `TxnRequest` built in a loop. The etcd bug: `issues/etcd-txn-nested-depth-apply-panic.md`.
   Restatement: `MarshalIRR`'s post `irrDecode bs = some rq'` only under a depth premise on `rq`
   (`irrDepth rq < 10000`, the decoder's limit), which the server's path then needs: either a
   premise on the configuration (`MaxTxnOps` below about 4990) or a depth check in etcd.

Not tried: the other `ProtoMsg` instances (Put, Range, DeleteRange requests hold one key and
value, no repeated field, so no sharing; the responses are built by the server) and the stream
messages (`Watch`).

## Files

- `examples/axiomcx/txnwire/`: `txnwire.go` (`Attack`), `txnwire_test.go` (`TestAttack`,
  `TestAttackClientAPI`), `depth_test.go` (`TestDepthBoundary`, `TestUnknownFieldsOverride`),
  `poison_test.go` (`TestNestedDepthPoison`, `TestNestedDepthPoisonRestart`,
  `TestNestedDepthRefused`).
- `Code/…/axiomcx/txnwire.lean`, `GeneratedProof/…/axiomcx/txnwire.lean` (project
  `axiomcx-txnwire`), `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/txnwire/Attack.lean`.
- `issues/etcd-txn-nested-depth-apply-panic.md` (with `INDEX.md`, `RANKING.md` rows).

Branch `axiom/txn-nested-wire` (off `txn-nested`), not pushed. A note for the proof: an `iframe`
or `dsimp` that touches `List.replicate 262145 _` makes the kernel unfold it (deep recursion,
memory); the proof keeps the literal lists syntactic (`rw` with `attackT_*` equations, `iexact`).
