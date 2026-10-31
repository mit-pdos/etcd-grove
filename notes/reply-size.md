# The replies' size: a workload premise on `grpc.start` (2026-10-31, branch `reply-size`)

The repair of `grpc.serve` and `grpc.serveStream`, known-false since 2026-10-30 (`notes/audit.md`,
the row "the replies' size"): grpc v1.84 marshals a served reply before any size check, and the
codec's `make` panics above Go's `maxAlloc`; the axioms claimed serving never panics, whatever the
handler returns. The design (the reply-size draft, round 4, after three spec reviews) was approved
by the user on 2026-10-31, with four decisions; it is recorded in `notes/decisions.md`, "The
replies' size: a workload premise on `grpc.start`". This file records the change as built.

## State: done (one axiom restated, no new axiom, no new `sorry`)

## The Go at the pin

grpc v1.84.0, protobuf-go v1.36.12, golang/protobuf v1.5.4, go1.27.3. Unary and stream replies take
`prepareMsg` → `encode` → `c.Marshal` → `proto.Size`, then `make` (protobuf-go
`proto/encode.go:184-194`, `growcap(0, size) = size`; grpc's default codec
`internal/mem/buffer_pool.go:354-356`, page-rounded). `makeslice` panics iff the size passes
`maxAlloc = 2^48` (`runtime/malloc.go:213,220`), in `Serve`'s goroutines, unrecovered.

| encoded length of the reply | result |
|---|---|
| `≤ 2^31 − 1` | sent |
| `(2^31 − 1, 2^32 − 1]` | `ResourceExhausted` (`payloadLen > MaxInt32`; etcd's `MaxSendMsgSize`) |
| `[2^32, 2^48]` | `ResourceExhausted` (`encode`'s `MaxUint32` check) |
| `> 2^48` | **panic** in `make`, before any check |

Go's user address space on linux/amd64 is `2^47` bytes, so a reply that references each byte slice
and submessage a bounded number of times runs out of memory (outside the model) before its encoding
reaches `2^48`. A reply that references the same bytes many times can pass it.

**etcd's case** (`issues/etcd-txn-keysonly-reply-alloc-panic.md`, reproduced). A keys-only range's
`KeyValue`s share the index's key slices (`mvcc/index.go:181`, `kvstore_txn.go:88-106`);
`checkTxnRequest` bounds the operations per nesting level, not the tree. A `Txn` whose `Then` is a
tree of nested transactions with keys-only ranges at the leaves encodes to leaves × keys × key bytes.
- **Nested: not read-only.** `IsTxnReadonly` (`txn/txn.go:352-363`) checks only the top level, whose
  operations are transactions, so the request goes through raft, bounded by `--max-request-bytes`
  (`v3_server.go:1099`); every member builds the reply in apply; the member serving the client
  marshals it and panics. Measured: 4 keys under a 32 MiB `--max-request-bytes`, 2,560,000 leaves,
  `≈ 2^48.29` bytes, a 12.8 GiB member, the panic (with `ReqTimeout` widened above the build time;
  at the default timing the client times out first, the reply is built and discarded on every member).
- **Flat read-only** (`v3_server.go:325-351`): served locally after a linearizable read, without the
  proposal's `--max-request-bytes` check (only grpc's receive limit, `MaxRequestBytes + 512 KiB`),
  but one level holds at most `--max-txn-ops` ranges (128 by default), so its reply is at most that
  many copies of the stored keys: below `2^48` unless that limit times the stored keys' bytes passes
  it (2 TiB of keys at the default; the suggested maximum quota is 8 GiB).
- A single keys-only range does not amplify (its own key, `index.go:166-171`). Watch, Lease and Auth
  replies: no amplification (traced by the axiom review, `notes/axiom-review/grpc-start-replies.md`).

## What changed

- **The trusted statement** (`Proof/google_golang_org/grpc/InvGrpcServer.lean`): `grpcReplyMax :=
  2 ^ 48` and `opaque grpcRepliesFit : Prop` (its docstring: what it says, what makes it true, the
  closed theorems' workloads it is true of, what it is false of); `axiom grpc.start` takes
  `grpcRepliesFit →` first, its name unchanged. The file header gains "The replies' size".
- **Docstrings only**: `grpcServerAt` (`InvGrpc.lean`), `grpcStreamServerAt` (`InvGrpcStream.lean`),
  `grpcServeTok` ("exists only in a run satisfying `grpcRepliesFit`: made only by `grpc.start`"),
  and `grpc.serve`, `grpc.serveStream`, `grpc.Server.Serve.wp_proof` (the token comes only from
  `grpc.start`, under the premise). No law turns a token into `⌜grpcRepliesFit⌝`.
- **The start path** (`(Hrf : grpcRepliesFit)`): `client.etcd_kv_started` (`client/v3/Results.lean`),
  `etcd_cache_served` (`cache/v3/Results.lean`), `common.kv_served` (`examples/common/Served.lean`),
  `watchkv.wk_served` (`watchkv/Served.lean`), `authkv.ak_served_kv` (`authkv/MainServe.lean`).
- **`Spec/` files** (`grpcRepliesFit →` after `apply.backendUnderQuota →`): the `Main.spec` of
  putget, putget3, putgetc, linkvtxn, k8setcd3, watchkv, cachekv, authkv, linkv3p and linkv3p's
  `MainWatch`; linkv3p's `startMember` and `startCluster`; their proofs intro and pass it.
- **The closed theorems** (`(Hrf : grpcRepliesFit)` after `Hbuq`): the `Results`/`Adequacy` of
  putget, putget3, putgetc, linkvtxn, k8setcd3, watchkv, cachekv, linkv3p and linkv3p's
  `AdequacyWatch`; authkv's `authkv_Main` gains it through `Main.spec`. The Adequacy headers that
  list the named premises (putget's, putget3's, putgetc's; the others refer to them) name it.
- **Unchanged**: `common/Serve.spec`/`specOn`, `common/StartServer.spec`, `StartCompactingServer.spec`,
  `authkv/startServer.spec` (they never reach `grpc.start`), every served result and handler spec.
  Their headers (`client/v3/Results.lean`, `ServedOn.lean`, `AuthnServedOn.lean`,
  `v3rpc/Results.lean`) say the served results are conditional on the premise through the token.

## Departures from the draft

- The premise's docstring and the audit row follow the issue, not the draft's "read-only
  transactions are the largest": a nested all-reads transaction is not read-only and goes through
  raft; a flat read-only one is bounded by `--max-txn-ops`.
- `notes/audit.md` had no row for `grpc.Server.Serve.wp_proof`; one was added ("ok under
  `grpcRepliesFit`"), and `grpc.start` was split out of the row of `NewClient`/`NewServer`/
  `RegisterService`.
- `watchkv.wk_served` calls `etcd_kv_started` directly, not `etcd_cache_served`; both take the
  premise.

## Checks (2026-10-31, at `40a19922dd`)

- `lake build` (full): green, first try; no new warning.
- `etc/tcb-report.py --check`: the baseline unchanged (769 axioms, 17 `sorry`s): `grpc.start` keeps
  its name and the baseline records names only, and `grpcRepliesFit` is an `opaque`, not an axiom.
  The 43 collections `--check`: all pass, none updated. The restatement is recorded here and in
  `notes/audit.md`.
- `etc/api-check.py etc/api/raft.txt --check`: 0 errors; `etc/gen-interface.py etc/api/raft.txt
  --check --layout`: no interface moved, 0 new layout violations; `etc/gen-init.py --check`: clean;
  `etc/gen-link.py`: every Link identical (but the known lintest-logkvcompact/logkvsnap mismatch).
- The axiom review of the restated `grpc.start` and the premise's docstring (2026-10-31,
  `notes/axiom-review/grpc-start-replies.md`): **survives**. Watch, Lease and Auth replies do not
  amplify, and no closed workload comes near `2^48`. Four docstring inaccuracies were found, with
  wording proposed but not applied: the flat bound's per-key encoding, linkv3p's `Main` and the
  cache's own requests, "a few kilobytes", outside clients.
