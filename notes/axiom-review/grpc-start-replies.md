# Review: `grpc.start` restated with the workload premise `grpcRepliesFit` (2026-10-31)

**Target.** `lean` at `1f700d2138` (branch `reply-size`, `notes/reply-size.md`; the user's approval:
`notes/decisions.md`, "The replies' size: a workload premise on `grpc.start`"):

- **`axiom grpc.start`** (`Proof/google_golang_org/grpc/InvGrpcServer.lean:262`): now takes
  `grpcRepliesFit →` first; makes `grpcServerAt`, `grpcStreamServerAt`, `grpcServeTok`.
- **`opaque grpcRepliesFit : Prop`** (`InvGrpcServer.lean:253`) and its docstring (`:216-252`):
  every reply a gRPC server of the run marshals encodes to at most `grpcReplyMax = 2^48`; the
  per-workload argument for the closed theorems; the known false case.
- The axioms it makes true, statements unchanged: **`grpc.serve`** (`InvGrpc.lean:765`),
  **`grpc.serveStream`** (`InvGrpcStream.lean:1043`), **`grpc.Server.Serve.wp_proof`**
  (`Server__Serve.lean`, spec `Spec/google_golang_org/grpc/Server__Serve.lean`).

Pins: grpc v1.84.0, protobuf-go v1.36.12, `github.com/golang/protobuf` v1.5.4, etcd fork
`249d76bea7` (`.lake/go-src/etcd`), k8s apiserver `v0.0.0-20261021221356-9c4ec15b8038`, go1.27.3.
The user asked in particular for attacks on the **Watch, Lease and Auth** replies.

## Verdict

**Survives.** No etcd handler that a closed theorem's program reaches produces a reply anywhere
near `2^48` encoded bytes, and the only amplification in etcd's replies is the known one (keys-only
ranges sharing the index's key slices: `issues/etcd-txn-keysonly-reply-alloc-panic.md`). The premise
can only be used as a hypothesis. Nothing reaches the serving facts without going through
`grpc.start`. grpc v1.84 has no other reply-side panic that the three axioms still exclude.

There is no counterexample and no new `issues/` file. Four inaccuracies in the docstring, none of
which makes the premise false of a closed theorem. Their corrections were **applied** on this branch
at the coordinator's request (docstrings and notes only, no statement changed; see "Applied
wording" below):

1. **The flat read-only bound leaves out the per-key encoding.** "at most that many copies of the
   stored keys" is not quite right. A keys-only `KeyValue` encodes its three revisions too.
   Measured with protobuf-go v1.36.12, a 1-byte key's entry in a `RangeResponse` is 11 bytes at
   revision 5, 17 bytes at `2^20` and 35 bytes at `2^63 - 1`. So the bound is `--max-txn-ops`
   times (Σ over the stored keys of their length plus at most 34). With few stored keys, as in
   every closed theorem, this is negligible. The "2 TiB of keys" threshold should be read as
   2 TiB of keys-only encodings.
2. **The workload list is incomplete.** It names linkv3p's `MainWatch` but not linkv3p's `Main`,
   which is a closed theorem (`linkv3p/Adequacy.lean`). Its workload is linkvtxn's
   (`linkvtxn.Apply`/`Gen`), run over three members through bridges. The list also omits
   cachekv's own requests: the `etcd/cache` library sends a whole-prefix `Get`, a count-only `Get`
   with limit 1, a watch with progress and created notifications, and `RequestProgress`. All of
   them are bounded.
3. **"A few kilobytes" undersizes the watch replies.** A watch reply can batch up to 1000 revisions
   (`watchBatchMaxRevs`), so in the watch examples a reply can reach tens of kilobytes. This is
   still nine orders of magnitude below `2^48`.
4. **"Every run of the theorem's program" means the program's own clients.** The members listen on
   loopback TCP ports, and a process outside the program could connect to one and send the
   issue's request. The adequacy theorems model no outside peer, so this is the scope of every
   closed theorem, not a gap in this axiom. Still, the docstring should say "the replies to the
   program's own clients' calls".

## Attacks tried

### 1. Using the premise other than as a hypothesis (none possible)

- `grpcRepliesFit` is an `opaque` constant of type `Prop`. The kernel never unfolds it, it has no
  `Decidable` instance, and erasure keeps `native_decide` from reaching it. Every one of the 42
  Lean files that mention it was grepped. Apart from its declaration, it appears only as
  `(Hrf : grpcRepliesFit)`, as `grpcRepliesFit →`, or in docstrings. No theorem concludes it or
  its negation, and no law, instance or definition relates it to anything else. `grpcReplyMax` is
  used in no statement.
- Its negation buys nothing either. A classical case split leaves the `¬` branch with no way to
  call `grpc.start`, so no serving fact is available there. A program that needs a server cannot
  be proved safe in that branch.
- No law turns a token back into `⌜grpcRepliesFit⌝`. `grpcServerAt`, `grpcStreamServerAt` and
  `grpcServeTok` are bare `axiom … : IProp GF` with no instance or law. The theorems that mention
  them only consume them (`grpc_serve_rpcs`, `grpc_serveStream_rpcs`, `ServedOn`, `AuthnServedOn`,
  v3rpc's `Results`).

### 2. Another route to the serving facts (none)

- Producers. `grpc.start` is the only axiom whose conclusion contains one of the three tokens. It
  is applied in exactly two places, `client/v3/Results.lean:2649` (`etcd_kv_started`) and
  `examples/authkv/MainServe.lean:92` (`ak_served_kv`), and each passes its own `Hrf` hypothesis.
- Serving facts. `grpcServes` and `grpcServesStream` come only from `grpc.serve` and
  `grpc.serveStream`, which consume the tokens. Every axiomatized `Spec/` file was checked for one
  that mentions a serving fact or token. `ClientConn.NewStream` consumes them. `Server.Serve`
  consumes `grpcServeTok`. `bridge.New` only transports `grpcServes`/`grpcServesStream` from
  `addr` to the bridge's address, and needs them as input. The bridge relays bytes and is not a
  gRPC server: it marshals nothing.
- Closed theorems. Every adequacy theorem that serves gRPC takes `(Hrf : grpcRepliesFit)`:
  putget, putget3, putgetc, linkvtxn, k8setcd3, watchkv, cachekv, linkv3p and linkv3p's
  `AdequacyWatch`. authkv takes it through `Main.spec`. kv and kvreconf do not use gRPC.
- Not done: `etc/tcb-report.py --roots`, which needs an up-to-date `lake build` of this worktree.
  The checks above are structural greps instead.

### 3. Watch replies (`serverWatchStream.sendLoop`, `v3rpc/watch.go:411-510`): no amplification

- **Event construction.** On the write path, `watchableStoreTxnWrite.End`
  (`mvcc/watchable_store_txn.go:22-45`) makes one event per change of the write transaction. A
  put's change holds the request's key and value, which `proto.Unmarshal` copied out of the raft
  entry. A delete's change holds the index's key, and each key is deleted once per revision. On
  the catch-up path, `kvsToEvents` (`watchable_store.go:457-477`) unmarshals a fresh `KeyValue` per
  backend record. protobuf-go copies bytes fields (`internal/impl/codec_gen.go:5418`,
  `append(emptyBuf[:], v...)`), and a Go check overwrote the input buffer after `Unmarshal` with
  the decoded key and value unchanged.
- **Per-watcher copies.** `newWatcherBatch` (`watcher_group.go:79-97`) gives every watcher its own
  `*mvccpb.Event` copy. Only the `Kv` is shared, across watchers, and it appears once per reply.
  So `sendWatch`'s `events[i].PrevKv = …` (`watch.go:444-452`, under the fork's
  "TODO(fuweid): do we still need copy here?") writes only that watcher's copy. There is neither
  a data race nor a leak into another watcher's reply.
- **Batching.** `eventBatch.add` (`watcher_group.go:39-62`) caps a reply at
  `watchBatchMaxRevs = 1000` revisions. On the synced path a notification holds exactly one
  revision, enforced by the panic check in `notify`, `watchable_store.go:484`. The victim path
  resends the same batch, and responses buffered for a watch ID not yet announced (`pending`) go
  out one by one.
- **`prev_kv`.** For each event, a fresh non-keys-only `Range` at `ModRevision - 1` returns a
  freshly unmarshalled `KeyValue`, so the reply's memory matches its size. No closed program asks
  for it.
- **Fragmentation.** `sendFragments` (`watch.go:609-`) only splits a reply, by
  `--max-request-bytes`; one oversized event is sent alone. No closed program asks for it.
- **Progress notifications and control responses** (created, canceled, `CompactRevision`) carry a
  header and a few integers. The cancel reason is `err.Error()` of a static etcd error.

So a watch reply's encoding is at most about the memory it references (events fresh or referenced
once, packed varints at most 1.25× their memory), and it fits Go's `2^47`-byte address space. In
the watch examples a reply holds at most 1000 one-key puts of the 5-byte keys `wk/kN` with 1-byte
values: tens of kilobytes.

### 4. Lease replies: no amplification, and no closed program sends one

- `LeaseTimeToLive` with `Keys` builds `[]byte(k)` copies of `Lease.Keys()` (`lease/lease.go:106-114`,
  `v3_server.go:651-657`): each attached key once.
- `LeaseLeases` returns IDs; Grant, Revoke and the keep-alive replies are fixed-size.
- No example calls a lease RPC. k8s' lease manager (`NewDefaultLeaseManagerConfig`) leases only
  objects with a TTL, and k8setcd3's `Create` passes TTL 0.
- `LeaseKeepAlive` (`v3rpc/lease.go:93-108`) can return while its `leaseKeepAlive` goroutine still
  calls `stream.Send` (`:147`): a send after the handler returned. In grpc v1.84 that `SendMsg`
  reaches `http2Server.write`, which returns `streamContextErr` for a stream that is done
  (`internal/transport/http2_server.go:1160-1170`). That is an error, not a panic. No closed
  program opens this stream.

### 5. Auth replies: no amplification

`UserGet` (`auth/store.go:597`), `UserList` (`:604-606`), `RoleGet` (`:669-671`) and `RoleList`
(`:679-681`) build their replies from records read and unmarshalled from the backend for that call,
each record once. `Authenticate` returns a short simple token. authkv's Auth calls (`UserAdd`,
`RoleAdd`, `RoleGrantPermission`, `UserGrantRole`, `AuthEnable`, and `Authenticate` from its
`Username` clients) all use literal arguments.

### 6. The rest of KV

A non-keys-only range unmarshals every value fresh (`kvstore_txn.go:141`). Put and DeleteRange
with `prev_kv` read through the same path. Count-only ranges carry no `KeyValue`. `RangeStream`
streams one range per page. A single keys-only range references each index key once
(`index.go:162-187`). The only sharing is keys-only ranges repeated in one reply, which is the
known issue. For the flat read-only form, see 8.

### 7. Each closed theorem's workload (the docstring's argument checked against the Go)

| program | requests (Go) | largest reply |
|---|---|---|
| putget, putgetc, putget3 | one `Put("k","v")`, one `Get("k")` (putget3 over three members) | one KV |
| linkvtxn, linkv3p `Main` | `Gen` (`linkvtxn.go:610-`): `Get`/`Put`/`Delete` of the workload keys with values `a`–`d`, `List` = `Get(k, WithRange(l))`, flat `Txn` of 1–3 point ops on distinct keys | the few workload keys |
| k8setcd3 | seed `Put`s; the k8s store's `Get`, `OptimisticPut` (`Create`/`GuaranteedUpdate`) and `OptimisticDelete`: flat point transactions. `getKeys` (keys-only) only after `EnableResourceSizeEstimation` (`etcd3/store.go:677,711`), which the program never calls | one object |
| authkv | literal Puts, Gets, ranges, three flat Txns and one nested Txn whose leaf is a Put, Deletes, Auth setup, two watches from revision 1 (`""` by root; `[lo,hi)` by `u`) | a watch batch of its few small writes |
| watchkv, linkv3p `MainWatch` | `Put`s of `wk/k0..2` with values `a`–`d`; one prefix watch from rev 1 with progress and created notifications | ≤ 1000 revisions of one small event each |
| cachekv | the same Puts; the cache's prefix `Get`, count-only `Get` with limit 1, prefix watch with progress and created notifications, `RequestProgress` | the prefix's few keys, or a watch batch |

No program sends a keys-only range other than through the APIs above (it never does), a nested
transaction of reads, `prev_kv`, fragmentation, or a compressed request. Compression would make
grpc compress the reply, and the program sends none. The parameters the theorems quantify over
(`clients`, `ops`, `nw`, `nops`, `sched`) only scale the number of small operations, and the
watch batch cap bounds a reply's size whatever they are.

### 8. The flat read-only `Txn` bound

`checkTxnRequest` (`v3rpc/key.go:202`) limits each branch to `--max-txn-ops` operations, and
`IsTxnReadonly` (`txn/txn.go:352`) admits only top-level `Range`s, which are served locally. Each
keys-only range returns every key of the index at its revision once. So the reply is at most
`--max-txn-ops × Σ_keys (len(key) + ≤ 34)` plus the headers. Non-keys-only ranges copy their
values, so their memory matches their size. The docstring's claim holds once the per-key encoding
is counted (inaccuracy 1). The examples run at the default quota with `MaxTxnOps 128` and a
handful of keys.

### 9. Other reply-side panics in grpc v1.84 below `2^48` (none)

- **The allocation bound is exact.** etcd's server uses `grpc.CustomCodec(&codec{})`
  (`v3rpc/grpc.go`), so the call path is `codecV0Bridge.Marshal` (`codec.go:69-75`) →
  `v3rpc.codec.Marshal` → golang/protobuf `proto.Marshal` → protobuf-go `marshal`
  (`proto/encode.go:184-194`) → `make([]byte, 0, growcap(0, size))`. `growcap(0, size)` is
  `size` (`:223-241`), and `makeslice` panics iff `size > maxAlloc = 2^48` (`runtime/slice.go:104`,
  `malloc.go:220`). So `grpcReplyMax` inclusive is the right threshold.
- **Size limits** after the marshal: `encode`'s `MaxUint32` check (`rpc_util.go:822`) and
  `maxSendMessageSize = MaxInt32` both return `ResourceExhausted`. A payload in
  `(2^31 − 6, 2^31 − 1]` passes the send limit and wraps `int32(len(hdr)+dataLen)` in
  `writeQuota.get` (`http2_server.go:1179`, `flowcontrol.go:54-67`). That only mis-accounts flow
  control, at worst a stall, with no panic. It is not reachable in the closed programs.
- **Size cache:** protobuf-go clears the `int32` size cache above `MaxInt32 − 1` and recomputes,
  so there is no truncated length. Invalid UTF-8 in a string field, or a mismatched size, makes
  `Marshal` return an error, which becomes `codes.Internal`, not a panic. A nil reply is skipped by
  `encode`, and a typed nil marshals empty. The codec's `v.(proto.Message)` holds for every
  generated reply type. `sentBytes.Add(len(b))` is never negative.
- **Status and metadata:** etcd sets no status details and no header or trailer metadata (grep of
  `SetHeader`/`SendHeader`/`SetTrailer`/`WithDetails`: only the gRPC proxy's adapter). An
  over-long header list fails `checkForHeaderListSize` with an error. `grpc-message` is
  percent-encoded.
- **Send after close:** the Watch handler closes the stream (`sws.close()`, `watch.go:233`), which
  waits for `sendLoop` (`wg.Wait`, `:665-669`). All of the stream's sends come from `sendLoop`, one
  goroutine, so there are no concurrent `SendMsg`s. For Lease, see 4.
- **Panics outside the reply path** (handlers, interceptors) are excluded by the handlers' proofs
  and the interceptors' own axioms, not by these three. They were not in scope.

## Applied wording

Applied on `axiom/grpc-start-replies` (2026-10-31) in `grpcRepliesFit`'s docstring and the
`InvGrpcServer.lean` header ("the replies to the program's own clients' calls"), and in
`notes/reply-size.md` and `notes/audit.md`'s replies'-size row. The Adequacy headers only name the
premise and repeat none of these claims, so they are unchanged. Checks after applying them: full
`lake build` green (11270 jobs); `etc/tcb-report.py --check` matches the baseline (769 axioms, 17
`sorry`s); all 43 collections `--check` pass; `etc/gen-interface.py etc/api/raft.txt --check
--layout`: no interface moved, 0 new layout violations. As first proposed:

In `grpcRepliesFit`'s docstring:

- After "Global, one for the run, not per server", add: "about the replies to the program's own
  clients' calls (the closed theorems model no outside peer; an outside client could send the
  request below)."
- Change "linkvtxn: point operations and one bounded range" to "linkvtxn, and linkv3p's `Main`
  (linkvtxn's workload over three members through bridges): …".
- Change "the watch examples (watchkv, cachekv, linkv3p's `MainWatch`): small literal prefixes" to
  "…: small literal prefixes, each reply at most 1000 revisions of one small put (cachekv's cache
  adds a prefix `Get`, a count-only `Get` and progress requests)".
- Change "at most that many copies of the stored keys … unless that limit times the stored keys'
  bytes passes it (at the defaults, 2 TiB of keys …)" to "at most that many copies of the stored
  keys' keys-only encodings (each key's bytes plus at most 34) … (at the defaults, 2 TiB of such
  encodings …)".

## Files

The report only. The Go check of point 1 and section 3 (`proto.Size` of keys-only `KeyValue`s, and
`proto.Unmarshal` not aliasing its input) was a throwaway test in the examples module, run at
go1.27.3 and removed. Its output:

```
rev 5: KeyValue 9 bytes, in RangeResponse 11 bytes (key 1 byte)
rev 1048576: KeyValue 15 bytes, in RangeResponse 17 bytes (key 1 byte)
rev 9223372036854775807: KeyValue 33 bytes, in RangeResponse 35 bytes (key 1 byte)
after overwriting the buffer: key "key" value "value"
```
