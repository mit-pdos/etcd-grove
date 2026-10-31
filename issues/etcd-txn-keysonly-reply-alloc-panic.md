---
upstream: unchecked
checked: 2026-10-31
links: []
---

# etcdserver: a Txn of nested keys-only whole-range reads builds a reply above 2^48 encoded bytes, and the gRPC codec's allocation panics the member (with `--max-request-bytes` ≥ about 10 MiB)

- **Status**: bug (a reachable panic of a member process, caused by one client request a client with
  read+write access can send). Reachable with a non-default but ordinary `--max-request-bytes`
  (10–32 MiB); borderline at the default (1.5 MiB). Reproduced end to end through `clientv3`.
- **Where** (the fork's `goose-lean`, `249d76bea7`; upstream `main` the same code; grpc-go v1.84.0,
  protobuf-go v1.36.12, `github.com/golang/protobuf` v1.5.4, which forwards to protobuf-go):
  - `server/etcdserver/api/v3rpc/key.go:202-231` (`checkTxnRequest`) budgets `maxTxnOps` **per
    nesting level**: each level is checked at `maxTxnOps - opc` and recurses into nested
    transactions (`checkRequestOp`, `key.go:324-335`), so a tree whose fan-outs sum to at most
    `maxTxnOps` (128) has (product of the fan-outs) leaf operations. `checkRangeRequest`
    (`key.go:153-167`) imposes **no key-length limit** and admits a keys-only whole-key range.
  - `server/storage/mvcc/index.go:162-187` (`treeIndex.Range`) and
    `server/storage/mvcc/kvstore_txn.go:88-106` (`storeTxnCommon.rangeKeys`, the `FastKeysOnly`
    branch): a keys-only range returns the index's own key slices (`keys = append(keys, ki.key)`,
    `index.go:181`) and builds a fresh `*mvccpb.KeyValue` per key with `Key: keys[i]` — no copy.
    `server/etcdserver/txn/range.go:67,156-172` sets `FastKeysOnly` and copies only the pointers
    (`asembleRangeResponse`). So every leaf range re-references the **same** key buffers.
  - `server/etcdserver/txn/txn.go:352-363` (`IsTxnReadonly`) inspects only the **top level**: a
    nested transaction's top-level ops are `RequestTxn`, not `RequestRange`, so a nested keys-only
    transaction is **not** classified read-only.
  - `server/etcdserver/v3_server.go:325-375` (`EtcdServer.Txn`): because it is not read-only, the
    transaction takes the write path (`raftRequest`, `v3_server.go:375,1013`), is marshalled into a
    raft entry and checked against `--max-request-bytes` (`v3_server.go:1099`), proposed, committed,
    and applied by every member's apply loop (`apply/apply.go:27`, `txn/txn.go:32,135` →
    `executeTxn`), which builds the reply. The gRPC handler waits for the apply result under
    `ReqTimeout = 5s + 2·election-timeout` (`config/config.go:314-318`,
    `v3_server.go:1059-1127`).
  - `server/etcdserver/api/v3rpc/codec.go:20-24` (`codec.Marshal` → `proto.Marshal`): when the
    handler receives the result and sends it, grpc's codec marshals it with protobuf-go, which
    allocates `proto.Size(m)` bytes with `make([]byte, len, growcap(0, size))`
    (`google.golang.org/protobuf/proto/encode.go:186-190`) **before** any size check. Go's
    `makeslice` panics when the capacity exceeds `maxAlloc` (2^48 on amd64).
    `server/etcdserver/api/v3rpc/grpc.go:36,74-75`: the server's gRPC receive limit is
    `MaxRequestBytes + 512 KiB` and the send limit is `MaxInt32`, but the send-limit check in
    grpc's `encode` (`rpc_util.go:818`) runs only after the allocation.
- **What happens**: a client puts a few long keys (one `Put` each, each key just under
  `--max-request-bytes`) and sends one `Txn` whose `Then` is a tree of nested transactions whose
  leaves are keys-only ranges over all keys (`["\x00", from-key)`, `WithKeysOnly`). The leaves'
  replies alias the same key buffers, so the reply's heap is modest (about 136 B per `KeyValue`
  struct plus the few key buffers) while its encoded size is `leaves · keys · key-bytes`, which can
  exceed 2^48. The member commits and applies the transaction (on every member), builds the reply
  in the apply loop, and panics marshalling it:

  ```
  panic: runtime error: makeslice: cap out of range
  google.golang.org/protobuf/proto.MarshalOptions.marshal(...) proto/encode.go:190
  github.com/golang/protobuf/proto.Marshal(...) proto/wire.go:23
  go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc.(*codec).Marshal(...) api/v3rpc/codec.go:22
  google.golang.org/grpc.encode(...) rpc_util.go:818
  google.golang.org/grpc.(*serverStream).SendMsg(...) stream.go:1842
  google.golang.org/grpc.(*Server).processRPC(...) server.go:1450
  ```

  (full stack: [`etcd-txn-keysonly-reply-alloc-panic/panic.txt`](etcd-txn-keysonly-reply-alloc-panic/panic.txt)).
  grpc-go installs no panic recovery around the handler goroutine (`server.go:1082-1087,1537-1595`),
  so the process exits. With auth off (the default) any client can send it; with auth on, a user
  with read+write permission on a range.

  A nuance of the timing. The transaction goes through raft, so the handler marshals the reply only
  if the apply loop finishes building it **within** `ReqTimeout`. With etcd's **default** timing
  (election 1 s, `ReqTimeout` 7 s) a reply large enough to exceed 2^48 takes longer than 7 s to
  build (about 2.1M leaf ranges at 32 MiB keys), so the client times out first
  (`etcdserver: request timed out`) and the handler never marshals — but the apply loop still builds
  and discards the multi-GB reply **on every member**, and **replays** it on every restart (the
  entry is in the WAL). The marshal panic itself fires once `ReqTimeout` exceeds the build time,
  which a wider election timeout (etcd allows up to tens of seconds for high-latency deployments)
  produces. Both the amplification and the crash follow from the same request.

- **Measured** (one member, `--max-request-bytes` 32 MiB, `--max-txn-ops` 128):
  - 4 keys of 33,553,408 bytes; `Txn.Then` a 5-level tree of fan-outs `20·20·20·20·16 = 2,560,000`
    leaf ranges (fan-outs sum 96 ≤ 128); the request marshals to about 30 MiB (about 12 B per leaf,
    under the 32 MiB + 512 KiB receive limit).
  - reply encoded size ≈ `2,560,000 · 4 · 33,553,408 ≈ 3.44·10^14 ≈ 2^48.29` bytes — above `maxAlloc`.
  - with the election timeout widened to 15 s (`--heartbeat-interval` 500 ms, `--election-timeout`
    15 s, so `ReqTimeout` 35 s) the member panics in `make` after building the reply; **peak RSS
    about 11–13 GiB** (well under the machine's 120 GiB), build time about 25–28 s.
  - estimates for other limits (reviewer's, unverified here): `--max-request-bytes` 10 MiB,
    ≈ 900k leaves over 40 keys, ≈ 5.4 GB heap; the default 1.5 MiB, borderline (≈ 2^48,
    ≈ 1.5 GiB of keys, ≈ 25 GB heap).
- **Reproduction**: `examples/etcdbugs/keysonlyreply/repro_test.go` (`TestKeysOnlyReplyPanic`),
  using the examples' Go module. It starts one member in a subprocess (so the member's panic does
  not take the test binary down), puts 4 keys, sends the nested keys-only `Txn` through `clientv3`,
  and checks the member's output for the `makeslice` panic:

  ```
  export PATH=/usr/local/go/bin:/root/go/bin:$PATH
  cd examples && KEYSONLY_REPRO=1 GOTOOLCHAIN=go1.27.3 \
    go test -v -run '^TestKeysOnlyReplyPanic$' -timeout 20m ./etcdbugs/keysonlyreply/
  ```

  Output of the committed run (2026-10-31): `PASS`; `Txn returned after 28.5s: err=... EOF`;
  `member exited: exit status 2`; `member's peak RSS: 12.82 GiB`; the member's stderr holds the
  `makeslice` panic above. `KEYSONLY_MAXREQ`, `KEYSONLY_FANOUT`, `KEYSONLY_TICKMS`,
  `KEYSONLY_ELECTION`, `KEYSONLY_LOG` override the configuration (package comment). The test is
  opt-in (`KEYSONLY_REPRO=1`): it needs about 13 GiB of memory and a minute.
- **Expected**: a request the gRPC layer accepts and the server proposes can be served; a reply too
  large to marshal should fail the call with `ResourceExhausted` (as grpc-go documents for a message
  over the send limit), not crash the member.
- **How the proof handles it**: the server axioms `grpc.serve` and `grpc.serveStream` are
  known-false for exactly this (`notes/audit.md:338`: the server's replies marshal through the same
  `codecV2.Marshal`, and nothing bounds the replies' size). The repair being drafted is an opaque
  workload premise `grpcRepliesFit` (a draft, not yet in code): a `Prop` that every reply grpc
  marshals under a workload is at most 2^48 bytes, discharged per workload (as `apply.backendUnderQuota`
  and `authRecordsFit` are), which is **false** of etcd's server under the client workload above and
  so must name this case. The same codec root cause on the **client** send side is
  [grpc-codec-alloc-before-size-check](grpc-codec-alloc-before-size-check.md) (there repaired by the
  encoded-size premise `Req.wireLen < 2^32` on `grpc.ClientConn.Invoke`/`NewStream`).
- **Possible fixes**:
  - grpc-go: check the encoded size against the send limit before allocating, or cap the allocation
    and let `MarshalAppend` grow it (same fix as the client-side issue).
  - etcd: copy the key in the keys-only branch (`kvstore_txn.go:90-106`) so the reply cannot alias,
    which turns the amplification back into an honest heap cost that the backend quota bounds; or cap
    a transaction's **total** leaf operations or total response size (not only per level,
    `checkTxnRequest`); or check the marshalled reply size before `SendMsg`.
  - Separately, `IsTxnReadonly` (`txn.go:352`) classifying a nested all-reads transaction as a write
    sends it through raft and the WAL, so a read-only-looking request mutates the log and is replayed
    on every restart; recognising nested read-only transactions would at least keep them off raft.
- **Found**: 2026-10-31, the `axiom` skill's review of the server reply-size axioms
  (`grpc.serve`/`grpc.serveStream`; the reply-size draft, finding 1), reproduced end to end.
