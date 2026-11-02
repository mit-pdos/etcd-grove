---
upstream: none
checked: 2026-10-31
links:
blocks-proof: yes
---

# etcdserver: a Txn of nested keys-only whole-range reads makes every member build a huge reply, and the member that answers it panics (with --max-request-bytes of about 10 MiB or more)

A client puts a few long keys and sends one `Txn` whose `Then` is a tree of nested transactions
whose leaves are keys-only reads of every key. The member accepts it (the operation limit is
checked per nesting level, so the leaves are the product of the fan-outs), proposes it through
raft, and every member builds the reply in its apply loop: small in memory, since keys-only results
share the index's key buffers, but over 2^48 bytes encoded. The member serving the request then
panics marshaling the reply (`makeslice: cap out of range`) and exits. With the default timing the
client times out first, and every member still builds and discards the reply, again at every
restart (the entry is in the WAL).

**Expected:** a request the server accepts and proposes should be served; a reply too large to
send should fail the call (`ResourceExhausted`, as grpc does for a message over its send limit),
not crash the member.

**Impact:** a client with write access (any client with auth off, the default), on a member with a
non-default but ordinary `--max-request-bytes` of about 10 MiB or more (estimated; borderline at
the default 1.5 MiB). The crash needs the request timeout (5 s + 2 × the election timeout) to
exceed the time to build the reply (about a minute here): an election timeout of 15 to 30 s, as
high-latency deployments use.

**Reproduction:** `TestKeysOnlyReplyPanic` in
[`issues/etcd-txn-keysonly-reply-alloc-panic/keysonly_reply_test.go`](etcd-txn-keysonly-reply-alloc-panic/keysonly_reply_test.go),
copied into a new package directory `tests/integration/zzkeysonlyreply` at
etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5 (2026-11-02), go1.27.3 (one member in a
subprocess, `--max-request-bytes` 32 MiB, `--max-txn-ops` 128, a 30 s election timeout; 4 keys of
33,553,408 bytes, fan-outs 20·20·20·20·16 = 2,560,000 leaves; opt-in, about 11 GiB of memory):

```
$ (cd tests && KEYSONLY_REPRO=1 go test ./integration/zzkeysonlyreply -run TestKeysOnlyReplyPanic -count=1 -v -timeout 20m)
    keysonly_reply_test.go:277: Txn returned after 1m0.807590637s: resp=false err=rpc error: code = Unavailable desc = error reading from server: EOF
    keysonly_reply_test.go:296: member's peak RSS: 10.42 GiB
    keysonly_reply_test.go:301: member exited: exit status 2
        panic: runtime error: makeslice: cap out of range
        google.golang.org/protobuf/proto.MarshalOptions.marshal(...)
        	google.golang.org/protobuf@v1.36.12/proto/encode.go:190 +0x3cb
        go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc.(*codec).Marshal(...)
        	server/etcdserver/api/v3rpc/codec.go:22 +0x85
        google.golang.org/grpc.encode(...)
        	google.golang.org/grpc@v1.84.0/rpc_util.go:818 +0x4a
    keysonly_reply_test.go:304: the member crashed marshalling the reply (makeslice); it should have refused the request or failed the call
--- FAIL: TestKeysOnlyReplyPanic (115.75s)
```

(With a 15 s election timeout the same run timed out instead: `etcdserver: request timed out`
after 42 s, the member at 9.3 GiB.)

**Cause:** [`checkTxnRequest`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/api/v3rpc/key.go#L202-L231)
gives each nested transaction the budget its parent leaves, but every sibling gets the same budget,
so a tree whose fan-outs sum to at most `--max-txn-ops` has their product of leaves.
[`IsTxnReadonly`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/txn/txn.go#L352-L364)
looks at the top level only, so the nested reads go through raft and are applied by every member.
A [keys-only range](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/storage/mvcc/kvstore_txn.go#L90-L106)
returns the index's own key slices, so every leaf's result references the same key buffers. The
server's [codec](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/api/v3rpc/codec.go#L21-L25)
calls `proto.Marshal`, which allocates the encoded size before grpc's send-limit check, and the
allocation panics above 2^48 bytes; grpc does not recover the handler's goroutine.

## Proof

yes: it makes the property a top-level adequacy test over this code checks false for a workload such a test may use, and no fix is in the goosed fork yet; the proof sidesteps it: the server's gRPC replies are assumed to fit, the workload premise `grpcRepliesFit` of
`grpc.start` (`Proof/google_golang_org/grpc/InvGrpcServer.lean`, `notes/reply-size.md`), which is
false of etcd under this client.

## Fix

**Branch**: `fix/etcd-txn-keysonly-reply-alloc-panic` in upamanyus/etcd (pushed 2026-10-31): 511703d7b test, 7a63f2b96 fix
**Base**: etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef

**PR draft**:

Title: etcdserver: count nested txns' operations toward --max-txn-ops

[`checkTxnRequest`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/key.go#L202-L231)
checks `--max-txn-ops` per nesting level: each nested txn gets the limit minus its parent's
operations, but its siblings each get the same budget, so a txn of 64 nested txns of 64 ranges
passes a limit of 128. This PR counts the operations of every nested txn toward the limit; a
request with at most one nested txn per level is checked as before.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix,
makes it pass.

**If a reviewer asks**: copying keys in the keys-only branch removes the aliasing but turns the
panic into memory exhaustion on every member and costs a copy per key; checking the reply's size
before marshaling yields `ResourceExhausted`, but only after every member built the reply, and
leaves the limit bypassed; making `IsTxnReadonly` recursive keeps such requests off raft but bounds
nothing. With the fix, a reply is at most `--max-txn-ops` × the keyspace (2^40 bytes at 128 × 8
GiB), below the panic.

## Notes

Not a security report (the user's call, 2026-11-02): it needs an authenticated client, and etcd's `THREAT_MODEL.md` ("The Client-to-Server Boundary") counts crashes and memory exhaustion from an authenticated client's requests as robustness defects; it also needs non-default flags ("Non-Default & Test-Only Configuration"). File it as a normal issue.

The fix's tests (`TestCheckTxnRequestNestedOps`,
`TestV3TxnNestedTooManyOps`: 64 nested txns of 64 ranges accepted under 128) fail at the base
(2026-10-31). The fix is the change [`nonissues/etcd-max-txn-ops-nested`](../nonissues/etcd-max-txn-ops-nested.md)
calls documentation only: if this is filed, that one is its root cause. The same allocation in
grpc's own codec: [`grpc-codec-alloc-before-size-check`](grpc-codec-alloc-before-size-check.md).
