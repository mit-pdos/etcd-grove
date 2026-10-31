Title: A Txn of nested keys-only ranges bypasses --max-txn-ops and can crash the member

### What happened?

With `--max-request-bytes` 32 MiB and the default `--max-txn-ops` (128), on one member:

1. A client puts 4 keys of just under 32 MiB.
2. The client sends one `Txn` of nested txns, five levels deep (fan-outs 20, 20, 20, 20, 16), whose 2,560,000 leaves are keys-only ranges over all keys.
3. The member builds a reply of about 2^48 encoded bytes (peak RSS 12.8 GiB). With a 15 s election timeout (so that the client waits), the member panics sending it and exits (output trimmed):

```
panic: runtime error: makeslice: cap out of range
google.golang.org/protobuf/proto.MarshalOptions.marshal(...)
	google.golang.org/protobuf@v1.36.12/proto/encode.go:190
go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc.(*codec).Marshal(...)
	etcdserver/api/v3rpc/codec.go:22
google.golang.org/grpc.encode(...)
	google.golang.org/grpc@v1.84.0/rpc_util.go:818
```

With the default election timeout the client times out instead, and every member still builds the reply. This affects any client with write access, with `--max-request-bytes` of about 10 MiB or more (estimated; borderline at the default).

### What did you expect to happen?

The member should reject the `Txn` as having too many operations: 2,560,000 exceed `--max-txn-ops`.

### How can we reproduce it (as minimally and precisely as possible)?

The crash: [this program](https://github.com/mit-pdos/etcd-grove/blob/d1bafb95f3a2c7feabc376d921c9cfe013302c9e/examples/etcdbugs/keysonlyreply/repro_test.go) runs these steps (13 GiB of memory).

The operation limit: [`TestCheckTxnRequestNestedOps`](https://github.com/upamanyus/etcd/blob/fix/etcd-txn-keysonly-reply-alloc-panic/server/etcdserver/api/v3rpc/key_test.go#L70-L88) and [`TestV3TxnNestedTooManyOps`](https://github.com/upamanyus/etcd/blob/fix/etcd-txn-keysonly-reply-alloc-panic/tests/integration/v3_grpc_test.go#L265-L291) on branch [`upamanyus/etcd:fix/etcd-txn-keysonly-reply-alloc-panic`](https://github.com/upamanyus/etcd/tree/fix/etcd-txn-keysonly-reply-alloc-panic), off `main` (1573d5941), send 64 nested txns of 64 ranges each, accepted on `main`:

```
--- FAIL: TestCheckTxnRequestNestedOps (0.00s)
    key_test.go:86: expected "rpc error: code = InvalidArgument desc = etcdserver: too many operations in txn request", but got ""
--- FAIL: TestV3TxnNestedTooManyOps (0.19s)
    v3_grpc_test.go:289: err = <nil>, want rpc error: code = InvalidArgument desc = etcdserver: too many operations in txn request
```

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

The tests: `main` (1573d5941), go1.27.3 linux/amd64. The crash: an embedded member built from [249d76bea](https://github.com/upamanyus/etcd/commit/249d76bea78d0c8980251d5fa7b26c35ef21263a), whose code on this path is `main`'s.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The crash: one member, `--max-request-bytes=33554432`, `--heartbeat-interval=500`, `--election-timeout=15000`, otherwise defaults. The tests: `--max-txn-ops=128`.

</details>
