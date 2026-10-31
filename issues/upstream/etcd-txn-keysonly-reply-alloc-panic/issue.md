Title: A Txn of nested transactions exceeds --max-txn-ops many times over, and its reply can crash the member

<!-- Draft of a private report through https://github.com/etcd-io/etcd/security/advisories/new (etcd's security/README.md). Not filed. Ecosystem Go, package go.etcd.io/etcd/server/v3; affected: main (1573d5941), where keys-only ranges share the index's key buffers; release branches have the same unbounded operation count (memory, not this panic; not reproduced there). -->

### Summary

`--max-txn-ops` (default 128, "Maximum number of operations permitted in a transaction") is checked per nesting level, not over the whole request: a `Txn` whose `Success` holds nested transactions can contain far more operations than the limit, e.g. 64 nested txns of 64 ranges each, 4096 ranges, is accepted with the limit at 128. On `main`, the reply of keys-only ranges re-references the same key bytes for every range, so such a reply can be small in memory and yet encode to more than 2^48 bytes; marshalling it for gRPC then panics (`makeslice: cap out of range`) and the member exits.

### Details

With 4 keys just under `--max-request-bytes` (32 MiB) and one `Txn` of 2,560,000 nested keys-only ranges over all keys (the request is about 30 MiB), the member builds a reply of about 2^48.3 encoded bytes and panics when sending it (output trimmed):

```
panic: runtime error: makeslice: cap out of range
google.golang.org/protobuf/proto.MarshalOptions.marshal(...)
	google.golang.org/protobuf@v1.36.12/proto/encode.go:190
github.com/golang/protobuf/proto.Marshal(...)
	github.com/golang/protobuf@v1.5.4/proto/wire.go:23
go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc.(*codec).Marshal(...)
	etcdserver/api/v3rpc/codec.go:22
google.golang.org/grpc.encode(...)
	google.golang.org/grpc@v1.84.0/rpc_util.go:818
```

A nested txn is not treated as read-only, so it goes through raft and every member builds the reply when applying it. The panic is seen when the request timeout (5 s plus twice the election timeout) exceeds the time to build the reply (about 25 s here, with a 15 s election timeout); with the default timing the client times out first, and each member still builds and discards the reply, a peak RSS of about 13 GiB here.

### PoC

At `main` (1573d5941), `checkTxnRequest` accepts 4096 ranges with a limit of 128:

```go
func TestCheckTxnRequestNestedOps(t *testing.T) {
	rangeOp := &pb.RequestOp{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{
		Key: []byte{0}, RangeEnd: []byte{0}, KeysOnly: true,
	}}}
	nested := &pb.TxnRequest{}
	for range 64 {
		nested.Success = append(nested.Success, rangeOp)
	}
	txn := &pb.TxnRequest{}
	for range 64 {
		txn.Success = append(txn.Success, &pb.RequestOp{Request: &pb.RequestOp_RequestTxn{RequestTxn: nested}})
	}

	// 64 nested txns of 64 ranges each: 4096 ranges, more than 128 operations.
	err := checkTxnRequest(txn, 128)
	if getError(err) != getError(rpctypes.ErrGRPCTooManyOps) {
		t.Errorf("expected %q, but got %q", getError(rpctypes.ErrGRPCTooManyOps), getError(err))
	}
}
```

```
--- FAIL: TestCheckTxnRequestNestedOps (0.00s)
    key_test.go:86: expected "rpc error: code = InvalidArgument desc = etcdserver: too many operations in txn request", but got ""
```

An integration test sending the same `Txn` through gRPC gets a reply instead of `ErrGRPCTooManyOps`. The crash above was reproduced end to end with `clientv3` against one member, at a commit whose code on this path is the same as `main`'s (f061acd09 with two unrelated fixes), go1.27.3 linux/amd64, `--max-request-bytes` 32 MiB, `--election-timeout` 15 s. I can share both tests and a fix in the advisory's private fork.

### Impact

A client that can send a `Txn` (with auth enabled, a user with permission on the keys read) can crash the member serving it with one request, and make every member build a reply of many GiB. The crash needs `--max-request-bytes` of about 10 MiB or more and a request timeout longer than the time to build the reply; at the default 1.5 MiB the keys needed are about the default backend quota. etcd's `THREAT_MODEL.md` may class this as a robustness defect (an authenticated client, a non-default flag); I report it privately so that you can decide.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
