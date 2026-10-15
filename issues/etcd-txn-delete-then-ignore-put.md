# etcdserver: a txn that deletes from a key on and then puts it with IgnoreValue panics every member, permanently

## Summary

A transaction that deletes every key from `k` on (`DeleteRange{Key: k, RangeEnd: "\x00"}`, i.e. `clientv3.OpDelete(k, clientv3.WithFromKey())`) and then puts `k` with `IgnoreValue` or `IgnoreLease` passes the gRPC layer's checks, is committed, and then panics the apply loop of every member with `index out of range [0] with length 0`. The entry is in every member's WAL and the consistent index is not persisted past it, so a restarted member applies it again and panics again: the cluster stays down. Any client allowed to write `k` can do this with one request. I found this while formally verifying etcd's `txn` package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `kvServer.Txn` (`server/etcdserver/api/v3rpc/key.go:118-137`) calls `checkIntervals` (`key.go:236-315`) on each branch, which rejects a put that overlaps a delete of the same transaction (`ErrGRPCDuplicateKey`). It builds a delete's interval as `adt.NewStringAffineInterval(Key, RangeEnd)` (`key.go:251`). A from-key delete has `RangeEnd` `"\x00"` (`client/v3/op.go:445-453`), which the server reads as "every key from `Key` on" (`mkGteRange`, `server/etcdserver/txn/delete.go:63`; the watch server, `watch.go:325-328`), but here it gives the interval `[Key, "\x00")`, which is empty and overlaps no put.
2. `txn.Txn` checks the puts of the chosen branch at the transaction's read view, before any operation runs (`server/etcdserver/txn/txn.go:54`, `checkTxn` → `checkPut` at `txn.go:214` → `checkAndGetPrevKV`, `put.go:90-102`): `k` still exists there, so the `IgnoreValue` put passes.
3. In the write transaction, `executeTxn` runs the operations in order: the delete removes `k`, then `getPrevKV` re-reads `k` (`txn.go:172`) and finds nothing, and `put` (`put.go:54-59`) indexes `prevKV.KVs[0]` of the empty list and panics, with the backend's batch lock held. In a server this is in the apply loop (`applyEntryNormal`, `server/etcdserver/server.go:1940`), for a committed entry, on every member.
4. On restart: the panic happens before the backend commits, so the backend's consistent index is that of an earlier entry, and the transaction's entry is in the WAL; the member replays it and panics again (below). `applyEntryNormal`'s deferred `SetConsistentIndex` (`server.go:1942-1949`) does run during the panic, but only in memory.

`IgnoreLease` instead of `IgnoreValue` panics the same way (`put.go:58`). A plain put of `k` after the from-key delete does not panic, but it is the overlap `checkIntervals` is meant to reject, and is rejected when the delete names `k` alone.

## How to reproduce

The branch below adds:

- `TestCheckIntervalsFromKeyDelete` (`server/etcdserver/api/v3rpc/key_test.go`): `checkIntervals` on a from-key delete with a put of the key, of a greater key, before the delete, in a nested transaction, a from-key delete in a nested transaction, a delete of every key (`Key: "\x00"`) — all must be rejected — and a put of a smaller key, plain and nested, which must be accepted.
- `TestTxnDeleteFromKeyThenIgnorePut` (`tests/integration/clientv3/txn_test.go`): through a client on a 1-member cluster, `Then(OpDelete("a", WithFromKey()), OpPut("a", "", opt))` with `WithIgnoreValue()` and `WithIgnoreLease()` fails with `ErrDuplicateKey` and leaves `"a"`; a from-key delete of `"b"` with an `IgnoreValue` put of `"a"` succeeds.

```
cd server && go test ./etcdserver/api/v3rpc/ -run TestCheckIntervalsFromKeyDelete -v
cd tests && go test ./integration/clientv3/ -run TestTxnDeleteFromKeyThenIgnorePut -v
```

On `main` (the fix's `key.go` reverted):

```
--- FAIL: TestCheckIntervalsFromKeyDelete/put_of_the_key
    key_test.go:107: checkIntervals: got <nil>, want rpc error: code = InvalidArgument desc = etcdserver: duplicate key given in txn request
(the same for put_of_a_greater_key, put_before_the_delete, put_in_a_nested_txn, delete_in_a_nested_txn, delete_of_every_key)

TestTxnDeleteFromKeyThenIgnorePut:
    PANIC  m0  execute job failed  {"member": "m0", "job": "server_applyAll", "panic": "runtime error: index out of range [0] with length 0"}
panic: runtime error: index out of range [0] with length 0 [recovered]
go.etcd.io/etcd/server/v3/etcdserver/txn.put(...)
go.etcd.io/etcd/server/v3/etcdserver/txn.executeTxn(...)
...
go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).applyEntryNormal(...)
FAIL  go.etcd.io/etcd/tests/v3/integration/clientv3
```

The panic in the `txn` package alone (a probe, not on the branch; next to `server/etcdserver/txn/txn_test.go`'s `setup`):

```go
func TestProbeDeleteThenIgnoreValuePut(t *testing.T) {
	s, lessor := setup(t, testSetup{key: []byte("a")})
	rt := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestDeleteRange{RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte("a"), RangeEnd: []byte{0}}}},
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("a"), IgnoreValue: true}}},
	}}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("Txn panicked: %v", r)
		}
	}()
	Txn(context.TODO(), zaptest.NewLogger(t), rt, false, s, lessor, false)
}
```

prints `Txn panicked: runtime error: index out of range [0] with length 0` (then hangs in its cleanup on the batch lock the panic left held; run with `-v -timeout 20s`).

What a restarted member does, with the binaries of `main` (`make build`): a 1-member and a 3-member cluster on fresh data directories, then

```
etcdctl put a v
printf '\ndel a --from-key\nput a --ignore-value\n\n\n' | etcdctl txn
```

The `txn` gets `Unavailable desc = error reading from server: EOF`; every member exits (status 2) with `panic: runtime error: index out of range [0] with length 0`. Restarting every member on its data directory (twice): every member exits again with the same panic, a few seconds after the election. In the 3-member cluster each member logs `restore consistentIndex ... "index":8` and `newRaft ... commit: 9, applied: 0, lastindex: 10`: the transaction's entry (index 10) is in each WAL, after the backend's consistent index, so it is applied again. A binary with the fix below panics the same way on those data directories: the fix keeps the entry out of the log, it does not make an entry already committed applicable.

## Expected

The transaction is rejected before it is proposed, with `ErrGRPCDuplicateKey`, as `Then(OpDelete("a"), OpPut("a", ...))` already is, or with `ErrKeyNotFound` as an `IgnoreValue` put of a missing key is. No request a client can send should crash the apply loop.

## The fix

Branch `txn-delete-then-ignore-put` (d9ba0e03c, one commit off `main` f061acd09, with the tests). `checkIntervals` reads a `RangeEnd` of `"\x00"` as "every key from `Key` on", the interval `[Key, "")` (the affine infinity), as `mkGteRange` and the watch server do; the transaction is then rejected with `ErrGRPCDuplicateKey`. This also rejects, by design, a plain put of a key at or after a from-key delete in the same transaction, which `main` accepts (and the same put after a point or bounded-range delete is rejected already). `checkIntervals` collects no range requests, so there is no read-side counterpart to fix.

Not in the fix: making `put` return `ErrKeyNotFound` instead of indexing an empty `KVs`. In the write path an error becomes `txn`'s `lg.Panic("unexpected error during txn with writes")` (`txn.go:91`), so it would change the panic's message, not the outcome, and it would not let a wedged cluster recover; the check has to happen before the entry is proposed.

The existing tests pass with the fix: `go test ./server/etcdserver/api/v3rpc/ ./server/etcdserver/txn/`, `go test ./integration/clientv3/ -run Txn`, `go test ./integration/ -run 'TestV3Txn|TestV3DeleteRange|TestV3PutOverwrite|TestV3RangeRequest'`.

(How the Lean proof handles it: the premise `IgnOk` of the transaction run; `notes/STATUS.md`, the `txn` unit 3 section. At the gRPC layer, `checkIntervals` reads a from-key delete as the empty interval: `v3rpc.check_gives_nodup` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/CheckNodup.lean`, the request path's unit 1) takes the premise `ReqOp.noFromKeyDelL`.)
