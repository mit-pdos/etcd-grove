# etcdserver: checkIntervals accepts a put in a nested txn and a delete of the key in a later sibling txn

- **Status**: open (not filed). Not a crash found; the check is inconsistent with itself.
- **Where**: `server/etcdserver/api/v3rpc/key.go`, `checkIntervals` (lines 236-315 at the
  pinned `bc8b52a50`, upstream `main` f061acd09 the same), called by `kvServer.Txn` on each
  branch ("check for forbidden put/del overlaps").
- **What happens**: `checkIntervals(reqs)` collects the level's deletes, then for each nested
  transaction in order checks its puts against `puts` and `dels` *so far* and only then unions
  its deletes into `dels`; the level's own puts are checked last. So a nested transaction's put of
  `k` is never checked against the deletes of a nested transaction *after* it. A transaction
  `Then(Txn(Then(Put(k))), Txn(Then(Delete(k))))` passes the check and runs a put of `k` and a
  delete of `k` in one revision, while the flat `Then(Put(k), Delete(k))` and the reversed
  `Then(Txn(Then(Delete(k))), Txn(Then(Put(k))))` are rejected with `ErrGRPCDuplicateKey`.
  Reproduction (a test in package `v3rpc`, run with `go test -overlay` from `server/`):

```go
package v3rpc

import (
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

func putOp(k string) *pb.RequestOp {
	return &pb.RequestOp{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(k)}}}
}
func delOp(k string) *pb.RequestOp {
	return &pb.RequestOp{Request: &pb.RequestOp_RequestDeleteRange{RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte(k)}}}
}
func txnOp(then ...*pb.RequestOp) *pb.RequestOp {
	return &pb.RequestOp{Request: &pb.RequestOp_RequestTxn{RequestTxn: &pb.TxnRequest{Success: then}}}
}

// A put in a nested transaction and a delete of the same key in a later sibling.
func TestProbeSiblingPutThenDelete(t *testing.T) {
	_, _, errFlat := checkIntervals([]*pb.RequestOp{putOp("a"), delOp("a")})
	_, _, errNested := checkIntervals([]*pb.RequestOp{txnOp(putOp("a")), txnOp(delOp("a"))})
	_, _, errNestedRev := checkIntervals([]*pb.RequestOp{txnOp(delOp("a")), txnOp(putOp("a"))})
	t.Logf("flat put;del: %v", errFlat)
	t.Logf("nested txn(put);txn(del): %v", errNested)
	t.Logf("nested txn(del);txn(put): %v", errNestedRev)
	if errNested == nil {
		t.Errorf("checkIntervals accepted a put in a nested txn and a delete of the key in a later sibling txn (flat: %v, reversed: %v)", errFlat, errNestedRev)
	}
}
```

  prints `flat put;del: ... duplicate key given in txn request`, `nested txn(put);txn(del):
  <nil>`, `nested txn(del);txn(put): ... duplicate key ...`.
- **How it happens**: at each level, `checkIntervals` checks a nested transaction's puts
  against the deletes collected so far, and only then adds that transaction's deletes. The
  example `Then(Txn(Then(Put(a))), Txn(Then(Delete(a))))`:

  1. The top level has no deletes of its own, so `dels` starts empty.
  2. The first nested transaction returns `putsThen = {a}`. `a` is not in `dels`, so it is
     accepted and added to `puts`.
  3. The second nested transaction returns `delsThen = {a}`, unioned into `dels`. Its puts are
     empty, so nothing is checked against the new delete.
  4. The level's own puts (none) are checked last. The function returns no error, and the
     transaction applies a put of `a` and a delete of `a` in one revision.

  ```go
  // server/etcdserver/api/v3rpc/key.go:258-297 (etcd main f061acd09)
  	// collect children puts/deletes
  	puts := make(map[string]struct{})
  	for _, req := range reqs {
  	// ...
  		putsThen, delsThen, err := checkIntervals(tv.RequestTxn.Success)
  	// ...
  		for k := range putsThen {
  			if _, ok := puts[k]; ok {
  				return nil, dels, rpctypes.ErrGRPCDuplicateKey
  			}
  			if dels.Intersects(adt.NewStringAffinePoint(k)) { // <- only deletes seen so far
  				return nil, dels, rpctypes.ErrGRPCDuplicateKey
  			}
  			puts[k] = struct{}{}
  		}
  	// ...
  		dels.Union(delsThen, adt.NewStringAffineInterval("\x00", "")) // <- added after
  		dels.Union(delsElse, adt.NewStringAffineInterval("\x00", ""))
  	}
  ```

  This order, put then delete, does no harm downstream as far as we found. mvcc writes the put
  at `(R, 0)` and the tombstone at `(R, 1)`, and the delete's range sees the put. The key index
  holds `{(R,0), (R,1)t}, {}`, so a read at `R` sees the key deleted, and compaction at `R`
  keeps the tombstone (`key_index.go`, `doCompact`). Watchers get a PUT then a DELETE at `R`.
  The reversed order, delete then put, is the one that corrupts compaction
  (`etcd-compaction-delete-then-put`), and the check rejects it.
- **Expected**: the check's documented purpose ("puts and deletes overlap for a list of ops");
  the same verdict for the two orders of the siblings, as for the flat case.
- **How the proof handles it**: `v3rpc.intervalsOkCheckStmt`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Defs.lean`), what `checkIntervals`
  gives the txn package's `NoDupKeysPerRev` (`keys_nodup_iff_check`), is stated with the premise
  `ReqOp.siblingSafeL` (no nested put deleted by a later sibling), beside `noFromKeyDelL`
  (`etcd-txn-delete-then-ignore-put`): it is false without it. Proved under both premises by
  the request path's unit 1 (`v3rpc.check_gives_nodup`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/CheckNodup.lean`), whose docstring names
  this issue.
- **Possible fixes**: check every nested transaction's puts against the level's final `dels`
  (a second pass over the collected puts after all unions), as the level's own puts are.
- **Found**: 2026-10-12, the request path's unit 0 (stating `checkIntervals`'s semantics in
  `Defs.lean`).
