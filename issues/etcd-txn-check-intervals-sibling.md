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
