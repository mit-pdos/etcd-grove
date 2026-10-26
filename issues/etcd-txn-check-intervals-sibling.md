---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#16380 issue closed: same bug (put in an earlier nested txn vs delete in a later sibling passes; reversed order rejected); confirmed by ahrtr, closed not planned (stale) in 2025
  - etcd-io/etcd#16395 pr closed: fix for #16380, never merged (drafted, then closed stale); ahrtr found it too costly and questioned the expected semantics
  - etcd-io/etcd#22395 pr open: related, not this bug (checkIntervals and from-key deletes)
---

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
- **Possible fixes**: check each nested transaction's puts against the deletes of the
  transactions *after* it too, in a reverse pass over the level's nested transactions (see the
  2026-10-23 note below). Checking them against the level's final `dels` instead would be too
  strict: it would reject a then-put whose key the same transaction's else branch deletes, which
  the two mutually exclusive branches allow.
- **Found**: 2026-10-12, the request path's unit 0 (stating `checkIntervals`'s semantics in
  `Defs.lean`).

**A consequence for watchers** (2026-10-15, the watch slice's unit W-C): such a revision writes
`k` twice (a put, then a delete), so etcd's watch delivers, at that revision, a put event of `k`
whose key-value is not in the state at the revision, then the delete. A watcher contract that
says each event's key-value is (for a put) or is not (for a delete) in etcd's state at the
event's revision (`client/v3`'s `rangeWatchEvOk`, which the recipes and the cache rest on) is
false for it. The client's watch is verified under the premise `srvNoDupKeys` (every certified
log of the server writes each key at most once per revision, `txn.NoDupKeysPerRev`;
`Proof/go_etcd_io/etcd/client/v3/InvWatch.lean`), which the transactions of the recipes and the
cache meet (their transactions never put and delete one key): the premise is about other writers
to the same server.

**A simple fix** (2026-10-23, investigated at upstream `main` `3aaab3479`):

- *The old fix and its objections.* In #16380, ahrtr first proposed moving the unions before the
  put checks, and then one loop collecting every delete before any put is checked. bsbds pointed
  out that a nested txn's then-put may overlap its own else-delete, which rules out "every delete
  first". He then opened #16395 (+44/−17 in `key.go`), which checks every *pair* of sibling txns:
  for each pair (x, y), x's puts against y's deletes and y's against x's. ahrtr rejected it
  (2023-09-07): "too complicated and inefficient (e.g. triple loops)", O(T²·P·log D) for T sibling
  txns. He also judged the bug not critical, since Kubernetes does not use nested txns, and said
  "the key from putThen should be allowed to be overlapped with key range from delElse" (#16395
  already allowed that within one txn) and "we should clearly define & clarify the expected
  behaviour firstly". bsbds then wrote the constraints out (six of them). The bug is only his
  constraint 3: a put in txn X must not overlap a delete in another txn Y. He asked for a cheaper
  way to check it and got no answer, and both the issue and the PR went stale.
- *Proposed fix.* Keep the existing forward loop, which checks each nested txn's puts against the
  level's deletes and the earlier siblings' deletes. Record each nested txn's
  `(putsThen, putsElse, delsThen, delsElse)`, then add a reverse pass. It walks the nested txns
  from last to first with a tree `later` of the deletes of the txns after the current one. It
  checks the current txn's puts against `later`, then unions the current txn's deletes into it.
  The forward pass covers constraint 3 for X before Y, the reverse pass for X after Y, and neither
  compares a txn with itself, so then-put/else-delete stays allowed. The cost: each nested put is
  checked once more (O(log D)), and each nested delete is unioned once more. That is the same
  asymptotic cost as today, linear in the ops, against #16395's quadratic one. The diff is +25
  lines in `key.go`, no deletions. The branch is `txn-check-intervals-investigate`, worktree
  `~/etcd-fixes/txn-check-intervals-investigate`, commit `fc6254021` (+67 lines of
  `TestCheckIntervals`/`BenchmarkCheckIntervals` in `key_test.go`).
- *Tests.* `TestCheckIntervals` has 8 cases. Before the fix, 3 fail: put in a txn then delete in a
  later sibling; put then range delete in a later sibling; a doubly nested put then a later
  sibling's else-delete. After the fix all 8 pass, including the reversed order, the flat case,
  then-put/else-delete of one txn (allowed), and a key put in two siblings (rejected). The whole
  package (`go test ./etcdserver/api/v3rpc/...`) passes, and so do the integration tests
  `TestV3TxnDuplicateKeys|Revision|CmpHeaderRev|RangeCompare|NestedPath`.
- *Benchmark* (benchstat, n=6, a noisy 24-core machine; `flat` does not run the new code, so its
  +9.7% is the noise level): `flat` (128 puts, 128 deletes) 501µs → 549µs; `siblings` (64 nested
  txns, each 2 puts / 1 else-delete) 604µs → 797µs, +32%, allocs 1871 → 2456; `oneTxn` (one
  nested txn, 128 puts) unchanged. The cost, the second tree's inserts, is paid only by requests
  with two or more nested txns at one level.
- *Worth an upstream-report candidate?* Yes, as a follow-up on #16380, which a maintainer
  confirmed: this answers both objections (linear, not triple loops; then/else overlap kept) and
  makes the order-dependence visible in a table test. The impact stays low (put then delete in
  one revision is harmless downstream; see above).
