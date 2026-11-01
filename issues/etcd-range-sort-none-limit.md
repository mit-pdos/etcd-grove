---
upstream: reported
checked: 2026-11-01
links:
  - etcd-io/etcd#22612 issue open: this bug, reported 2026-10-19; a maintainer (Jefftree) agreed with the problem and fix 2026-10-21, doubting how often it is hit
  - etcd-io/etcd#22616 pr open: our fix, opened 2026-10-19
  - etcd-io/etcd#22615 pr open: a fix by someone else, an hour before #22616: makes IsDefaultOrdering false for a non-key target with NONE, which also fixes etcd-rangestream-sort-none; needs TestV3RangeRequest/sort updated
  - etcd-io/etcd#21326 pr merged: related (the same limit/sort logic, KEY/ASCEND); not this bug
  - etcd-io/etcd#6672 pr merged: related (2016: NONE with a non-key target sorts ascending); where the bug starts
blocks-proof: yes
---

# etcdserver: a range sorted by version, revision or value with no order and a limit returns the wrong keys

A `Range` sorted by a target other than the key (`VERSION`, `CREATE`, `MOD` or `VALUE`) with
`SortOrder: NONE` and a `Limit` returns the first `limit` key-values of a sort of the first
`limit + 1` keys of the range in key order, not the first `limit` key-values of the sorted range
(`etcdctl get a d --sort-by=VERSION --limit=1` without `--order`). With `--order=ASCEND`, which is
how the server reads `NONE` with such a target, the answer is right.

**Reproduction:** `TestKVGetSortNoneLimit` in
[`issues/etcd-range-sort-none-limit/kv_get_sort_none_limit_test.go`](etcd-range-sort-none-limit/kv_get_sort_none_limit_test.go),
copied (as `zz_kv_get_sort_none_limit_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (order 0 is
`SortNone`; `SortAscend` passes):

```
$ (cd tests && go test ./integration/clientv3 -run '^TestKVGetSortNoneLimit$' -count=1)
--- FAIL: TestKVGetSortNoneLimit (0.13s)
        	Error:      	Not equal:
        	            	expected: "c"
        	            	actual  : "b"
        	Messages:   	order 0
FAIL
```

## Proof

yes: the txn run and the client's get model take the premise that a get's sort is not cut early by
its limit (`cutEarly`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/TxnRun.lean`), which etcd does
not enforce.

## Fix

**Branch**: `fix/etcd-range-sort-none-limit` in `~/etcd-fixes/etcd-range-sort-none-limit` (upamanyus/etcd, pushed): 1f10b22ed test, 6cb3f6108 fix
**Base**: etcd-io/etcd@22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4

The PR is open (#22616).

## Notes

The user's plan (`INDEX-reviewed.md`): support #22615 over #22616, which also fixes
`etcd-rangestream-sort-none`; a comment for #22615 was drafted 2026-10-23 (not posted): prefer it,
note that it fixes `RangeStream`, and that `TestV3RangeRequest/sort` needs its last `RangeStream`
case expected unsupported (`[]bool{false, true, true, true, true, true}`). If #22615 merges, close
#22616.
