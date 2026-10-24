# etcd-io/etcd#22616: tests and logs

The verification report is `notes/pr-verify/etcd-22616.md`. Revisions:
- PR head: `6cb3f6108d7598a675ad4e70251171f268c1c6a1` (`etcd-io/etcd` `pull/22616/head`)
- Upstream base: `22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4`
- Goose fork branch: `pr-etcd-22616-goose-lean` (`6be819cfe8d3a246d8b9869498d9095f2819e0ef`, onto pinned `goose-lean` `bc9c3868ced67e518fb2fecba44ce0fa70b7303b`)

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `range_sort_limit_test.go` | `TestRangeSortLimit` (from PR #22616): `txn.Range` with `SortTarget: CREATE`, `SortOrder: NONE`, and `Limit: 0, 1, 2` over keys `"c"`, `"b"`, `"a"` created in that order. On base, `limit 1` fails (`expected ["c"], actual ["b"]` because `rangeLimit` reads `limit + 1 = 2` keys `"a", "b"` in key order before sorting); on the PR head / fork branch, all cases pass. | PR head / fork branch, base | `cp range_sort_limit_test.go <etcd>/server/etcdserver/txn/ && cd <etcd>/server && GOTOOLCHAIN=go1.27.1 go test -v -count=1 -run '^TestRangeSortLimit$' ./etcdserver/txn/` |
| `range_sort_limit_head.log`, `range_sort_limit_base.log` | Output of `TestRangeSortLimit` on the fork branch (`pr-etcd-22616-goose-lean`) and on the base (`bc9c3868c`). | Fork branch, base | as above |
