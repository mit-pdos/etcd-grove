---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#21595 pr open: touches the same lines (doSerialize's get returns its error); does not change this
---

# A read-only `Txn` that fails auth is recorded as a successful request

**Status**: a bug (a wrong metric and a misleading slow-request warning), not a safety problem:
the request fails as it should.

**Where**: `server/etcdserver/v3_server.go` at the pinned etcd revision (`09669450f`), the
read-only branch of `EtcdServer.Txn` (lines 351-372): the deferred function computes
`success := err == nil` over the closure variable `err` and passes `resp, err` to
`txn.WarnOfExpensiveReadOnlyTxnRequest`, but the auth-failure return
`if serr := s.doSerialize(ctx, chk, get); serr != nil { return nil, serr }` does not set `err`.
`Range` (lines 150-153) and `RangeStream` (lines 190-193) do set it (`err = serr`). Same code on
upstream `main` (`b25719d10`).

**What happens**: a read-only transaction denied by `CheckTxnAuth` (permission denied, invalid
user), or rejected by the stale-token check after a successful read
(`ErrAuthOldRevision`), is counted in `etcd_server_request_duration_seconds{type="ReadonlyTxn",
success="true"}`, and its slow-request warning is logged without the error (for the stale case,
with the response the client never receives). Reproduction:
`notes/pr-verify/etcd-21595/both/txn_readonly_metric_test.go` on branch `pr-verify/etcd-21595`;
`cp txn_readonly_metric_test.go server/etcdserver/ && cd server && go test -run TestReadonlyTxnAuthFailure ./etcdserver/`
fails at the pinned revision (and with etcd-io/etcd#21595 applied): `expected: 0x0, actual:
0x1`, "a denied read-only Txn was recorded as success="true"" (log:
`notes/pr-verify/etcd-21595/txn-metric-base-fork.log`).

**Expected**: `success="false"`, as for `Range`, and the error in the warning.

**How the proof handles it**: the specs say nothing about metrics or logs:
`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Txn.lean`'s postcondition is over the
returned values; the histogram observation and `WarnOfExpensiveReadOnlyTxnRequest` are callees
with specs that take any `success` label and any error.

**Possible fixes**: `err = serr` before `return nil, serr`, as in `Range`.

**Found**: 2026-10-17, by the reviewer of the verification of etcd-io/etcd#21595; confirmed with
the test above.
