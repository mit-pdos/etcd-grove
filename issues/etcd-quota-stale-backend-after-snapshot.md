---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#20553 pr merged: related, not this bug (another holder of the backend across applySnapshot's swap, the maintenance Defragment path; fixes #20271); does not touch the gRPC quota
blocks-proof: yes
---

# etcdserver: a member that catches up by a snapshot rejects writes with "database space exceeded" while its db is under its quota

After a member installs a leader's snapshot, its gRPC quota check keeps measuring the backend it
started with, which the snapshot replaced and closed. If that old db was over
`--quota-backend-bytes`, every write through the member fails with `etcdserver: mvcc: database
space exceeded` although its current db is under the quota, and each refusal raises a NOSPACE
alarm that stops writes on every member; disarming does not help until the member restarts.

**Expected:** a write should be refused only when the member's db plus the write exceeds
`--quota-backend-bytes` (the flag's [documentation](https://etcd.io/docs/v3.6/op-guide/maintenance/#space-quota)),
as the apply path's quota, rebuilt after a snapshot, already checks.

**Impact:** default configuration apart from the quota itself. A member whose db was over its
quota when it started and that then catches up by a snapshot under the quota: for example a member
that was down while the cluster recovered from NOSPACE (compact, defragment, disarm), the
documented recovery. The cluster then cannot take writes until that member is restarted. The quota
has been built once since it was added (2016), so every release has it.

**Reproduction:** `TestV3StorageQuotaAfterSnapshot` in
[`issues/etcd-quota-stale-backend-after-snapshot/quota_after_snapshot_test.go`](etcd-quota-stale-backend-after-snapshot/quota_after_snapshot_test.go),
copied into `tests/integration` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3 linux/amd64:

```
$ go test ./integration -run TestV3StorageQuotaAfterSnapshot -count=1
        	Error Trace:	.../tests/integration/zz_quota_snap_test.go:67
        	Error:      	Received unexpected error:
        	            	rpc error: code = ResourceExhausted desc = etcdserver: mvcc: database space exceeded
        	Messages:   	put through member 2 with db size 24576 under quota 65536
--- FAIL: TestV3StorageQuotaAfterSnapshot (1.26s)
FAIL	go.etcd.io/etcd/tests/v3/integration	13.135s
```

**Cause:** the KV and lease gRPC servers check writes against a quota that
[`newBackendQuota`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/quota.go#L93-L95)
builds once, when the servers are created, over `s.Backend()` at that time.
[`applySnapshot`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L1082-L1083)
replaces that backend and closes the old one, whose size then stays frozen; it rebuilds only the
[applier's quota](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L1146-L1148).
Each refused write [proposes a NOSPACE alarm](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/quota.go#L38-L51).

## Proof

yes: the verified fork carries the fix (`8f793b820`, `etc/goose.py`; the quota alarmer holds the
server and reads its current backend, `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`).

## Fix

**Branch**: `fix/etcd-quota-stale-backend-after-snapshot` in `~/etcd-fixes/etcd-quota-stale-backend-after-snapshot` (upamanyus/etcd, not pushed): b0baf43c1 test, 563ae7f6c fix
**Base**: etcd-io/etcd@6782f5229b8a6dbc5f6d421107fd70d66de98694

**PR draft**:

Title: server: check the gRPC quota against the current backend

The KV and lease gRPC servers check writes against a quota that [`newBackendQuota`](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/api/v3rpc/quota.go#L93-L95) builds once, when the servers are created, over the member's backend at that time. [`applySnapshot`](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/server.go#L1082-L1083) replaces that backend with the snapshot's and closes the old one, so the quota keeps measuring the closed backend; `applySnapshot` rebuilds only the [applier's quota](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/server.go#L1146-L1148). This PR builds the gRPC quota at each check, over the server's current backend.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

A reviewer may ask about the cost (one small allocation and a read lock per write, negligible
next to a proposal) and why not rebuild in `applySnapshot` (the gRPC servers are created outside
`EtcdServer`, which holds no reference to them).

## Notes

INDEX-reviewed.md's Plan is "Skip for now" (availability, not safety): a filing decision; the
finding stays an issue. The branch's base is three weeks behind the recorded base; the test fails
at both.
