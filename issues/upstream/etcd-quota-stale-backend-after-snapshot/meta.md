# etcd-quota-stale-backend-after-snapshot

## Security classification

Not a security report, but the user should confirm it: the effect is a cluster-wide loss of write availability (a
NOSPACE alarm that disarming does not clear until the member restarts), but no client with ordinary access can
trigger it. It needs a member whose db was over its quota when it started to catch up by a snapshot, which depends
on the member lagging (down, partitioned) and on the operator's quota and defragmentation, not on any request.

## Candidate

- **Finding**: `issues/etcd-quota-stale-backend-after-snapshot.md`
- **Target**: etcd-io/etcd, `main`. The gRPC quota has been built once from `s.Backend()` since the quota layer was
  added (2016); the release branches likely have the bug too (not checked).
- **Branch**: `fix/etcd-quota-stale-backend-after-snapshot` in `~/etcd-fixes/etcd-quota-stale-backend-after-snapshot`,
  two commits: b0baf43c1 (`tests/integration: test the quota after a snapshot install`) adds the test, which fails
  there; 563ae7f6c (`server: check the gRPC quota against the current backend`) is the fix. Not pushed.
- **Base**: upstream `main` 6782f5229b8a6dbc5f6d421107fd70d66de98694 (2026-10-19); `server/etcdserver/api/v3rpc/quota.go`
  and `applySnapshot` match the finding's description at the fork pin (8a24be2a3).
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-19)

Five searches on etcd-io/etcd: `quota snapshot backend`, `"database space exceeded" snapshot`, `quota stale backend`,
`NOSPACE alarm restart`, `BackendQuota`. No duplicate, no open PR. Related, different: #10312 (closed: quota flag
ignored with a config file), #17318 (closed: alarm not clearing after the db shrank; no snapshot detail, cause not
shown), #9992 (closed: why disarm is manual), #14267 (closed: bbolt free pages), #21636 (closed: consistent index
on the alarm-plus-snapshot path), #22524 (open: a member caught up by a snapshot becomes ready late; not the quota).

## Verification (go1.27.2 linux/amd64)

`TestV3StorageQuotaAfterSnapshot` (in `tests/integration/v3_alarm_test.go`, after `TestV3StorageQuotaApply`, in its
style) is the issue's example.

- At the tests commit b0baf43c1 (`cd tests; go test ./integration/ -run 'TestV3StorageQuotaAfterSnapshot$'
  -count=5`): fails 5 of 5 at the last assertion, `etcdserver: mvcc: database space exceeded`, with member 2's db
  24576 or 28672 bytes under the 65536-byte quota.
- At the fix commit 563ae7f6c: the same command passes 5 of 5; `go test ./integration/ -run
  'Quota|Alarm|Snapshot|Defrag|Lease' -count=1` ok (169 s); in `server/`, `go test ./etcdserver/... ./storage/...`
  ok, `go build ./...` ok, `go vet ./etcdserver/api/v3rpc/ ./etcdserver/api/v3client/` clean; `gofmt -l` empty.
- At the fix commit, the whole of `tests/integration` and `tests/integration/clientv3` (`cd tests; go test ./integration/ ./integration/clientv3/ -count=1 -timeout 50m`): ok (472 s, 83 s).
- The issue's "Anything else" (alarm, put through member 0, disarm, restart), run at the base by `go test -overlay`
  (the base's `quota.go` and a copy of the test extended with those steps, not on the branch), 2 runs of 2: the
  rejected put raises NOSPACE for member 2; a put through member 0 then fails with `database space exceeded`;
  after disarming, a put through member 2 fails again and the alarm is back; after restarting member 2 and
  disarming, a put through member 2 succeeds (db 28672 or 32768 bytes).

Not run: `tests/e2e`, `make verify` (golangci-lint), benchmarks. The finding's NOSPACE-recovery scenario (quota on
member 2 from the start, alarm raised, recovered while member 2 was down) was run at the fork pin only, not at this
base.

## Why the test shows the bug and not a misuse

Every step is an ordinary operation through the gRPC API or the integration framework: puts, a delete, a physical
compaction, `Defragment` on the two running members, stopping and restarting a member, and setting
`--quota-backend-bytes` on a member at restart (a configuration change etcd allows; the member's db being over the
new quota is the state the NOSPACE alarm exists for). The linearizable range through member 2 before it stops makes
sure member 2 applied the big put (so its db file is over the quota when it restarts); the one after the restart
makes sure it caught up, and `Backend().Size() < quota` checks that it did so by the leader's (defragmented)
snapshot. The expectation is the quota's documented meaning: a write is refused when the member's db plus the
write would exceed `--quota-backend-bytes`.

## Why the fix works

At the base, `NewQuotaKVServer`/`NewQuotaLeaseServer` (called once, by `v3rpc.Server` and `v3client.New`) store
`newBackendQuota(s, …)`, a `storage.BackendQuota` holding `s.Backend()` at that time. `applySnapshot` swaps `s.be`
for the snapshot's backend and closes the old one; `backend.Size()` is an atomic set at each commit, so the closed
backend's size stays at its last value. Each gRPC write is then checked against that frozen size, refused, and
`quotaAlarmer.check` proposes a NOSPACE alarm. The apply path is not affected: `applySnapshot` rebuilds
`s.uberApply`, whose `quotaApplierV3` takes the new `s.be`. With the fix, `quotaAlarmer` holds the server and the
quota's name and calls `newBackendQuota(qa.s, qa.name)` at each check, so it reads `s.Backend()` (under `bemu`)
each time. Alarm and member ID come from the same server, as before (the two fields were the server itself).

## If a reviewer asks

- **Cost per request**: `storage.NewBackendQuota` per Put/Txn/LeaseGrant: one small allocation, a `sync.Once` check,
  `s.Backend()`'s read lock, and one or two `Set`s of the `quota_backend_bytes` gauge. Negligible against a raft
  proposal. With the default quota (0) the gauge is set to 0 and then to the default within one call, so a scrape
  could in principle read 0 for a moment; before the fix this happened only at startup and at each snapshot install
  (the applier's quota). If a reviewer objects: build the quota once and give `storage` a constructor that takes
  a function returning the backend, or cache the quota per backend in `quotaAlarmer` (needs a lock or an atomic
  pointer); both are larger changes.
- **Rebuild the gRPC quota in `applySnapshot`, like the applier**: the gRPC servers are created outside
  `EtcdServer` (`v3rpc.Server`, `v3client.New`) and `EtcdServer` has no reference to them.
- **Opposite direction** (db under the quota at start, snapshot over it): the gRPC check does not refuse writes it
  should, but the applier's quota still raises the alarm; the same fix covers it. Not tested.

## Commit messages to rewrite

- `tests/integration: test the quota after a snapshot install` (no body)
- `server: check the gRPC quota against the current backend`, body: "A member replaces its backend when it applies
  a snapshot, but the gRPC quota kept measuring the backend the member started with."

## Push (when the user approves)

`git -C ~/etcd-fixes/etcd-quota-stale-backend-after-snapshot push origin fix/etcd-quota-stale-backend-after-snapshot`;
then check the issue's test link (`v3_alarm_test.go#L129-L181`) on GitHub.
