---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# etcdserver: a crash during a membership change can leave the stored ConfState one change ahead of the consistent index

`applyConfChange` hands the new `ConfState` to the backend hooks (`SetConfState`) before the member
write takes the batch lock and moves the consistent index. A backend commit in between (the
batch-interval timer) makes durable a database whose stored `ConfState` is that of entry `k` while
its consistent index is still `k - 1`, and whose `members` bucket is still that of `k - 1`. After a
power loss there, the restarted member reapplies entry `k`, which succeeds: the membership check
reads the `members` bucket, not the stored `ConfState`.

**Why not an issue:** the window is real and reachable, but the restart is correct. The test
reaches the image and replays the entry on it: no error, no panic, and the result (consistent
index `k`, members, `ConfState`) is the one a run without the crash gives.

**How** (upamanyus/etcd `e94f33b50d`, the pinned fork; upstream `main` `4e090c033a`, 2026-11-24,
has the same order):
- `server/etcdserver/server.go:2081`: `s.beHooks.SetConfState(ep.confState)` (marks it dirty);
  then `:2096`/`:2098`/`:2107`: `PromoteMember`/`AddMember`/`RemoveMember`, whose backend write
  (`storage/schema/membership.go:59`, `:78`) is the first `LockInsideApply` of the entry; its hook
  (`server.go:2504`, `getTxPostLockInsideApplyHook`) moves the consistent index to `k`.
- A commit in between runs `OnPreCommitUnsafe` (`storage/backend/batch_tx.go:384`,
  `storage/hooks.go:47-55`): it saves the consistent index (`k - 1`) and the dirty `ConfState` (`k`).
- On restart `k > ci`, so entry `k` is applied with `ApplyBoth` (`server.go:1961-1965`);
  `ValidateConfigurationChange` reads `members` (`api/membership/cluster.go:311`), which does not
  have the change yet, so an add is not refused with "member exists" (nor a remove with "not
  found"), and `AddMember`/`RemoveMember` redo the write. `SetConfState` rewrites the same `ConfState`.

**Test:** `TestConfChangeCommitBetweenSetConfStateAndLockInsideApply` in
[`etcd-confstate-ahead-of-consistent-index/confstate_crash_test.go`](etcd-confstate-ahead-of-consistent-index/confstate_crash_test.go),
copied into `server/etcdserver` at upamanyus/etcd@e94f33b50d (go1.27.1). It builds the server
around a real backend (hooks and consistent index wired as `bootstrapBackend` does, batch interval
one hour), applies "add member 1" (entry 1) and "add member 2" (entry 2) through `EtcdServer.apply`,
and wraps the cluster's membership backend so that, just before entry 2's member write, it calls
`ForceCommit` (the timer firing at that instant) and copies the committed `db` file (the image a
power loss leaves). It then restarts from the copy (raft from a snapshot at index 1) and replays
entry 2:

```
$ go test ./etcdserver -run TestConfChangeCommitBetweenSetConfStateAndLockInsideApply -v
    confstate_crash_test.go:213: crash image: consistent index 1, stored ConfState voters [1 2], members [1]
    confstate_crash_test.go:227: replay errors: [<nil>]
    confstate_crash_test.go:235: after the replay: consistent index 2, stored ConfState voters [1 2], members [1 2]
--- PASS: TestConfChangeCommitBetweenSetConfStateAndLockInsideApply (0.11s)
```

## Proof

no: the crash image's row on the stored configuration (`srvCrashImageAt`, `confAt γ.cl i m`) is
false at such an image; T10's restatement `confRowW` (the configuration at `i` or at `i + 1`,
`dist/crash/BackendImage.lean`; ledger 2026-11-25) admits it, and the replay is correct, so no fork
fix is needed.

## Notes

- The stored `ConfState`'s only reader is the fork's `createMergedSnapshotMessage`
  (`server/etcdserver/snapshot_merge.go:53`), which runs on the apply goroutine after a batch, never
  inside the window. After a restart from such an image, and before the replay reaches entry `k`,
  a snapshot it sends with `replayConf == nil` (no disk snapshot) or a stored index the replay
  log does not cover would carry index `k - 1` with entry `k`'s configuration. Entry `k` was
  committed (it was applied), so the receiver's configuration is only early by one committed
  single change; not tested.
- The stored `ConfState` is loose in the other direction too: an entry at or below the consistent
  index is replayed with `ApplyV2storeOnly`, which skips raft's `ApplyConfChange` but still calls
  `SetConfState(ep.confState)` with the configuration it last held (at first the boot snapshot's), by code reading (`server.go:2078-2081`).
