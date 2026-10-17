---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#22190 pr open: fixes the same pattern in `StorageVersion` only
  - etcd-io/etcd#17223 issue closed: "UnsafeRange panicking during shutdown", the same class
---

# etcdserver: `Defragment`, `Snapshot` (and `Compact`'s `ForceCommit`) use the backend after `Cleanup` closed it

- **Status**: bug (a reachable `Fatal` exit or nil dereference during shutdown), the same class as
  `issues/etcd-storageversion-closed-backend.md`, which etcd-io/etcd#22190 fixes for
  `StorageVersion` only.
- **Where**: `server/etcdserver/server.go` at the pinned revision (09669450f): `Defragment`
  (`server.go:964`) read-locks `s.bemu` and calls `s.be.Defrag()` (`server.go:975`) without
  checking `s.stopping`; `Compact` (`v3_server.go:412`) read-locks it and calls
  `s.be.ForceCommit()` after a physical compaction. `Cleanup` (`server.go:942`), run at the end
  of `run`'s shutdown after `close(s.stopping)`, closes the backend under `s.bemu.Lock()`;
  nothing stops a later reader. `Defragment` is reached from the Maintenance `Defragment` RPC
  (`api/v3rpc/maintenance.go:123`), which keeps being served while the member shuts down. The
  Maintenance `Snapshot` RPC (`maintenance.go:141`) starts with
  `schema.ReadStorageVersion(ms.bg.Backend().ReadTx())`: `Backend()` (`server.go:2386`) takes
  `bemu` only to return `s.be`, and the read happens after it is released, so the PR's pattern
  (a check under the lock) cannot cover it; nor the other users of `Backend()`'s result (hash
  checks, the quota's `Size`).
- **What happens**: after `Cleanup`, `Defragment` logs `FATAL failed to commit tx {"error": "tx
  closed"}` and exits the process (`backend.defrag`'s commit of the stopped batch transaction);
  `ForceCommit` logs `FATAL failed to begin tx {"error": "database not open"}`; `Snapshot`'s
  storage-version read panics with the nil `*bolt.Tx` dereference of
  `issues/etcd-storageversion-closed-backend.md`. Reproduction:
  `notes/pr-verify/etcd-22190/closed_backend_probe_test.go` (`TestProbeDefragmentAfterCleanup`,
  `TestProbeForceCommitAfterCleanup`; each exits the test binary, so run them one at a time) and
  `notes/pr-verify/etcd-22190/snapshot_after_cleanup_probe_test.go`
  (`TestProbeSnapshotReadStorageVersionAfterCleanup`, the verification's reviewer's);
  the log is `notes/pr-verify/etcd-22190/base-goose-lean.log`, and they fail the same way with
  the PR applied (`pr-goose-lean.log`). The probes call the methods after `Cleanup` directly; that
  a `Defragment` RPC can arrive in the window between `Cleanup` and the gRPC server's stop is the
  same window as #22189's `Status` (not reproduced end to end here). `Compact`'s path needs a
  physical compaction to finish across the shutdown, narrower.
- **Expected**: an RPC racing the shutdown fails with an error (e.g. `ErrStopped`); the member
  exits cleanly.
- **How the proof handles it**: `Defragment` and `Compact` are not verified (names-only /
  outside the translated request path). The lock invariant of branch `pr-verify/etcd-22190`
  (`InvBackendLife.lean`) states what a `bemu` reader may assume: a fraction of the backend's open
  token only if it has seen `stopping` open under the lock, so `Defragment` as written would not
  meet a spec over it.
- **Possible fixes**: the PR's pattern in each `bemu` reader that uses the backend under the lock
  (`select` on `s.stopping` under the read lock, returning `ErrStopped`); for `Backend()`'s
  callers, which use the backend after the lock, a "closed" check inside the backend itself (its
  read transaction failing instead of dereferencing nil), or an `ErrStopped` check in the RPC
  layer before the call (which narrows, but does not close, the window).
- **Found**: 2026-10-17, verifying etcd-io/etcd#22190 (`notes/pr-verify/etcd-22190.md`).
