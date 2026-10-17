---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22189 issue open: the same crash (Maintenance Status racing a member's shutdown), reported with a reproducer
  - etcd-io/etcd#22190 pr open: the fix (`StorageVersion` checks `s.stopping` under `bemu`); its `Cleanup` half is already in main (d6af8028d, etcd-io/etcd#22425)
  - etcd-io/etcd#17223 issue closed: "UnsafeRange panicking during shutdown", the same class (stale, closed unfixed)
---

# etcdserver: `StorageVersion` reads the backend after `Cleanup` closed it (nil `*bolt.Tx`)

- **Status**: bug (a reachable nil dereference: the member crashes instead of exiting cleanly).
- **Where**: `server/etcdserver/server.go` at the pinned revision (`etc/goose.py`, 09669450f):
  `StorageVersion` (`server.go:2192`) read-locks `s.bemu` and calls
  `schema.DetectSchemaVersion(s.lg, s.be.ReadTx())` unconditionally; `run`'s deferred shutdown
  closes `s.stopping` (`server.go:815`) and later calls `Cleanup` (`server.go:827`), which closes
  the backend under `s.bemu.Lock()` (`server.go:956`; the lock is upstream d6af8028d's). The
  lock makes a reader in progress finish before the close, but a reader that arrives after the
  close reads a backend whose shared read transaction `CommitAndStop` has reset to nil. Reached
  from `maintenanceServer.Status` (`api/v3rpc/maintenance.go:289`, through
  `serverVersionAdapter.GetStorageVersion`, `adapters.go:72`) and the `/version` HTTP handler
  (`api/etcdhttp/version.go:37`), which keep serving while the member shuts down (a member
  removed from the cluster stops its own server).
- **What happens**: `backend.(*baseReadTx).UnsafeRange` calls `(*bolt.Tx).Bucket` on a nil
  transaction: `panic: runtime error: invalid memory address or nil pointer dereference`.
  Reproduction: `notes/pr-verify/etcd-22190/closed_backend_probe_test.go`,
  `TestProbeStorageVersionAfterCleanup` (and the PR's own test, copied as
  `storageversion_during_stop_test.go`), on the pinned fork: `cp` both into `server/etcdserver/`,
  `go test ./etcdserver/ -run TestProbeStorageVersionAfterCleanup`; the log is
  `notes/pr-verify/etcd-22190/base-goose-lean.log`.
- **Expected**: a `Status` call racing a shutdown succeeds (without the storage version) or
  fails with an error; the member exits cleanly.
- **How the proof handles it**: on `lean` `StorageVersion` is not translated (names-only). On
  branch `pr-verify/etcd-22190` it is verified with the PR's fix: `bemu`'s lock invariant
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBackendLife.lean`, `bemuP`) holds a fraction of
  the backend's open token or the backend shut with `stopping` closed, and `DetectSchemaVersion`'s
  contract asks for a fraction of the open token; without the `select` on `s.stopping` the shut
  case has none, so the pinned code's `StorageVersion` does not meet the spec.
- **Possible fixes**: etcd-io/etcd#22190 (check `s.stopping` under `s.bemu`'s read lock); more
  generally, a "closed" flag set under `bemu.Lock()` in `Cleanup` that every `bemu` reader checks
  (the same class: `issues/etcd-backend-use-after-cleanup.md`).
- **Found**: 2026-10-17, verifying etcd-io/etcd#22190 (`notes/pr-verify/etcd-22190.md`).
