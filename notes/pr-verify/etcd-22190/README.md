# Files of the verification of etcd-io/etcd#22190

Go tests and probes for the findings of `notes/pr-verify/etcd-22190.md`, and their logs. The
fork branch is `mit-pdos/etcd-grove` branch `pr-etcd-22190-goose-lean` (`f150c16f9`: the PR at
`455bf3f8a` applied onto the pinned `goose-lean` `09669450f`); "base" is the pin itself.

Run each from a checkout's `server/` directory after `cp <file> etcdserver/`, with
`GOTOOLCHAIN=go1.27.1`. The probes that end in `lg.Fatal` exit the test binary, so run the tests
one at a time (`-run '^Name$'`).

| File | What it shows | Revision | Command |
|---|---|---|---|
| `storageversion_during_stop_test.go` | The PR's regression test `TestStorageVersionDuringStop`, copied as `TestStorageVersionDuringStopCopy` (a file of its own, to run at the base, where the PR's `server_test.go` change is absent). At the base both subtests hit the nil `*bolt.Tx` dereference (the concurrent one then hangs: the panic leaves `txMu` held); with the PR both pass. | base, PR | `go test ./etcdserver/ -run '^TestStorageVersionDuringStopCopy$' -count=1 -v` |
| `closed_backend_probe_test.go` | `bemu` readers after `Cleanup` closed the backend: `StorageVersion` (panics at the base, `nil` with the PR), `Defragment` (`FATAL failed to commit tx {"error": "tx closed"}` at both), `ForceCommit` as `Compact` calls it (`FATAL failed to begin tx {"error": "database not open"}` at both). `issues/etcd-storageversion-closed-backend.md`, `issues/etcd-backend-use-after-cleanup.md`. | base, PR | `go test ./etcdserver/ -run '^TestProbeStorageVersionAfterCleanup$' -count=1 -v` (and `TestProbeDefragmentAfterCleanup`, `TestProbeForceCommitAfterCleanup`) |
| `snapshot_after_cleanup_probe_test.go` | The reviewer's probe: `maintenanceServer.Snapshot`'s first step, `schema.ReadStorageVersion(s.Backend().ReadTx())`, after `Cleanup`: the nil `*bolt.Tx` dereference at both revisions (`Backend()` releases `bemu` before the read, so the PR's check does not apply). `issues/etcd-backend-use-after-cleanup.md`. | base, PR | `go test ./etcdserver/ -run '^TestProbeSnapshotReadStorageVersionAfterCleanup$' -count=1 -v` |
| `base-goose-lean.log` | The runs above at the base (filtered to the result lines). | base `09669450f` | as above |
| `pr-goose-lean.log` | The same at the fork branch with the PR. | `f150c16f9` | as above |
