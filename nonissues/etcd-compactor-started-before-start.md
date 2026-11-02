---
upstream: none
checked: 2026-11-01
links:
blocks-proof: yes
---

# etcdserver: NewServer runs the auto-compactor before Start, which panics if Start is late or never comes

`NewServer` starts the auto-compactor before steps that can still fail and before `Start` sets the
wait registry; its error paths close the backend without stopping it. A compactor whose period
elapses before `Start` calls `Compact` on the half-built server and panics on the nil wait registry;
on the error paths the goroutine leaks and panics later.

**Why not an issue:** a precondition etcd's caller meets: `embed.StartEtcd` calls `Start` right after
`NewServer` (only the opt-in initial corruption check runs between them), and a periodic compactor
fires only after a full retention period (an hour for `--auto-compaction-retention=1`); on
`NewServer`'s or the initial check's failure (`StartEtcd` calls `Cleanup`, which does not stop the
compactor) etcd exits. It panics only for an embedder that keeps running after `StartEtcd` fails with
auto-compaction on, or with a retention shorter than the gap.

## Proof

yes: the verified fork runs the compactor from `start()` (`goose-lean-compactorstart` `964dccdb4`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__start.lean`): with it run from `NewServer`, no
sound contract exists for its `Compact` calls.

## Notes

`TestAutoCompactorNotRunBeforeStart` in
[`nonissues/etcd-compactor-started-before-start/repro_test.go`](etcd-compactor-started-before-start/repro_test.go)
(`NewServer` with a 1s periodic retention, `Start` 2s later; copied as `zz_repro_test.go` into
`tests/integration`) panics at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (go1.27.3):
`panic: runtime error: invalid memory address or nil pointer dereference` at `v3_server.go:1108`
(`processInternalRaftRequestOnce`), from `v3compactor/periodic.go:142`. A test of the error path
(`StartEtcd` failing after `NewServer`, the process kept alive) would make it an issue.
