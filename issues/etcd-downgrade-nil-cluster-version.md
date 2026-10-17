---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22574 issue open: the same panic, reported upstream
  - etcd-io/etcd#22575 pr open: the fix (guards both handlers); verified in notes/pr-verify/etcd-22575.md (branch pr-verify/etcd-22575)
---

# server: `Downgrade` ENABLE and CANCEL panic before the cluster version is known

- **Status**: bug (a reachable panic: a client request crashes the member).
- **Where**: `server/etcdserver/v3_server.go` at the pinned revision (`etc/goose.py`, etcd
  09669450f): `downgradeEnable` (`v3_server.go:1252-1266`) and `downgradeCancel`
  (`v3_server.go:1268-1275`); `server/etcdserver/version/version.go:47`
  (`Manager.DowngradeValidate`: `allowedDowngradeVersion(cv)` with `cv` unchecked) and
  `downgrade.go:57-60` (`allowedDowngradeVersion` dereferences `ver`). `downgradeValidate`
  (`v3_server.go:1231-1250`) has the guard (`ErrClusterVersionUnavailable`).
- **What happens**: during the bootstrap window (`s.ClusterVersion()` is `nil` until the first
  `ClusterVersionSet` is applied), `Downgrade` with `ENABLE` panics in `allowedDowngradeVersion`
  (via `Manager.DowngradeEnable` → `DowngradeValidate`, after the linearizable read), and with
  `CANCEL` panics on `s.ClusterVersion().String()` after the cancel request (whose error is only
  logged: `etcd-downgrade-cancel-error-dropped.md`). The gRPC server does not recover handler
  panics, so the member exits. Reproduction: `TestDowngradeClusterVersionUnavailable` in
  `notes/pr-verify/etcd-22575/v3_server_downgrade_test.go` (the fork's layout) and
  `notes/pr-verify/etcd-22575/upstream/v3_server_downgrade_test.go` (upstream's), both
  `cp <file> server/etcdserver/ && go test -run TestDowngrade ./etcdserver/` from `server/`: on
  09669450f and on upstream bc12c9498, ENABLE and CANCEL panic
  (`notes/pr-verify/etcd-22575/test-base.log`, `notes/pr-verify/etcd-22575/upstream/test-upbase.log`).
- **Expected**: `ErrClusterVersionUnavailable`, as `VALIDATE` returns.
- **How the proof handles it**: the downgrade API is not verified on `lean` (names-only). On the
  branch `pr-verify/etcd-22575`, `semver.Version.String`'s spec needs a non-nil version and the
  Server interface's `GetClusterVersion` contract returns `nil` unless the caller holds the
  cluster-version witness, so the old code's specs are not provable; the PR's code is
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeEnable.lean`, `..Cancel`).
- **Possible fixes**: etcd-io/etcd#22575 (a `nil` check at the top of both handlers).
- **Found**: 2026-10-16, verifying etcd-io/etcd#22575 (already reported upstream as #22574).
