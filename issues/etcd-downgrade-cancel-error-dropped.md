---
upstream: unchecked
checked: 2026-10-16
links:
  - etcd-io/etcd@e47c3c22d: "server: Move downgrade API logic into version package" turned the returned error into a log line
  - etcd-io/etcd#22575 pr open: touches downgradeCancel, keeps the dropped error
---

# server: `Downgrade` CANCEL reports success when the cancel fails

- **Status**: bug (a wrong result: errors are dropped, the client is told the cancel succeeded).
- **Where**: `server/etcdserver/v3_server.go` at the pinned revision (`etc/goose.py`, etcd
  09669450f), `downgradeCancel` (`v3_server.go:1268-1275`):

  ```go
  err := s.Version().DowngradeCancel(ctx)
  if err != nil {
  	s.lg.Warn("failed to cancel downgrade", zap.Error(err))
  }
  resp := pb.DowngradeResponse{Version: version.Cluster(s.ClusterVersion().String())}
  return &resp, nil
  ```
- **What happens**: every error of `Manager.DowngradeCancel` is logged and the RPC returns a
  response with a `nil` error: `ErrNoInflightDowngrade` (no downgrade in progress), the
  linearizable read's errors (`ErrTimeout`, `ErrLeaderChanged`, `ErrStopped`, the context's) and
  the proposal's (`raftRequest`: timeouts, `ErrStopped`, too large ...). `etcdctl downgrade
  cancel` then prints success though nothing was cancelled, and a cancel that timed out is
  indistinguishable from one that was applied. Before e47c3c22d the handler returned these
  errors; the gRPC layer still maps `version.ErrNoInflightDowngrade` to
  `rpctypes.ErrGRPCNoInflightDowngrade` (`v3rpc/util.go:69`), and the e2e helper
  `tests/framework/e2e/downgrade.go:65` (`DowngradeCancel`) still expects "no inflight downgrade
  job" from a cancel with nothing in progress. Reproduction:
  `TestDowngradeCancelWithoutDowngradeReportsError` in
  `notes/pr-verify/etcd-22575/v3_server_downgrade_test.go` (fork layout) and `upstream/` (upstream
  layout): fails on 09669450f, on the fork with the PR, on upstream bc12c9498 and on the PR head 5aa78069a (`test-*.log` and `upstream/test-*.log` there).
- **Expected**: the error returned (`return nil, err`), as before e47c3c22d and as the gRPC error
  map and the e2e helper assume.
- **How the proof handles it**: `downgradeCancel`'s spec on `pr-verify/etcd-22575`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeCancel.lean`) states what the
  code does: once the version is known, success whatever the cancel returned. It is not the
  intended behavior; the report (`notes/pr-verify/etcd-22575.md`) says so.
- **Possible fixes**: `if err != nil { s.lg.Warn(...); return nil, err }`.
- **Found**: 2026-10-16, verifying etcd-io/etcd#22575.
