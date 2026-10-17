---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#21671 issue closed: the report (a leader change makes `/v3/lease/keepalive` answer `{"code": 2, "message": "not a primary lessor"}`); closed as stale, not fixed
  - etcd-io/etcd#21684 pr open: the fix (maps `lease.ErrNotPrimary` to a new `rpctypes.ErrGRPCLeaseNotPrimary`, code `Unavailable`); verified on branch `pr-verify/etcd-21684`
---

# server/etcdserver/api/v3rpc: a lease renewal refused for lost leadership answers gRPC `Unknown`

- **Status**: a bug (a wrong result: a transient, retryable condition is reported with the code
  of an unknown, permanent failure).
- **Where**: at the pinned fork commit `09669450f` (`etc/goose.py`'s etcd pin):
  `EtcdServer.LeaseRenew` returns `lease.ErrNotPrimary` itself when the member believes it is
  the leader but `ensureLeadership()` fails (`server/etcdserver/v3_server.go:503-505`);
  `LeaseServer.leaseKeepAlive` passes it to `togRPCError` (`server/etcdserver/api/v3rpc/lease.go:142-143`);
  `togRPCError` (`util.go:98`) looks the error up in `toGRPCErrorMap` (`util.go:35-93`), which
  has `lease.ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge` but not
  `lease.ErrNotPrimary`, so it falls through to `status.Error(codes.Unknown, err.Error())`.
  `rpctypes` has no error for it either. The server's own comment
  (`v3_server.go:664-665`, `LeaseTimeToLive`) says "lease.ErrNotPrimary is not retryable error for
  client. Instead, uses ErrLeaderChanged", and `LeaseRenew`'s comment (`v3_server.go:501-502`) says
  the error is returned "so that the client can switch to another member".
- **What happens**: the keep-alive stream ends with `rpc error: code = Unknown desc = not a primary
  lessor`; through the grpc-gateway, `{"code": 2, ...}`. Reproduction:
  `notes/pr-verify/etcd-21684/lease_notprimary_probe_test.go` (branch `pr-verify/etcd-21684`),
  `TestProbeLeaseKeepAliveNotPrimaryCode`, which serves `LeaseServer` over gRPC with a lessor
  whose `LeaseRenew` returns `lease.ErrNotPrimary`: at `09669450f` it fails with
  `expected codes.Unavailable, got Unknown` (`probe-base.log`).
- **Expected**: a code that says to retry elsewhere (`Unavailable`, as `ErrGRPCNoLeader`,
  `ErrGRPCLeaderChanged`, `ErrGRPCNotLeader`).
- **How the proof handles it**: on `lean`, `v3rpc.togRPCError.spec` says only that the result is a
  non-nil error, and `v3rpc.grpcErrMap` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Base.lean`)
  leaves the map's keys open, so nothing is claimed of this error's code. On `pr-verify/etcd-21684`
  the spec says that for `lease.ErrNotPrimary` the result is `rpctypes.ErrGRPCLeaseNotPrimary`, of
  code `Unavailable`; it is proved of the PR's code, under the package-initialization fact
  `notPrimaryEntry`, which the code before the PR does not meet.
- **Possible fixes**: etcd-io/etcd#21684 (map it to a new `Unavailable` error), or map it to
  `rpctypes.ErrGRPCLeaderChanged` / `ErrGRPCNotLeader`, as `LeaseTimeToLive` does for a demoted lease.
- **Found**: 2026-10-17, verifying etcd-io/etcd#21684 (`notes/pr-verify/etcd-21684.md`).
