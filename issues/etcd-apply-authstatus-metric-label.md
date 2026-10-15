# The apply metrics label an `AuthStatus` request `unknown`

- **Status**: open (minor; not filed).
- **Where**: `server/etcdserver/apply/uber_applier.go:167` (`uberApplier.dispatch`, the fork
  `upamanyus/etcd` at `bc8b52a50`, as upstream `main`): every case of the second `switch` sets
  `op` to the request's name before calling the applier, but `case r.AuthStatus != nil:` does not,
  so the deferred `txn.ApplySecObserve("v3", op, success, …)` records an `AuthStatus` request's
  apply time under the label `op="unknown"` (`etcd_server_apply_duration_seconds`), the label
  the code reserves for a request it does not know.
- **What happens**: an `AuthStatus` entry (proposed by `EtcdServer.AuthStatus` when it is
  linearized through raft) is applied correctly; only its latency is counted under `unknown`.
  Reproduction: apply an `InternalRaftRequest{AuthStatus: &pb.AuthStatusRequest{}}` through
  `NewUberApplier(...).Apply(...)` and read the histogram's label: `op="unknown"` (no Go test
  written: the metric is a package global).
- **Expected**: `op = "AuthStatus"`, as for the 29 other cases.
- **How the proof handles it**: not at all: `dispatch`'s spec says the deferred metrics return
  (`txn.ApplySecObserve`'s spec takes any `op`); nothing in the specs depends on the label.
- **Possible fixes**: add `op = "AuthStatus"` to the case.
- **Found**: 2026-10-12, reading `dispatch` for its spec (the apply package's unit 2).
