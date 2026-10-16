---
upstream: none
checked: 2026-10-16
links:
---

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
- **How it happens**: `dispatch` starts with `op := "unknown"`, and a deferred call records the
  apply time under `op`.

  1. `EtcdServer.AuthStatus` proposes an `AuthStatus` request, and the apply loop calls
     `dispatch` on it.
  2. The `AuthStatus` case applies the request but does not set `op`.
  3. The deferred `txn.ApplySecObserve("v3", op, ...)` observes the latency under
     `op="unknown"`.

  ```go
  // server/etcdserver/apply/uber_applier.go:93-98, 164-169 (etcd main f061acd09)
  func (a *uberApplier) dispatch(r *InternalRaftRequestWrapper, shouldApplyV3 membership.ShouldApplyV3) *Result {
  	op := "unknown"
  	ar := &Result{}
  	defer func(start time.Time) {
  		success := ar.Err == nil || errors.Is(ar.Err, mvcc.ErrCompacted)
  		txn.ApplySecObserve("v3", op, success, time.Since(start))
  	// ...
  	case r.AuthDisable != nil:
  		op = "AuthDisable"
  		ar.Resp, ar.Err = a.applyV3.AuthDisable()
  	case r.AuthStatus != nil:
  		ar.Resp, ar.Err = a.applyV3.AuthStatus() // <- op not set
  	case r.AuthUserAdd != nil:
  		op = "AuthUserAdd"
  ```
- **Expected**: `op = "AuthStatus"`, as for the 29 other cases.
- **How the proof handles it**: not at all: `dispatch`'s spec says the deferred metrics return
  (`txn.ApplySecObserve`'s spec takes any `op`); nothing in the specs depends on the label.
- **Possible fixes**: add `op = "AuthStatus"` to the case.
- **Found**: 2026-10-12, reading `dispatch` for its spec (the apply package's unit 2).
