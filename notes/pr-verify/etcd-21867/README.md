# Files for `notes/pr-verify/etcd-21867.md`

Revisions: upstream base = etcd-io/etcd `9ed485d3e37bbdddff471f5c6d6d7f62048c07d1` (the PR's merge
base with `main`); PR head = `8e685ea555050fdd92a08e36b81f8710b833d050`; fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-21867-goose-lean` (`d83ba44bd`: the fork's `goose-lean`
`09669450f` plus the PR, applied without conflicts, and the PR's unit test). The integration tests
were run in upstream checkouts with `GOTOOLCHAIN=go1.26.3` (the toolchain their `go.mod` names), from
the `tests` module.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `force_new_cluster_transport_test.go` | `TestForceNewClusterStopsDialingRemovedPeers`: after a 3-member cluster's member 0 is restarted with `ForceNewCluster` (the members' `ConfChangeAddNode` entries still in its WAL), a listener on a removed member's peer address sees no connection attempts once the node has settled. `...AfterSnapshot`: the same with `SnapshotCount: 10` and 30 puts (a snapshot covers the membership entries) | PR head: the first fails (80 connections in 2 s, 3 runs of 3), the second passes; base: both pass | `cp force_new_cluster_transport_test.go <checkout>/tests/integration/ && cd <checkout>/tests && go test ./integration/ -run '^TestForceNewClusterStopsDialingRemovedPeers' -count=1 -v` |
| `pr-head-dial.log`, `base-dial.log` | the results of the test above | PR head, base | as above |
| `force_new_cluster_stale_member_test.go` | `TestForceNewClusterWithStaleBackendMember`: a member written into member 0's backend only (not in its WAL) before the force-new-cluster restart: the node must elect itself and make progress | PR head: passes; base: hangs (raft voters `(42 self)`), the test times out | `cp force_new_cluster_stale_member_test.go <checkout>/tests/integration/ && cd <checkout>/tests && go test ./integration/ -run '^TestForceNewClusterWithStaleBackendMember$' -count=1 -timeout 120s -v` |
| `pr-head-stale.log`, `base-stale.log` | the results of the test above (the base's: the timeout and member 0's raft configurations) | PR head, base | as above |
| `force_new_cluster_restart_test.go` (the reviewer's) | `TestForceNewClusterThenPlainRestartDials`: dials to the removed members after the force-new-cluster restart, then after a following plain restart (logged; the test does not fail) | PR head: 80, then 0 (and the two "Validation on configuration change failed" ERRORs); base: 0 and 0 | `cp force_new_cluster_restart_test.go <checkout>/tests/integration/ && cd <checkout>/tests && go test ./integration/ -run '^TestForceNewClusterThenPlainRestartDials$' -count=1 -v` |
| `pr-head-restart.log`, `base-restart.log` | the results of the test above | PR head, base | as above |
| `pr-head-TestForceNewCluster-transport.log`, `base-TestForceNewCluster-transport.log` | the existing `TestForceNewCluster` (`tests/integration/cluster_test.go`, passes on both), member 0's transport and validation log lines after the restart: on the base the removal entries apply (`removed remote peer` for both); with the PR both fail validation (`membership: ID removed`) and the peers stay | PR head, base | `cd <checkout>/tests && go test ./integration/ -run '^TestForceNewCluster$' -count=1 -v`, then the lines filtered |

Also run on the fork branch: `go build ./...` and `go test ./etcdserver/` in `server` (pass, with
the PR's `TestFinalizeForceNewClusterRemovesStaleMembers`).
