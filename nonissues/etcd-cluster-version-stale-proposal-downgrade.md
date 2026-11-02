---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---

# etcdserver: two cluster-version proposals in flight can apply out of order, lowering the cluster version and forcing a snapshot

The leader's version monitor decides the next cluster version from its own read of the current one
and proposes it from a goroutine, and the applier sets any proposed version unconditionally (a
lower one logs "Cluster version downgrade detected" and forces a snapshot). Two proposals in
flight at once (one made while the version is unset and some member's version unknown, proposing
3.0.0, and a later one proposing the members' version; or two successive leaders' stale reads) can
be applied in the other order: the cluster version moves down with no downgrade enabled, and a
snapshot is forced, until the next monitor tick raises it again.

**Why not an issue:** no test, found by code reading; whether the reordering is reachable (each
proposal waits up to the request timeout, against the monitor's interval and raft's ordering of
one member's proposals) is not checked.

## Proof

no: the server's request model admits any `ClusterVersionSet` whose version parses
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvMonitors.lean`), so the downgrade branch and its
forced snapshot are in the model (`notes/raft-unified-plan.md`, "Repair: Stage F statements").

## Notes

The code: `UpdateClusterVersionIfNeeded`/`decideClusterVersion` (`server/etcdserver/version/monitor.go`),
`UpdateClusterVersion` proposing in a goroutine (`adapters.go`), `updateClusterVersionV3`
(`server.go`), `applierV3backend.ClusterVersionSet` (`apply/backend.go`). A test could promote it:
unit tests for each half (two monitor ticks proposing 3.0.0 then V while the version is unset; an
applied lower version forcing a snapshot), and an integration test delaying one proposal past the
next tick (a failpoint in `updateClusterVersionV3`). A fix: have the applier ignore a lowering
`ClusterVersionSet` unless a downgrade to that version is enabled, or propose a compare-and-set on
the version read.
