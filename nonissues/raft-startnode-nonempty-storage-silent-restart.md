---
upstream: none
checked: 2026-11-05
links:
blocks-proof: no
---
# raft: `StartNode` on a non-empty storage only logs a warning and runs the node as a restart

`StartNode` documents that it "appends a ConfChangeAddNode entry for each given peer to the initial
log". On a storage that already holds entries, `RawNode.Bootstrap` refuses ("can't bootstrap a
nonempty Storage"), and `setupNode` only logs that error as a warning and starts the node anyway
([node.go](https://github.com/etcd-io/raft/blob/b867cf13ff0ca9bd3a9ab7c10ef13a8f1ef9d9f2/node.go#L258-L261)):
the caller gets a node restarted from the storage, without the peers it passed and without being
told.

**Why not an issue:** documentation only, and a precondition etcd meets: etcd calls `StartNode`
only with peers, which it has only at the first start of a new cluster, with no WAL, on a fresh
`MemoryStorage` (`server/etcdserver/bootstrap.go`, `bootstrapRaft`: `!haveWAL && cfg.NewCluster`);
every other start calls `RestartNode`. The doc comment could say that the storage must be empty, or
`StartNode` could fail instead of warning. Found by code reading; no test.

## Proof

no: `StartNode.spec` takes a fresh storage (`restartStorage` at the empty contents,
`Spec/go_etcd_io/raft/v3/StartNode.lean`), under which `Bootstrap` succeeds; its post
`nodeStartedFresh` (the node's log began as the bootstrap log) rests on it.

## Notes

Found 2026-11-05 by a spec review of `nodeStartedFresh` (the lease-expiry plan's E2 revision 5).
Upstream not searched (`gh` unavailable here): `checked` is the date of the finding.
