---
upstream: none
checked: 2026-11-04
links:
  - kubernetes/kubernetes#143325 pr open: related, not this: the watch cache's snapshots kept behind the compaction revision it tracks
blocks-proof: no
---

# k8s apiserver etcd3: `CompactRevision` can report a revision etcd has not compacted

`storage.Interface.CompactRevision`'s doc (`k8s.io/apiserver/pkg/storage/interfaces.go:283`) says it
"returns latest observed revision that was compacted". The etcd3 compactor sets it in two ways. Its
own successful round sets it after `client.Compact` returns. A failed compare-and-swap sets it from
`compact_rev_key`'s value. The winning compactor wrote that value before it called `client.Compact`,
so the compaction may not have happened yet. If that call fails (a timeout, the winner stopping), it
never happens at that revision. Until a later round compacts further, `CompactRevision` is ahead of
etcd's compaction revision: it is the latest revision *scheduled* for compaction.

**Why not an issue:** documentation only, and the error is conservative. The consumer, the watch
cache's compactor (`cacher/compactor.go:66`), drops its history up to the reported revision, so it
answers "too old" for revisions etcd could still serve. It never serves history etcd has dropped. The
next successful round compacts past the reported revision. Upstream searched by web search (2026-11-04): no report of it. Found by code reading while planning `notes/k8s-compactor-plan.md`.

## Proof

no: the compactor's spec states what the code does: the reported revision is one some compactor
recorded in `compact_rev_key`, at most the cluster's revision, not one etcd has compacted.
