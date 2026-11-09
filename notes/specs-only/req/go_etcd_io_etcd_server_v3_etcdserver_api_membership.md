# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/api/membership` (2e)

## from 2d

What `applyConfChange` (2d) needs of the membership (`RaftCluster`):

1. **`ValidateConfigurationChange(cc, shouldApplyV3)`** is a function of the membership's state at
   the entry (the history's members at `histAt γ (k-1)`, and the removed ids), so every member decides
   a committed conf change alike (2d decides it once for the cluster: R1's `confDecide`).
2. **`AddMember`/`PromoteMember`/`RemoveMember`/`UpdateRaftAttributes(…, shouldApplyV3)`**: with
   `shouldApplyV3`, the backend write runs the post-lock hook (the consistent index to the entry);
   without, only the in-memory view (the replay below the consistent index).
3. **`Members()`**, **`IsIDRemoved(id)`** (with a thread token), **`SetBackend`/`Recover`** over a
   snapshot's image (`applySnapshot`).
4. The conf change's context (JSON) decodes and names the change's node: the cluster's invariant on
   conf-change proposals (`configure`'s, 2c) gives it, so `applyConfChange`'s `lg.Panic`s are
   unreachable.
