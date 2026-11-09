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

## from 3c

1. **`Lease.clusterOk cl`** (provisional in `lease/Api.lean`; persistent): the `*RaftCluster` the
   server passes to `lease.NewLessor` as its `cluster`: `Version()` may be called from any goroutine
   (the lessor's `Checkpoint`, on the apply thread) and returns `nil` or a readable
   `*semver.Version`. A law `isCluster c ... ⊢ Lease.clusterOk (iface c)` of yours would discharge
   it at `NewServer`. Used by: `NewLessor.spec`, `lessor.shouldPersistCheckpoints.spec`.
   ```go
   srv.lessor = lease.NewLessor(srv.Logger(), srv.be, srv.cluster, lease.LessorConfig{...}) // server.go:344
   cv := le.cluster.Version()                                                                 // lessor.go:386
   ```
