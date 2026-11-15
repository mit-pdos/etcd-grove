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


## from 3a

The apply layer (3a) calls the membership on the apply thread (`applierV3backend`'s membership
methods), in both modes:
1. **`UpdateAttributes`**: as 2e's spec (used with the caller's update, `Apply.memberUpd`).
2. **`Version()`, `SetVersion(ver, onSet, shouldApplyV3)`**: a spec, with its panic-freedom
   (`semver.MustParse(r.Ver)` in the applier, `MustDetectDowngrade` in `SetVersion`) as a pure
   premise on the version: 3a's provisional `Apply.clusterVerOk ver` (the version parses and the
   member's binary is not older); the cluster's invariant should give it for every committed
   `ClusterVersionSet` (the leader proposes the minimum of the members' versions) or it is a
   deployment premise (a decision).
3. **`SetDowngradeInfo(d, shouldApplyV3)`**: a spec (no panic, the backend written at `shouldApplyV3`).
4. **`ID()`** (the reply header): read-only.
5. `beView c st` held inside 3a's `smAt` (the backend's member buckets with `st.members` a permutation
   of the model's members).
Used by: `applierV3backend.{ClusterVersionSet,ClusterMemberAttrSet,DowngradeInfoSet,newHeader}.spec`.

## from 4b

`beMembers mb st` is `∃ lg be cb, mb ↦□ membershipBackend{lg, be} ∗ Schema.memberBkts be (some cb)`
with `cb.st = st` (`Schema.ClusterBkts`: the view, the stored cluster version as a `Semver.SemVer`,
the stored downgrade info); `none` is a backend whose membership buckets are not created yet
(`MustCreateBackendBuckets` creates them). The methods' specs are
`Schema.membershipBackend.*.spec` (assumed: names only): `MustCreateBackendBuckets`,
`MustSaveMemberToBackend`, `MustDeleteMemberFromBackend`, `MustReadMembersFromBackend`,
`MustSaveClusterVersionToBackend`, `MustSaveDowngradeToBackend`, `ClusterVersionFromBackend`,
`DowngradeInfoFromBackend`. The writers run the backend's post-lock hook (`Schema.applyHook be Pre Q ∗
Pre` to `Q`: at `shouldApplyV3`, the consistent index's update, 2d); the readers take and give back a
`threadTok` (their read transaction's reader slot) and return fresh values (`memberPts … (own 1)` in
fresh maps; a `Semver.verAt`; a `DowngradeInfo` struct). `ClusterVersionFromBackend` needs the stored
version to parse back (`Semver.parse (render sv) = some sv`: true of what `SetVersion` stores, a
`MustParse`d version, by `Semver.parse_render`); `DowngradeInfoFromBackend` an enabled target to
parse. `TrimClusterFromBackend`, `TrimMembershipFromBackend` have no spec (no translated caller).
