# Axiom review: `membership.clusterImageOk_restModel`, generalized to any members with the model's ids

Date: 2026-11-06. Reviewed read-only in `/shared/etcd-grove-r2cscope`. Go code at etcd `673da07c8`
(the axiom's docstring cites `bc9c3868c`).

- Spec: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/clusterImageOk_restModel.lean`
- Axiom: `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/membership/clusterImageOk_restModel.lean`
- Proposed change (members premise only): from
  `clusterMem c (restModel c0 γ.raft.boot L).mem -∗ clusterMem c (restModel … L).mem ∗ ⌜clusterImageOk c (restModel … L').bk (restModel … L').mem⌝`
  to: for every `m` with `⌜keys m = keys (restModel c0 γ.raft.boot L).mem⌝`,
  `clusterMem c m -∗ clusterMem c m ∗ ⌜clusterImageOk c (restModel … L').bk (restModel … L').mem⌝`.

## Verdict: Survives

The conclusion's truth depends on `c` only through `c.localID` (and, through the deployment, on the
server binary's version). `c`'s current in-memory members are never read by `Recover` or by
anything `clusterImageOk` stands for: `UnsafeLoad` replaces `c.members` wholesale from the
backend. The premise `clusterMem c m` is needed only to put `c.localID` among the boot ids, and
the ids alone give that. No worktree was created and no counterexample was attempted, because
reading the code turned up no gap.

## How the conclusion is consumed

- `membership.memBucketsOk` is `opaque` (`InvRest.lean:610`). `clusterImageOk` is defined from it
  (`InvRest.lean:615`). The only axioms whose premise mentions it are this axiom and
  `membership.RaftCluster.Recover.spec`
  (`Spec/.../membership/RaftCluster__Recover.lean`). `grep` finds no other axiom over
  `clusterImageOk` or `memBucketsOk`. The proved uses (`SnapRecvOn`, `SnapRecvFacts`,
  `SnapApplyWalk`, `ApplySnapshotR`, `SnapApplyPost`, `EtcdServer__applySnapshot`) only carry it,
  or move it to another bucket map with the same three membership buckets, on its way to
  `Recover`.
- `Recover.spec` already takes `clusterMem c mem` for an **arbitrary** `mem` and returns
  `clusterMem c mem'`, with `mem'` the image's members. So the consumer never relates the
  pre-state members to the image.

## Attacks tried

1. **Recover reads or merges the old members.** It does neither. At `cluster.go:256-260`,
   `UnsafeLoad` assigns `c.version`, `c.members`, `c.removed` and `c.downgradeInfo` straight from
   `c.be`. `MustReadMembersFromBackend` (`schema/membership.go:83-120`) builds fresh maps from the
   `members` and `members_removed` buckets only; the `membershipBackend` holds no reference to the
   cluster. After that, `Recover` (`cluster.go:262-302`) reads only the new `c.members`. Failed.
2. **The local member's attributes or peer URLs.** In `Recover`, the local member appears only at
   `cluster.go:281-283` (`c.localID == m.ID` → `setIsLearnerMetric(m)`, which never panics), over
   the *loaded* members. `localID` is read-only after `SetID` (`rcLocalIn`'s `↦□`). Attributes
   play no part. Failed.
3. **The downgrade check.** `MustDetectDowngrade(c.lg, sv, c.version)` (`cluster.go:278`;
   `version/downgrade.go:42-55`) compares the binary's `version.Version` with `c.version`, which
   was just loaded from the `cluster` bucket. It does not depend on the old in-memory state or on
   members. The `downgradeInfo` log at `cluster.go:271-277` reads the loaded value. Failed.
4. **URL validation or panics on attribute mismatch.** `Recover` validates no URLs.
   `buildMembershipMetric` (`cluster.go:846-859`) uses only the ids of the loaded maps. The logs
   only read fields. The callers then use only the loaded members:
   - `applySnapshot` (`server.go:1156-1171`): `Recover`, `RemoveAllPeers`, then `AddPeer(m.ID,
     m.PeerURLs)` over `s.cluster.Members()`. Those are the image's members, whose peer URLs
     `memBucketsOk` asserts are the directory's.
   - `bootstrappedCluster.Finalize` (`bootstrap.go:508-522`): `Recover`, then
     `ValidateMaxLearnerConfig` over the loaded `Members()`.

   Nothing compares old and new attributes. Failed.
5. **Replace vs merge, and removed members.** It is a replace (attack 1). `c.removed` is also
   replaced from `members_removed`, which `memBucketsOk` asserts is empty, so `rcLockInv`'s empty
   removed map is re-established without reference to the old map. Failed.
6. **Lean level: a wider premise lets a cluster other than the server's satisfy it.**
   - The keys of `restModel c0 boot L` are `memBoot boot`'s ids for every `L`. `restBoot` starts
     `mem` at `memBoot`. `restUpdateAttrs` (`apply/RestModel.lean:118`) never adds a key: an
     unknown id leaves `r` unchanged. The conf changes are `AddNode`s of boot peers (`ccBootOk`),
     which `ValidateConfigurationChange` rejects.
   - So the new premise says only "`c`'s members have the boot ids". Through `isRaftCluster`'s
     `rcLocalIn` and the agreement of the two `memAt` halves, this gives `c.localID ∈ boot ids`,
     exactly what the old premise gave.
   - Any cluster object satisfying this does satisfy `memBucketsOk c` as its docstring reads: the
     local member is among the image's members, and the rest is about the image and the binary.
   - `clusterMem c m` is the apply thread's exclusive half and is returned unchanged, so no extra
     resource can be minted. Failed.
7. **The pin difference, `bc9c3868c` → `673da07c8`.** In the files the axiom cites, only
   `cluster.go` changed: `IsLocalMemberLearner` (`cluster.go:786-796`) now returns `false` where
   it used to `lg.Panic` on a missing local member. This is not on `Recover`'s path, and it makes
   that function more permissive. `schema/membership.go` and `version/downgrade.go` are
   unchanged. Failed.

## Not tried

- A Lean counterexample derivation: reading found no gap that would justify one.
- Re-auditing the parts of the axiom the change does not touch: that the image decodes, has a
  static membership, and has a version within bounds (the conclusion is unchanged). Also not
  re-checked: whether the restart replay itself can apply a `ClusterMemberAttrSet` to an id
  missing from the in-memory map. Go `UpdateAttributes`, `cluster.go:467+`, panics on an unknown,
  unremoved id. That is a question for the replay's own proof, not for this axiom. With
  `keys m` equal to the boot ids it does not arise.

## Proposed docstring addition (to append after the "*The members are the static cluster's…*" bullet)

> * *Only the ids of `c`'s in-memory members matter* (2026-11-06; the members premise taken at any
>   `m` with the model's keys, for the restart's WAL replay, whose in-memory attributes can be a
>   mix that no prefix's model has). `Recover` never reads the members it replaces: `UnsafeLoad`
>   (`cluster.go:256-260`) assigns `c.members` and `c.removed` from `MustReadMembersFromBackend`
>   (`schema/membership.go:83-120`), which reads only the buckets. Everything after it in `Recover`
>   (`cluster.go:265-302`: the metric, `MustDetectDowngrade` on the loaded version, the learner
>   metric of the local member, the logs) and in its callers (`applySnapshot`'s `AddPeer` over
>   `Members()`, `server.go:1160-1171`; `Finalize`'s `ValidateMaxLearnerConfig`,
>   `bootstrap.go:522`) reads the loaded members. `c`'s current members enter only to place
>   `c.localID` among the boot ids (`isRaftCluster`'s `rcLocalIn`, the halves of `memAt`
>   agreeing). The ids of `restModel c0 boot L`'s members are the boot log's for every `L`
>   (`memBoot`; `restUpdateAttrs` adds no key; the conf changes are rejected).

Possible simplification (optional): since `keys (restModel c0 boot L).mem = keys (memBoot boot)`
for every `L` under the premises, the premise could be stated as `keys m = keys (memBoot
γ.raft.boot)`, which drops the dependence on `L`. The proposed form is equivalent and also sound.

No etcd bug was found.
