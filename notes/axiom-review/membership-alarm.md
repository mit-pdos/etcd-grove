# Membership and the alarm store (axiom review, sweep batch 3, B3-4)

**Reviewed** (worktree `axiom/sweep-b3` at `fc2a20e7af`, 2026-11-07; the etcd pin `673da07c8fab`,
`etc/goose.py:258`; the Go files cited below are byte-identical at the pin and at `249d76bea7`
(`git diff` empty), so their line numbers hold at the pin):

| axiom | file:line | verdict |
|---|---|---|
| `membership.RaftCluster.Recover.wp_proof` | `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Recover.lean:26` (triple: `Spec/.../membership/RaftCluster__Recover.lean`) | **survives** (one zap hit, family (a)) |
| `membership.RaftCluster.SetBackend.wp_proof` | `Proof/.../membership/RaftCluster__SetBackend.lean:26` | **survives** |
| `membership.RaftCluster.String.wp_proof` | `Proof/.../membership/RaftCluster__String.lean:24` | **survives** |
| `membership.RaftCluster.updateMembershipMetric.wp_proof` | `Proof/.../membership/RaftCluster__updateMembershipMetric.lean:25` | **survives** |
| `membership.clusterImageOk_restModel.wp_proof` | `Proof/.../membership/clusterImageOk_restModel.lean:26` | **survives** (no program can reach it; its statement is stronger than its argument: see below) |
| `v3alarm.NewAlarmStore.wp_proof` | `Proof/.../v3alarm/NewAlarmStore.lean:26` | **survives** |
| `v3alarm.AlarmStore.restore.wp_proof` | `Proof/.../v3alarm/AlarmStore__restore.lean:26` | **survives** |

Also read: `AlarmStore.Recover` and `Get` (proved theorems, not axioms: `AlarmStore__Recover.lean:31`,
`AlarmGet.lean`), and `Activate`/`Deactivate` (no spec of their own; they are clauses of the
apply contract `apply.isAlarmStore`, `apply/Contracts.lean:462-479`, which `NewAlarmStore`'s post
gives through `alarmApplyOk`, `SnapRO.lean:80-84`).

No Go counterexample was built: every attack failed on a premise or on the Go code. No Lean was run
(the brief).

## The claims

- `Recover` (under `isRaftCluster c`, `clusterBeOn c d.be`, the idle part `rbOwnIn d.γB clusterBkts
  r`, `clusterImageOk c r mem'`, `clusterMem c mem`, a pooled reader and a thread token): it returns,
  `c.members` now decodes to `mem'`. Everything about the bucket contents is in the **opaque**
  `memBucketsOk` (`InvRest.lean:598-610`). It has no laws, so the only way to get it is
  `clusterImageOk_restModel`.
- `clusterImageOk_restModel`: for a committed log `L'` (`srvRLogLb γ L'`) that extends `L`, at least
  as long as the boot log, whose conf changes are all `ccBootOk`, and a cluster whose in-memory
  members are the model's at `L`, the model's three buckets at `L'` satisfy `memBucketsOk`.
- `SetBackend`: stores `be`, creates the three buckets (already present: `isSome` premises), one
  write-back. The part `rbPart S r` comes back idle (`rbOwnIn S r`).
- `String`: under `isRaftCluster c`, returns some string. `updateMembershipMetric`: under
  `rcLocalIDAddr c ↦□ lid`, returns.
- `NewAlarmStore` / `restore`: over an empty or absent alarm bucket (`(r.lookup "alarm").getD ∅ =
  ∅`) that is tracked (`d.P.RB "alarm"`: `KBReal.P`, `InvStore.lean:148-154`, makes `RB` the rest
  buckets) and in the table (`P.has alarmBI`): no error, the bucket created, the part idle.
  `NewAlarmStore` also gives `alarmEmpty a d.be ∗ alarmApplyOk a`.

## Attacks tried, and why each failed

### `RaftCluster.Recover`

1. **Malformed backend images** (bad JSON, a `null` value, a key that is not canonical hex, `"0"`,
   two keys that parse to one id (`"a"`/`"0a"`), a key whose id differs from the JSON's `"id"`, a
   removed member that is also a member, two `cluster` keys, a downgrade record with a bad target).
   In Go each one panics or misbehaves:
   - `mustParseMemberIDFromBytes`'s `lg.Panic` (`schema/membership.go:180-186`);
   - `json.Unmarshal(v, &m)` into a `**Member` (`:100-101`). A `null` value sets `m = nil`, and then
     `Recover`'s loop dereferences `m.ID` (`cluster.go:282`). JSON's `"id"` also overrides the key's
     id;
   - `ClusterVersionFromBackend`'s `semver.MustParse` / `lg.Panic` (`:190-206`);
   - `DowngradeInfoFromBackend`'s `lg.Panic`s (`:210-240`).

   **Blocked** by `clusterImageOk`. Every condition that matters is in `memBucketsOk`'s text:
   - each `members` entry is `memberKey mm.id ↦ memberEnc mm`, a JSON object;
   - every `members_removed` key is a member key, and no member is removed;
   - `cluster` holds the version `semverNorm` writes, with no downgrade record;
   - the local member is among the members.

   `memBucketsOk` is opaque and only `clusterImageOk_restModel` produces it, so these attacks have to
   go through that axiom (below).
2. **`MustDetectDowngrade`** (`version/downgrade.go:42-55`). It panics (a real `lg.Panic`, not
   `Fatal`) when `sv.LessThan(cv)`, with `sv` cut to `Major.Minor.0` and `cv` taken whole. So a
   cluster version of `3.8.1` panics a `3.8.0-alpha.0` server (`api/version/version.go:29`).
   **Blocked**: the version must be one `MustDetectDowngrade` accepts (`memBucketsOk`). The model's
   proposer, `monitorReq` (`InvMonitors.lean:55-68`, `semverAtMostServer`, `apply/InvRequest.lean:
   190-204`), proposes `Major.Minor.0` (`version/monitor.go:59`), which the docstring states
   precisely.
3. **The callback** `onSet = api.UpdateCapability` (`api/capability.go:63-83`): `nil` returns early,
   and otherwise it takes its own mutex and logs only when `lg != nil`. No panic.
4. **The metrics**:
   - `buildMembershipMetric` (`cluster.go:846-857`): two hex-string labels on the 2-label `knownPeers`;
   - `ClusterVersionMetrics.With({"cluster_version": version.Cluster(...)})` (`:300`): the right label
     name, valid UTF-8 (from `semver`).

   No panic.
5. **Concurrency**: `Recover` runs under `c.Lock()`, and so do `String`, `Members`, `AddMember` and the
   other readers. The fields outside the lock are `be` (owned: `clusterBeOn`), `localID` and `cid`
   (written only by `SetID`, which has no spec here). Every `c.be` user (`cluster.go:248-814`) is an
   apply-thread method. No race the model misses.
6. **(c) persistent facts**: `clusterBeOn`'s `mbl.be ↦□` and `mbl.lg ↦□`. `membershipBackend`'s
   fields are written only by `NewMembershipBackend` (`schema/membership.go:43-48`). The facts are
   true.
7. **(a) the zap family, a hit to note**. `Recover` logs through the **cluster's** logger: `c.lg.Info`
   at `cluster.go:272, 286, 296`, plus `MustDetectDowngrade(c.lg, …)`. `isRaftCluster` /
   `rcLockInv` (`membership/Defs.lean:174-186`) say nothing of `c.lg`, not even `≠ null`. The
   docstring assumes it works. `c.lg` is the bootstrap's `cfg.Logger` (`NewCluster` replaces only
   `nil` by `zap.NewNop()`, `cluster.go:107-109`), so a zero `&zap.Logger{}` server logger panics on
   the first `Info` (zap `logger.go:331`).
   - This is the zap-zero family (`zap-zero.md`). Whether it is reachable depends on what `NewServer`'s
     / `bootOk`'s premise says of `cfg.Logger`. Left to the zap sweep.
   - `mbl.lg` (`≠ null` only) is used only on panic paths, which `memBucketsOk` excludes. No
     difference.

### `clusterImageOk_restModel`

8. **A bad `ClusterVersionSet` in `L'`** (for example `99.0.0`, or `3.8.1`; attack 2). The model
   applies every committed `ClusterVersionSet` above `c0` (`restEntry` → `apply.restAfter` →
   `restSetVersion`: `InvRest.lean:304-316`, `apply/RestModel.lean:128-134`), and the axiom's
   premises constrain only conf-change entries (`ccBootOk`). Nothing in the statement says a normal
   entry is a request the server proposes (`rqOk` / `monitorReq`).
   - The docstring argues it from the code: only the monitor proposes `ClusterVersionSet`.
   - So the **statement is stronger than its argument**. `γ` is not tied to `c`, and nothing ties
     `L'`'s entries to the server's proposers.

   **Blocked from any program**. Using the conclusion needs `Recover`'s other resources:
   - `clusterBeOn c`, `clusterMem c` and `rbOwnIn` of the image's buckets are the apply thread's
     (`srvRestOwn`, `InvRest.lean:529-532`);
   - `isRaftCluster c` comes only from `bootOk`. No spec of `NewClusterFromURLsMap` /
     `NewClusterFromMembers` exists, so a program outside the package cannot build one.

   So the conclusion is used only inside the server's proofs (`SnapRecvFacts.lean:573`,
   `SnapRecvOn.lean:497`). There `γ` is the server's own and the committed log is the server's
   proposers'. A Go counterexample would need a running cluster that applies a snapshot whose
   `cluster` bucket was written by a forged proposal:
   - from a foreign binary: excluded by the deployment;
   - from a forged peer message: excluded in the model by `isMessage`.

   Proposed restatement (not applied): add the KV invariant's per-entry fact as a premise, `∀ m ∈
   L', m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq → ∀ v,
   rq.clusterVersionSet = some v → apply.semverAtMostServer v ∧ apply.semverValid v` (and no
   `DowngradeInfoSet`). Or state it for the server's `γ` only. Either way the argument becomes a
   premise the callers discharge from what they already hold.
9. **The members part** (`L'` drops a boot member, or the local member is missing).
   - `clusterMem c (restModel … L).mem` plus `isRaftCluster c` puts `c.localID` in the model's
     members at `L`: the halves agree (`memAt`, `Defs.lean:128-132`), and `rcLocalIn` holds.
   - `L <+: L'`, no `RemoveNode` (`ccBootOk`), and `AddNode`s of existing ids fail
     `ValidateConfigurationChange` (`cluster.go:306-390`), so the members never shrink.
   - `boot.length ≤ L'.length` puts every boot member's `AddNode` in `L'`.

   No gap.

### `SetBackend`

10. **Twice, or before or after `Recover`**: each call takes and returns `clusterBeOn`, and the
    premise needs the three buckets present. `MustCreateBackendBuckets`
    (`schema/membership.go:171-178`) calls `UnsafeCreateBucket`, which is `CreateBucketIfNotExists`
    (`backend/batch_tx.go:136-145`; its `Fatal` exits the process and needs a closed backend,
    excluded by `bOpen`).
    - The idle claim holds: `pending ≠ 0`, so `Unlock` writes back and commits any pending delete
      (`batch_tx.go:328-358`).
    - `S` may be any superset: `Unlock`'s write-back flushes every bucket, so idling all of `S`
      holds in Go.
11. **(a)**: `mbl.lg` is not used on this path. No hit.

### `String`, `updateMembershipMetric`

12. `String` (`cluster.go:213-229`) reads `cid`, the members (`%+v` of `*Member`: `types.ID`'s
    `String` is `FormatUint`) and `removed`, all under the lock. A nil `removed` map ranges fine, and
    a nil member cannot occur: `memberAt` has `m ≠ null`. Run concurrently with `AddMember`, it
    serialises on the lock; called while the lock is held, it deadlocks (not a counterexample).
13. `updateMembershipMetric` (`cluster.go:861-871`): `localID == 0` returns, and otherwise it sets
    `WithLabelValues(hex, hex)` on the 2-label vector. It cannot panic.
    - The `↦□ localID` premise (attack (c)): `SetID` (`:241-245`) is the only writer, and it has no
      spec, so no specified call changes it.
    - The member map is not read, so a nil map changes nothing.

### `NewAlarmStore`, `restore`

14. **A stored alarm that does not decode** (empty or malformed key; `proto.Unmarshal` in
    `GetAllAlarms`, `schema/alarm.go:91-102`, returns the error, and `restore` returns it,
    `alarms.go:112-123`), and **duplicate entries** in `restore`'s `addToMap` (`:125-137`: the
    first one wins). **Blocked**: the alarm bucket must be empty in the part. The part tracks what
    bbolt stores there (`P.RB`, `P.has`; round 4's untracked-bucket hole is closed in both
    triples). A backend opened on a file gets `rbOwn γ (rbData P D)` from the file's `D`
    (`backend/InvNew.lean:172-177`), so a program cannot claim an empty bucket over a file that
    holds alarms.
15. **`AlarmMember{0, NONE}`** (`nonissues/etcd-alarm-activate-none-zero-fatal.md`): its empty key
    reaches bbolt only through `Activate`, and the contract's `Activate` clause takes `at' ≠ 0`. The
    failure is a `Fatal` (exit) in any case. `Deactivate(_, NONE)` finds no member (`t[id] == nil`,
    `alarms.go:84-87`) and returns `nil`.
16. **(c) `alarmEmpty` against `alarmApplyOk`**: `Get` returns an empty slice under `alarmEmpty`.
    Could an `Activate` run through the contract while the caller keeps `alarmEmpty`? No.
    - The contract's write right must lend `alarmBeOn a d.be` (`rwLens RW (srvRestRW ∗ alarmBeOn …)`),
      the same half of `a.be` and `a.types` that `alarmEmpty` holds (`v3alarm/Defs.lean:80-96`).
      Two copies are impossible.
    - In the server, `srvRestRW`'s `rbOwn` and the apply thread's `srvRestOwn` are the same client
      half, so the contract's `Activate` cannot run while the model's alarm bucket is `∅`.
17. **(a) / (b)**:
    - `NewAlarmStore`'s `lg ≠ null`: `a.lg` is never used (`alarms.go:36-51`), and the alarm
      backend's `lg` only on a marshal error (`schema/alarm.go:60-63`) on the write paths. No hit.
    - A nil `ab`: the premise fixes `ab` to `*alarmBackend` at a location with `↦□` fields.
18. **`ForceCommit`'s hooks** (`backend.ForceCommit` runs `OnPreCommitUnsafe`): covered by
    `isBackend`'s hook contract. They write `meta`, which is not tracked (`KBReal.P.RB`), so even
    with `meta ∈ S` the part says nothing about it.

## Not tried

- A running-server counterexample for `clusterImageOk_restModel` (attack 8): a cluster with a
  forged `ClusterVersionSet`, then a snapshot sent to a member. It needs a foreign proposer or a
  forged peer message, which the deployment and `isMessage` exclude. Out of scope at estimate M.
- Whether, in Lean, a `ServerRaftNames` with `γ.pre = []` and `isCommittedLogLb` of arbitrary
  proposals can be built from raft's API apart from a server. That is the only way to instantiate
  attack 8's statement with a foreign `γ`, and even then `Recover`'s resources are missing. No
  `lake`.
- The zero-logger reach of `c.lg` (attack 7): left to the zap sweep.

## Go-code observations (not filed)

- `readMembersFromBackend` unmarshals into `&m` with `m` a `*Member` (`schema/membership.go:100-101`):
  - a `null` JSON value stores a nil member, which `Recover` then dereferences (`cluster.go:282`);
  - a JSON `"id"` overrides the key's id.

  etcd never writes either (`json.Marshal` of a non-nil `*Member` under its own id), so this would
  be a `nonissues/` entry at most.
- `MustDetectDowngrade` cuts the server version to `Major.Minor.0` but compares it with the cluster
  version as stored, so any stored patch above `0` panics. The monitor stores only `Major.Minor.0`
  (`monitor.go:59`), so this is not reachable in etcd. A `nonissues/` candidate at most.
