# Tracking the backend's rest buckets instead of the D22c determinism axiom

**Carried out** (2026-10-23): `notes/decisions.md`, "D22 the backend over every bucket carried
out"; `notes/STATUS.md`, "D22 the backend over every bucket". What follows is the study.

Read-only study, 2026-10-22, worktree `d22` at `lean` c7c4b2b441. Go at the etcd pin
`2aed163b` (`etc/goose.py:164`), extracted from `.lake/go-src/etcd`; Go paths are under
`server/`. `notes/snapshot-path-s0.md` quotes the older pin `8a24be2a3`, so its Go line numbers
are off by up to about 30 lines (for example `NewAuthStore` is now at `auth/store.go:958`). Lean
paths are relative to the repository. Abbreviations: **E/** = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`,
**S/** = `Spec/go_etcd_io/etcd/server/v3/`, **B/** = `Proof/go_etcd_io/etcd/server/v3/storage/backend/`.

"Rest buckets" means `restBuckets` (`E/InvImage.lean:60-62`): `lease`, `alarm`, `auth`,
`authUsers`, `authRoles`, `members`, `members_removed`, `cluster`.

**One fact first.** The closed theorems run raft in its no-snapshot mode: `bootOk`'s
`Hnosnap` (`E/InvBoot.lean:161`, `γ.reNoSnap = true`), with `SnapshotCatchUpEntries: 1 << 48`
in both programs. So in the runs that `putget_safe`/`putget3_safe` cover today, no image is sent
and no `Recover` runs. What follows is the writer analysis for the same workload once S-l/S-j
turn snapshots on (D22f). Even so, the apply-path invariant proposed below can be proved on
today's runs.

## 1. Every write to the rest buckets, and whether it is reachable

The workload is fixed by the following (Lean):
- `plainCover` (`E/KVModelDefs.lean:59-80`) admits only `put`, `deleteRange`, `txn`,
  `clusterVersionSet` and `clusterMemberAttrSet` (`_ => False`). `putgetWorkload` (`:134`) admits
  exactly these. `watchkv`'s workload (`examples/watchkv/Workload.lean:41`) admits less.
- `noGrant` (`:125`).
- Auth is off (`isAuthStore … false`).
- `srvCCPolicy` (`E/InvRequest.lean:284`) with `ccApplyOk` (`:264`) admits only `AddNode` of a
  member of the configuration, so the boot entries are the only conf changes.
- The apply package's own `rqOk` (`E/apply/Chain.lean:247-261`) is wider: lease kinds are
  `False`, but alarm, auth and downgrade kinds are `True`.

| # | Writer (Go) | Bucket | Reachable in putget / putget3? |
|---|---|---|---|
| B1 | `bootstrap`: `schema.CreateMetaBucket` (`etcdserver/bootstrap.go:266`); `Finalize` → `c.cl.SetBackend` → `MustCreateBackendBuckets` (`bootstrap.go:496`, `membership/cluster.go:247-250`, `storage/schema/membership.go:171-178`) | creates `members`, `members_removed`, `cluster` (empty) | **Yes**, at boot. It is part of `bootstrapContract`, a premise (`putget.premises`, `examples/putget/Defs.lean:114-128`). On a fresh data directory it writes no contents. `Recover` is only called with a WAL (`bootstrap.go:497`). |
| B2 | `NewServer` → `lease.NewLessor` → `initAndRecover`: `UnsafeCreateLeaseBucket` and `ForceCommit` (`server.go:348`, `lease/lessor.go:808-835`) | creates `lease` | **Yes** (creation only). The TTL clamp at `:817-818` is in memory only. |
| B3 | `NewServer` → `auth.NewAuthStore`: `CreateAuthBuckets`, then **`commitRevision` (`authRevision = 1`)** (`server.go:373`, `auth/store.go:974, 994-995, 1014-1016`) | creates `auth`, `authUsers`, `authRoles`; **puts `auth/authRevision`** | **Yes.** This is the only content write at boot. |
| B4 | `NewServer` → `restoreAlarms` → `v3alarm.NewAlarmStore` → `restore`: `CreateAlarmBucket` (`server.go:391, 2409-2416`, `api/v3alarm/alarms.go:103-104`) | creates `alarm` | **Yes** (creation only). |
| B5 | Apply: `applyConfChange` → `AddMember` → `MustSaveMemberToBackend` (its own `LockInsideApply`/`Unlock`, `json.Marshal(m)`) (`server.go:2017-2097`, `:2057`; `cluster.go:394-427`; `schema/membership.go:50-61`) | `members[id]` := JSON of the entry's context member | **Yes**: the boot `AddNode` entries 1..n, with `shouldApplyV3`, when validation passes. Validation (`cluster.go:306-391`) reads `members` and `members_removed` through `ReadTx` (`schema/membership.go:91-99`). On a fresh member the boot entries pass if the ids and peer URLs are distinct. A later `AddNode` of an existing voter fails with `ErrIDExists`, so it writes nothing. |
| B6 | Apply: `RemoveMember` / `PromoteMember` / `UpdateRaftAttributes` (`server.go:2055, 2066, 2084`; `cluster.go:429, 498, 535`) | `members`, `members_removed` | **No.** `ccApplyOk` excludes them. |
| B7 | Apply: `ClusterMemberAttrSet` → `applierV3backend.ClusterMemberAttrSet` → `RaftCluster.UpdateAttributes` (`apply/backend.go:287-296`; `cluster.go:467-496`) | `members[id]` := JSON of the **in-memory** `c.members[id]` with the new attributes | **Yes.** `publishV3` (`server.go:536, 1808-1815`) proposes it (its spec: `S/etcdserver/EtcdServer__publishV3.lean:25-37`). It writes only if `id ∈` the in-memory `c.members` (exception 7). |
| B8 | Apply: `ClusterVersionSet` → `SetVersion` → `MustSaveClusterVersionToBackend` (`apply/backend.go:270-285`; `cluster.go:589-623`; `schema/membership.go:148-155`, value `ver.String()`) | `cluster/clusterVersion` | **Yes.** `monitorClusterVersions` (`server.go:539, 2221`; its spec `S/etcdserver/EtcdServer__monitorClusterVersions.lean:25-40`) proposes it: `MinClusterVersion` while the members' versions are unknown, otherwise their minimum (`etcdserver/version/monitor.go:56-75`). In putget3 the peer handler is only the raft transport (`server.go:645`), so peers' versions are fetched with no `/version` handler and the minimum is unknown. |
| B9 | Apply: `DowngradeInfoSet` → `SetDowngradeInfo` (`apply/backend.go:298-304`; `cluster.go:811-818`; `schema/membership.go:159-169`) | `cluster/downgrade` | **No.** `plainCover` is `False` for it, and `monitorDowngrade` is off (`DowngradeCheckTime = 0`, `S/etcdserver/EtcdServer__monitorDowngrade.lean:25-37`). |
| B10 | Apply: `Alarm` → `AlarmStore.Activate`/`Deactivate` (`apply/backend.go:109`; `alarms.go:53-66`) | `alarm` | **No.** `plainCover` excludes it. The NOSPACE proposal (`server.go:2004-2012`) is dead (`E/NoSpaceDead.lean`, `backendUnderQuota`). CORRUPT is off (`monitorKVHash`/`monitorCompactHash` specs). The program's only client calls just Put and Get. |
| B11 | Apply: `LeaseGrant`/`LeaseRevoke`/`LeaseCheckpoint` → `lessor.Grant` (`persistTo`, `lessor.go:281-312`, `lease.go:55-61`), `Revoke` (`:326, 359`), `Checkpoint` (`:367-375`) | `lease` | **No.** `rqOk` is `False` (`Chain.lean:253-255`) and `isApplyLessor`'s `Revoke` takes `⌜False⌝` (`E/apply/Contracts.lean:280-293`). `noGrant` means `expiredC` never delivers (`server.go:842-843`). The checkpointer is the premise `ckptEffectsOk`, and `Promote`/`Demote` write nothing. |
| B12 | Apply: the auth writers (`AuthEnable`/`AuthDisable` `auth/store.go:293, 315`; `UserAdd` … `RoleDelete`, `:464-849`, each `commitRevision`) | `auth*` | **No.** `plainCover` excludes them and auth is off. Note that the generic apply proofs still cover them (`rqOk` `True`), and `isAuthStore`'s `AuthDisable` clause does not require `on = true` (`Contracts.lean:196-199`). |
| B13 | Receiver: `lessor.Recover` (create, `ForceCommit`), `restoreAlarms` (create), `authStore.Recover` (reads only), `cluster.SetBackend` (create), `cluster.Recover` (`UnsafeLoad`, reads) (`server.go:1080, 1102, 1111, 1116, 1135`; `lessor.go:600-609`; `auth/store.go:399-418`; `cluster.go:255-300`) | creations only (idempotent on an image) | **No** today (no snapshot mode). Once snapshots are on, it writes no rest contents. |
| B14 | `monitorStorageVersion` → `UnsafeMigrate` (`server.go:540, 2244`; `schema/schema.go:130-133`: only `addNewField(Meta, storageVersion)`) | `meta` only | Yes, but it writes no rest bucket. |
| B15 | Pre-commit hook `OnPreCommitUnsafe` (`storage/hooks.go:45-54`) | `meta` (ci, term, confState) | Yes, but it writes no rest bucket. |
| B16 | `TrimClusterFromBackend`/`TrimMembershipFromBackend` (`schema/membership.go:65, 124`) | `cluster`, `members*` | **No.** The server never calls them (migration tools only). |

Nothing else in `Start`'s goroutines writes the rest buckets (`server.go:533-544`):
`adjustTicks`, `purgeFile`, `monitorFileDescriptor`, `LinearizableReadLoop`, `monitorKVHash`
and `monitorCompactHash` (both off), and the lessor's `runLoop` before any grant. Neither do the
compactor (off) or the backend's `run` (it commits, and only the hook writes, B15).

**The reachable rest-bucket contents are therefore:**
- the boot state: B1–B4, that is every rest bucket empty except `auth = {authRevision ↦ 1}`;
- `members`, changed by B5 (the boot `AddNode`s) and B7 (`ClusterMemberAttrSet`);
- `cluster/clusterVersion`, changed by B8 (`ClusterVersionSet`).

`lease`, `alarm`, `auth`, `authUsers`, `authRoles` and `members_removed` stay at their boot value
for good.

## 2. Whether the reachable writes are verified, and how their callees are specified

| Write | Code path verified? | How the writing callee is specified (file:line) |
|---|---|---|
| B1 | No: bootstrap is a premise | `bootstrapContract` → `bootOk` (`E/InvBoot.lean:130-262`). About `D` it states only `HD`, the **Key** view empty (`:241`), plus opaque `bkFresh` tokens for `lease`, `auth`, `alarm` (`:244-245`; definition `:91-100`) and `bkNoCmp` (`:248`). **Nothing is stated about `members`, `members_removed`, `cluster`, `authUsers` or `authRoles`.** |
| B2 | `NewServer` is proved; the callee is an axiom | `lease.NewLessor` axiom (`Proof/go_etcd_io/etcd/server/v3/lease/NewLessor.lean:26`; spec `S/lease/NewLessor.lean:72-95`): it consumes `bkFresh "lease"` and hands out `lessorBackend` (`Proof/…/lease/LessorBackend.lean:84`), whose `leaseBatchTx` `UnsafePut` takes no bucket token (`:50-63`). Its post says nothing about bucket contents. |
| B3 | Callee is an axiom | `auth.NewAuthStore` axiom (`Proof/…/auth/NewAuthStore.lean:26`; spec `S/auth/NewAuthStore.lean:29-75`): consumes `bkFresh "auth"`. The docstring mentions `commitRevision`; **the post does not state `authRevision = 1`**. |
| B4 | Callee is an axiom | `v3alarm.NewAlarmStore` axiom (`Proof/…/api/v3alarm/NewAlarmStore.lean:26`; spec `S/etcdserver/api/v3alarm/NewAlarmStore.lean:29-65`): consumes `bkFresh "alarm"` and gives `alarmFresh`. `restoreAlarms` is proved over it (spec `S/etcdserver/EtcdServer__restoreAlarms.lean:24-45`). |
| B5 | **No**: the whole function is an axiom | `EtcdServer.applyConfChange.wp_proof` is an `axiom` (`E/EtcdServer__applyConfChange.lean:25`; spec `S/etcdserver/EtcdServer__applyConfChange.lean:28-95`). The post gives `ownCCV1`, `epConfState` with an **arbitrary** `cs'`, and `Post ∨ Adv`. **Nothing about `members` or validation.** `membership.ccContextOf` is opaque and yields only `(id, IsPromote)` (`E/InvRequest.lean:256`). |
| B7 | Proved down to the membership contract: `apply.Apply` → `uberApplier.dispatch` → `applierV3backend.ClusterMemberAttrSet.wp_proof` (`E/apply/Link.lean:404-406`) | `isCluster`'s `UpdateAttributes` clause (`E/apply/Contracts.lean:425-430`): `{cPre b P f Pre Q Post ∗ storeWT ∗ storeRT} … {cPost b Pre Post ∗ storeRT}`, **no bucket effect**. `isCluster` comes from `bootOk`'s `#Hisc` (`E/InvBoot.lean:218-222`), so the clause is part of the bootstrap-contract **premise**, not an axiom. `membership` is names-only. |
| B8 | Proved down to the contract: `applierV3backend.ClusterVersionSet.wp_proof` over `semver.MustParse`, `LessThan`, `String` (`E/apply/Link.lean:400-402`) | `isCluster`'s `SetVersion` clause (`Contracts.lean:420-424`): takes `⌜v ≠ null⌝` only, **no bucket effect**; same premise. `cPre`/`cPost` are at `:86-96`, `csContract` at `Proof/…/storage/mvcc/InvStore.lean:618-625`. The in-memory version has its own premise, `clusterVersionMono` (`E/InvStart.lean:180-186`; `bootOk`'s `Hcvm`). |
| (B9–B12, unreachable) | The generic apply proofs exist: `applierV3backend__Alarm/Auth*/Lease*/DowngradeInfoSet.lean` | `isAlarmStore` (`Contracts.lean:334-350`), `isAuthStore` (`:174-~230`), `isApplyLessor` (`:268-300`), `isCluster.SetDowngradeInfo` (`:431-435`). None of them names a bucket. |

## 3. How the backend model represents buckets today

- **The physical state has every bucket.** `Data := GMap GoString BktData` (`B/InvBbolt.lean:47-50`).
  `BSess.C`/`.S` (`B/Model2.lean:98-106`) are bbolt's committed data and the writer's contents,
  over all buckets; `fileHolds path D` (`B/InvBbolt.lean:89`) and `newPost … D`
  (`B/InvNew.lean:55-59`) are over the whole `D`. `put`/`del`/`create`/`delBucket`
  (`Model2.lean:270-290`) act on any bucket.
- **What clients can observe hides every bucket but `Key`.**
  - `vData` (`Model2.lean:166-172`) drops the hook buckets `HB`.
  - `bridgeParams` sets `HB n = (n ≠ Key)` (`Proof/…/storage/mvcc/BackendBridge.lean:98-101`), so
    `meta` and all rest buckets are hook buckets.
  - `bView` (`B/InvBackend.lean:175-176`) and `keyView` (`InvStore.lean`, "keyView") therefore see
    the `Key` bucket only.
  - `bucketView` (`InvStore.lean:990`) is the KV's share of that view.
- **The hook's own keys are the one tracked part outside `Key`.**
  - `BParams.HK` (`Model2.lean:49-56`), with `hkData P S` (`:329-335`), is a `ghostVar γ.hkd`
    split in halves: half held by the batch lock (`B/InvBatch.lean:289`), half held by the client
    as `hkOwn` (`B/InvBackend.lean:89-91, 219-220`).
  - `UnsafePut` of an `hk` key needs `hkPut` (`InvBackend.lean:224-225`;
    `S/storage/backend/batchTxBuffered__UnsafePut.lean:28-34`; update lemma `InvBatch.lean:173-206`).
  - `UnsafeDelete`/`UnsafeDeleteBucket` forbid `hk` keys (`batchTxBuffered__UnsafeDelete.lean:27-35`,
    `…UnsafeDeleteBucket.lean:27-34`).
  - Only `meta/consistent_index` and `meta/term` are `HK` (`ciKeys`, `E/CindexBackend.lean:66-68`);
    `confState` is excluded (`hooksParams`, `Proof/…/storage/InvHooks.lean:49-51`).
- **So a put or delete to a rest bucket is unconstrained:** `hkPut` is `True` and no ghost state
  changes. Any holder of `isBackend` and the batch lock may write a rest bucket and nothing records
  it. The holders today are the lessor, the auth store, the alarm store, the cluster contract,
  `applyConfChange`, the storage-version monitor (`srvSVRes`), and the names-only monitors through
  `srvMonitorPermit` ⊇ `isServerReq` (`E/InvMonitors.lean:80-82`).
- **The batch-tx tokens are budget, not ownership.** `wbTok`/`ownToks γ.wb` (`InvBackend.lean:214`),
  `kbWT`/`kbRT`/`bkRTx` are fungible write-back and reader budgets. They name no bucket, so they
  cannot give a frame.
- **Rest-bucket facts are opaque tokens.** `bkFresh γB n` (`E/InvBoot.lean:91-100`, opaque,
  consumed by B2–B4's axioms), `alarmFresh` (`:102-107`) and `bkNoCmp` (`InvStore.lean:205-218`,
  the meta compaction keys) stand in for facts the model cannot state.
- **S-f's vocabulary is pure predicates on `Data`, not tied to any ghost state.** `imageAt`
  (`E/InvImage.lean:86-88`) includes `bkRestAt L D` (`:79-80`): per bucket, `D.lookup n = bkRestOf
  L n` (`:73-76`), which is `authBoot` (`:66`), `some ∅`, or the opaque `clusterBktOf n L`
  (`:69`). `dbImage` (`:98-100`) is persistent. `backend.Snapshot.spec`'s observation passes
  `viewAt` and `hkOwn` (`S/storage/backend/backend__Snapshot.lean:51,54`), so only the `Key` view
  and the ci/term keys can be observed, which is why S-h needed the determinism axiom
  (`notes/decisions.md:12660-12667`).

**What tracking changes, minimally.** Generalise the `HK` mechanism from keys to whole buckets:
- a new parameter `BParams.RB : GoString → Bool`; `bridgeParams` adds `RB n ↔ n ∈ restBuckets`,
  which requires `RB ⊆ HB` and `RB` disjoint from `SB`/`meta`;
- `rbData P S : GMap GoString BktData`, the map `n ↦ bktOf S n` for `RB n`, with absent counted as
  empty (`Model2.lean:195`'s `bktOf`). Choosing `bktOf` over `lookup` means creating a bucket needs
  no token (B2, B4, B13 stay token-free);
- a ghost name `BNames.rbk`: half in `batchGhost` (`ghostVar γ.rbk ½ (rbData P st.S)`), half the
  client's `rbOwn γ r`;
- `rbPut γ P n S`, the `hkPut` analogue, required by `UnsafePut` and, unlike `hk`, also by
  `UnsafeDelete`/`UnsafeDeleteBucket` on an `RB` bucket (both the buffered and plain variants);
- `hookStep` (`Model2.lean:296`) gains `rbData P st'.S = rbData P st.S`, so a hook may not write
  `RB`;
- `newPost` gains `rbOwn γ (rbData P D)`;
- `backend.Snapshot.spec`'s observation gains `-∗ rbOwn γ r -∗ ⌜Q vd d r⌝`, and its post
  `Q (sData P D) (hkData P D) (rbData P D)`;
- `bkFresh` and `alarmFresh` disappear, and `bkRestAt` restated over `bktOf` becomes
  `rbData = restModel L`.

## 4. The minimal tracking design for the current workload

**Which buckets are constant and which change, as a pure model.**
- `restBoot`: every rest bucket `∅`, except `auth = authBoot`. This is the state after B1–B4.
- `restModel L := foldl restStep restBoot L`, where:
  - a conf-change entry `cc` (`AddNode`, context `ctx`): if `ccValid r.members r.removed cc` then
    `members := insert (memberKey id) (memberEnc (ccMember ctx))`;
  - a normal entry with `clusterVersionSet v`: `cluster := insert clusterVersionKey (semverStr
    (semverParse v))`;
  - a normal entry with `clusterMemberAttrSet (id, a)`: `members := insert (memberKey id)
    (memberEnc (attrSet m a))`, with `m` the member at `id` (see the in-memory caveat in 5);
  - any other entry: unchanged (puts, deletes, txns, empty entries, entries at or below `c₀`).

  `memberEnc`, `ccMember`, `ccValid`, `semverParse` and `semverStr` are opaque pure functions,
  each named in one writer's statement.
- So `lease`, `alarm`, `auth`, `authUsers`, `authRoles` and `members_removed` stay at `restBoot`;
  only `members` and `cluster` change.

**What proves the verified code never writes the constant buckets.** A frame on the `rbOwn`
fragment, not on the batch-tx tokens:
- After `NewServer` the apply thread holds the fragment. Add `rbOwn d.γB (restModel (pre ++ A))`
  to `applyRes` (`E/InvRun.lean:239-250`), beside `kvRun`/`appliedLogAt`, mirroring
  `kvAppliedL`'s `x.log = kvModel γk A` (`E/InvRequest.lean:1215`).
- No other thread can then put to or delete from a rest bucket in the model. The storage-version
  monitor, the hook, the lessor's loop and the names-only monitors hold no fragment.
- On the apply thread, the writer clauses that need the fragment (alarm, auth, lease, downgrade,
  `RemoveMember`) run only on dispatch branches that `plainCover` rules out.
- The cheapest way to keep their proofs is to narrow the apply package's `rqOk` (`Chain.lean:247`)
  to `False` for the alarm, auth-write and downgrade kinds, as it already is for leases. No
  workload uses those kinds. Their branches become dead, so only the `ClusterVersionSet` and
  `ClusterMemberAttrSet` paths (and `applyConfChange`) thread the fragment.

**Writer specifications to state or strengthen.** Each is about one Go function. Items 1–10 are
trust-boundary statements, item 11 is provable, item 12 is a soundness check.
1. `bootOk` (premise): replace `Hfl`/`Hfa`/`Hfal` with `rbOwn d.γB (rbData d.P D)` (from
   `newPost`) and `⌜∀ n ∈ restBuckets, bktOf D n = ∅⌝`.
2. `lease.NewLessor` (axiom): drop `bkFresh`; `lessorBackend`/`leaseBatchTx`'s `UnsafePut`
   (`LessorBackend.lean:50-63`) takes and returns `rbOwn`. The proved `lessor.Grant`/`Checkpoint`/
   `persistTo` and `isApplyLessor`'s `Grant`/`Checkpoint` clauses thread it.
3. `auth.NewAuthStore` (axiom): takes `rbOwn r` with `r.auth = ∅` and returns `rbOwn (r with auth
   := authBoot)`. **It must take the fragment: its `commitRevision` writes.** The write clauses of
   `isAuthStore`/`isReqAuth` take it.
4. `v3alarm.NewAlarmStore` (axiom) and the `restoreAlarms` spec: the fragment replaces `bkFresh`
   (read-only: `restore` reads an empty bucket). `Activate`/`Deactivate` in `isAlarmStore` take it.
5. `isCluster.SetVersion` (`#Hisc` premise): `rbOwn r` to `rbOwn (r with cluster := insert
   clusterVersionKey (semverStr σ))`, where `v` points to semver `σ` (`semver.MustParse`'s spec
   must expose the parsed value).
6. `isCluster.UpdateAttributes`: the `members` effect, plus the in-memory member state (see 5).
7. `isCluster.SetDowngradeInfo`: takes the fragment (unreachable).
8. `EtcdServer.applyConfChange` (axiom): takes `rbOwn r`. On `v3`, validation is `ccValid
   r.members r.removed cc` (the members' read is `ReadTx`, true because the apply thread is the
   sole writer and `Unlock` writes back). On success `members` gets the entry's member record; on
   failure nothing changes. The context model `ccContextOf` must give the member record
   (`ccMember`), not only `(id, IsPromote)`.
9. `backend.Snapshot` (axiom, S-f #1): the observation's restatement above.
10. S-j's `Recover` axioms (lessor, auth, cluster) and `OpenBackend`/`OpenSnapshotBackend`'s
    `newPost`: they take and return the new backend's `rbOwn`, with contents from `bkRestAt`.
11. `NewServer`, `apply`/`applyEntries`/`applyEntryNormal`/`applyAll` (proved): thread the
    fragment and establish `applyRes`'s new conjunct. A non-writing entry needs `restStep = id`.
12. Soundness check: every axiom or premise whose Go code writes an `RB` bucket and whose
    precondition includes `isBackend` is **false** in the new model unless restated with the
    fragment. These are items 2, 3, 5–8 and the alarm/auth clauses. `monitorStorageVersion`'s
    axiom stays true unchanged: it writes `meta` only.

**Size estimate.**
- *Tracking:* about 40–55 files touched, no new axiom, about 8–10 trust-boundary statements
  restated.
  - Backend: about 15–20 files, mostly copies of the `hkd` pattern: `Model2`, `InvBackend`,
    `InvBatch`, the commit and write-back lemmas, `New`/`NewAlloc`/`InvNew`, 6 put/delete/
    delete-bucket specs and proofs (buffered and plain), the `Snapshot` spec, `hookStep` and
    `OnPreCommitUnsafe`, `BackendBridge`.
  - Server: about 10 files: `InvBoot`, `BootBackend`, `NewServer`, `InvRun`, the 4 apply-loop
    proofs, `InvImage` (`restModel`; `clusterBktOf` becomes defined), the `applyConfChange` spec.
  - Apply package: about 6 files with the narrowed `rqOk`: `Contracts`, `Chain`, `dispatch`,
    `ClusterVersionSet`/`ClusterMemberAttrSet`/`DowngradeInfoSet`. About 30 without the narrowing.
  - Lease: about 4 files. Constructor specs: about 4 files.
- *Determinism axiom plus `srvRestSole`:* about 4–6 files (the axiom; `snapOf` in `Snapshot`'s
  post; `srvRestSole` in `bootOk`/`NewServer` and minted again for a received image; `Recover`
  axioms over `bkRestAt`). It adds 1 axiom and 1 premise, both global claims that rest only on the
  S-0 code reading (all writers on the apply path, seven exceptions). That reading cannot be
  re-checked as the code moves, and `clusterBktOf` stays opaque.
- *What tracking buys besides removing them:* the cluster bucket's contents become stated (making
  `clusterVersionMono`'s after-restore claim provable), and it gives the means to discharge D22j
  (B).
- *What it does not cover:* the determinism axiom's other half, "no compaction key in the image".
  `bkNoCmp` would need the same treatment (track `meta/scheduledCompactRev` and
  `finishedCompactRev` as keys whose sole writer is `store.Compact`, unreachable) or stay as a
  separate small item.

**New environment premises?** One widening, of a kind that already exists. Today the fresh
data directory's facts are `HD` (Key view empty) and the opaque `bkFresh` for `lease`, `auth`,
`alarm`. Tracking needs `∀ n ∈ restBuckets, bktOf D n = ∅` in `bootOk`, which also covers
`members`, `members_removed`, `cluster`, `authUsers` and `authRoles`. It is true for a new cluster
without a WAL: bbolt creates the file empty, and B1 creates the membership buckets empty. To make
`members` exact across a restore (see 5) two more facts are needed:
- the static members' peer URLs are pairwise distinct and their ids fresh (from the deployment's
  `dir`/the initial-cluster map; check whether `bootOk`'s `memberRO dir` gives disjointness, or add
  it);
- every member's bootstrap in-memory member list is the same function of the initial-cluster map
  and token. putget3's three configurations do share the map and the token
  (`examples/putget3/putget3.go`, `startMember`).

No premise is needed about other processes: the gRPC and peer network is the program's closed
world.

## 5. What makes tracking harder than it looks

1. **`UpdateAttributes` writes the in-memory member (exception 7, reachable).**
   - It saves `json(c.members[id])` (`cluster.go:467-496`) and panics if `id` is in neither
     `c.members` nor `removed`.
   - `c.members` starts as bootstrap's list. Each boot `AddMember` replaces an entry with the
     entry's member, but only if validation passed.
   - If a boot entry failed validation on some member, that member's `members` bucket and
     in-memory list diverge. After a restore the receiver loads its in-memory list from the bucket
     (`UnsafeLoad`, `cluster.go:255-260`), so its next `UpdateAttributes` differs from the sender's
     (or it panics).
   - So `bucket = restModel L` across a restore needs either the cluster's in-memory state as ghost
     state in `isCluster`, or a proof that the boot entries validate on a fresh member (D22j (B):
     `ValidateConfigurationChange`'s URL and id checks, `cluster.go:306-391`, with `ccContextOf`
     extended to the member record).
   - The weaker "invariant, not function" form (every record is a static member's) does not give
     the receiver's `rcLocalIn` either: that needs all static members present.
2. **Hooks.** `hookStep` currently lets the pre-commit hook change any hook bucket, which today
   includes every rest bucket (`Model2.lean:296-299`). The hooks' contract must be strengthened
   (RB unchanged). The server's hook writes only `meta` (`hooks.go:45-54`), so its proved
   `OnPreCommitUnsafe` should still go through.
3. **`Recover`'s `ForceCommit`s (exception 1)** write the receiver's own stale
   `meta/confState` (`lessor.go:834` through the shared `beHooks`). This is in `meta`, not a rest
   bucket, so tracking is unaffected, as long as `meta` stays free except ci/term and the
   compaction keys. Do not put `confState` in `RB`/`HK`. The idempotent bucket creations of
   B2/B4/B13 need no fragment only if `RB` is tracked through `bktOf` (absent = empty).
4. **The storage-version monitor and the names-only monitors.**
   - `monitorStorageVersion` holds the batch lock with the whole `isBackend` (`srvSVRes`,
     `E/InvStorageVersion.lean`). `publishV3`/`monitorClusterVersions` get `isServerReq`, which
     includes `isAuthStore`/`isApplyLessor` write clauses (`E/InvMonitors.lean:80-82`).
   - Today only their docstrings keep them off the rest buckets. With tracking their axioms stay
     true unchanged (they get no fragment, and the Go code writes `meta/storageVersion` only,
     `schema.go:130-133`). The model then enforces it.
   - This is also why the batch-tx tokens are no frame: `srvWTPool` shares the fungible `wbTok`s
     between the monitor and the apply thread.
5. **Axioms that become false if not restated** (§4, item 12). The main one is `NewAuthStore`,
   because of `commitRevision` (`auth/store.go:994-995`). Because the backend's put spec will
   demand the fragment, every axiom with `isBackend` whose Go code writes `RB` must be re-audited.
6. **Reads through `ReadTx`.** Validation, `UnsafeLoad`, the lessor's and alarm store's restore,
   and the auth store's enabled flag and revision read the rest buckets through the readers' view,
   which hides `HB`. Their axioms must state the result from the fragment the caller holds. That is
   true only while no session with pending rest writes is open, which holds because the apply
   thread is the sole writer and `Unlock` writes back (and commits pending deletes).
7. **Per-member nondeterminism** (exceptions 4–6: the `minLeaseTTL` clamp, `checkpointPersist`,
   legacy bcrypt). All of it is in unreachable writers (B11, B12). `restModel` need not model it
   under the current workload. Lifting `noGrant` or auth-off later needs the
   `ElectionTicks`/`TickMs`/`checkpointPersist` agreement premise, and auth's clause must hold "up
   to password hashes" (decisions.md, "D22's environment assumptions approved" (3)).
8. **The cluster version's value** is `ver.String()` of `semver.MustParse(r.Ver)`, not `r.Ver`
   itself (`schema/membership.go:154`). The `SetVersion` clause needs the parsed value, and
   `semver.MustParse`'s spec must expose it. `MustDetectDowngrade` in `SetVersion` (`cluster.go:611`)
   is a panic path the contract currently ignores (it is unreachable at a fixed binary version).
9. **No new Go bug** was found in this pass.
