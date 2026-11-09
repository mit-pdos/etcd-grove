# Batch 2e: a member's bootstrap, storage, stop and restart; the server's smaller API packages

Author's report, round 0 (draft, before review). 2026-11-09.

## Build

`etc/specs-build.sh` of every 2e module by name (the `etcdserver/` directory is shared with 2c and
2d, so `--dir` builds their files too): **135 modules OK**. **Blocked, not by 2e**: the 11 modules of
`api/v3election/` and `api/v3lock/` import 1d's `Spec/go_etcd_io/etcd/client/v3/concurrency/Api.lean`,
which fails at line 511 (`ctxPrin`'s signature changed in W0's uncommitted `ApiClient.lean`/`Model.lean`
edits). Rebuild them once 1d/W0 settle.

**Infrastructure fix the coordinator must port** (it blocked every module importing
`Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver`, i.e. all of 2c/2d/2e): three defects of
`etc/gen-specs-pkginit.py`, fixed in a copy (`/tmp/gen2e.py`, not in `etc/`) with which I
regenerated `Spec/PkgInit/` (161 generated files changed, plus 6 new):
1. `perennial_instances`' regex `pkg_id\.([A-Za-z0-9_.]+)` misses `«unsafe»`: add `«»` to the class
   (bbolt's init then imports `Perennial.Proof.unsafe.Base`, not a missing `Spec.PkgInit.«unsafe»`).
2. Anonymous instances of packages with the same last path component get the same auto name
   (`internal/syscall/unix` and `golang.org/x/sys/unix`: "environment already contains"): every
   package whose last component is shared gets `instance pkgInit_<path with _>`.
3. Guillemet-escaped names (`«attribute»`, `«meta»`) were looked up as file paths with the
   guillemets: strip `«»` for paths (`fpath`), keep them in module names (6 missing modules written).

## Files

Vocabulary (one `Api.lean` per package; namespaces new on the branch: `Config`, `Features`, `Wal`,
`ServerStorage`, `Snap`, `Membership`, `V3compactor`, `V3alarm`, `V2stats`, `V3election`, `V3lock`,
`Leasehttp`; `EtcdServer` shared with 2c/2d):
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiBoot.lean` (the hub's vocabulary)
- `Spec/go_etcd_io/etcd/server/v3/{config,features,storage,storage/wal,lease/leasehttp}/Api.lean`
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/{snap,membership,v3compactor,v3alarm,v2stats,v3election,v3lock}/Api.lean`

Specs (133 files): `etcdserver/` 44 (`NewServer`, `bootstrap` (trusted), `Start`, `start`,
`HardStop`, `Stop`, `Cleanup`, `GoAttach`, `publishV3`, `purgeFile`, `adjustTicks`, the five
monitors, `monitorFileDescriptor`, `restoreAlarms`, `newCorruptionChecker`, `addFeatureGateMetrics`,
the three `bootstrapped*.Close`, `bootstrappedRaft.newRaftNode`, the getters `MemberID`, `Leader`,
`Lead`, `AppliedIndex`, `Term`, `Logger`, `RaftHandler`, `CutPeer`, `MendPeer`, `StoppingNotify`, the
`util.go`/`tracing.go` helpers); `config/` 7; `features/` 1; `storage/` 15 (`NewStorage`,
`storage.{Save,SaveSnap,Release,Sync,Close,MinimalEtcdVersion}`, `OpenBackend`,
`OpenSnapshotBackend`, hooks 3, quota 4); `api/snap/` 8; `api/membership/` 18; `api/v3alarm/` 5;
`api/v2stats/` 8; `api/v3compactor/` 18; `api/v3election/` 6; `api/v3lock/` 3; `lease/leasehttp/` 1.

Snippets: `examples/specreq/etcdserverboot/` (`go vet` clean): `boot.go` (`ReqStartOne`,
`ReqStartThree`, `ReqRestart`, `ReqJoin`, `ReqPartition`, `ReqStopAfterError`,
`ReqCleanupBeforeStart`), `storage.go` (`ReqSaveOrder`: the WAL's trusted model against a real
`wal.Open`/`ReadAll`; `ReqQuota`), `snap.go` (`ReqSnapRoundTrip`), `members.go` (`ReqMembers`),
`compactor.go` (`ReqCompactorLifecycle`).

## Exported vocabulary

`EtcdServer` (`ApiBoot.lean`):
- `dataDirFresh ds`: a data/WAL directory pair with nothing of etcd's (program start; excl., timeless).
- `memberBoot γ ms m`: initial member `m` of the cluster allocated with `ms` may start once.
- `memberUrls γ U` / `memberJoin γ urls`: peer-URL sets taken; the right to join once with `urls`.
- `memberDisk γ id ds`: a stopped member's durable state in `ds` (excl., timeless, client-owned).
- `memberStart γ cfg c`: the right to start a member of `γ` with `cfg` (three intro laws).
- `srvMember s γ id` (persistent), `srvBuilt s γ id cfg` (excl.), `isServer s γ` (persistent: 2c's
  handle), `srvRunning s γ id ds` (excl.).
- Internal: `bootOk`, `bootRaftOk`, `bootBackendAt`, `srvPublish`, `srvPurge`, `stoppingCh`,
  `srvClosers`, `srvClosed`, `isCorruptionChecker`.
- Provisional slots/names of other batches: `raftNodeBootCfg` (2d), `v3rpcBootCfg` (2a),
  `mvccBootCfg` (3e), `rafthttpBootCfg` (2f), `backendBootRes` (4a), `leaseBootRes` (3c),
  `authBootRes` (3d), `raftNodeBuilt` (2d), `raftHandler`, `transporterOk` (2f), `irrIsRevoke` (3h),
  `gaugeVecOk` (W0's metrics).
- Laws: `cluster_alloc`, `memberUrls_take`, `memberStart_new`, `memberStart_join`,
  `memberStart_restart`, `srvBuilt_closers`, persistence/timelessness/exclusivity/agreement of the
  above.

`Config`: `Model`, `cfgHeap cfg c` (persistent), `Dirs`/`dirsOf`, `backendPathOf`, `walDirOf`,
`snapDirOf` (opaque paths), `reqTimeoutOf`, `electionTimeoutOf`, `peerDialTimeoutOf` (Go's wrapping
arithmetic). `Features`: `serverGate fg` (+ `serverGate_ptr`).
`Wal` (trusted model): `Recs` with `save`, `saveSnap`, `release`, `validSnaps`, `newest`,
`readable`, `entsAfter`; `walRecs wd R`, `walOpen w wd`, `walPurgeRight wd`.
`ServerStorage`: `diskOk` (the environment premise), `isStorage`, `storageOpen` (fractional),
`storageIface`, `isHooks`, `isQuota`, `quotaReq`; provisional 4a: `beOpen`, `beReadable`, `beTx`.
`Snap`: `isSnapshotter`, `snapDbs sd F` (the db files, by index), `saveAt`, `releaseBelow`,
`isMessage`, `msgClose`, `msgCloseCh`; provisional: `BeImage`, `emptyImage`, `beFile` (4a),
`dbReader` (2f), `rcClose` (io).
`Membership`: `memberIdOf` (opaque SHA-1), `initialMembers`, `ClusterSt` (`add`, `remove`, `update`,
`isMember`), `isCluster`, `clusterSt` (TaDa view), `memberPts`, `membersOwn`, `beView`, the
conf-change check `decodeCtx`, `decodeMember`, `ccPanicFree`, `ccResult`, `VErr`, `vErr`;
provisional 4b `beMembers`.
`V3compactor`: the slot `bootCfg mode ret ac` (`_off`, `_on`, `_build`), `compactable`, `revGetter`,
`isCompactor`, `isPeriodic`, `isRevision`, `clockOk`.
`V3alarm`: `kindOf`, `getOf`, `raise`, `clear`, `isAlarmStore`, `alarmSt`, `alarmMemberRO`;
provisional 4b `alarmBe`, `beAlarms`. `V2stats`: three persistent handles.
`V3election`, `V3lock`: server handles and provisional message ownership. `Leasehttp`: `rtOk`.

## Main changes from the old specs

- **`NewServer` is no longer a hub of inline premises**: one triple for every mode (the old
  `specG`/`spec`/`specM` twins gone), each subsystem by one sealed slot (the slot convention), the
  boot resources one `memberStart` (new member, joiner, restart), the post two predicates
  (`srvMember`, `srvBuilt`) where it was eighteen conjuncts. Thread/receipt bounds, claim maps,
  ghost names chosen before the call, the auth/compaction coupling: inside the owners' slots or gone
  with W0's model (quota refusals and the `NOSPACE` alarm are in the model: no workload premise).
- **Restart from any durable state** (`memberStart_restart`, `memberDisk`): the R2d'a restart
  premises do not return; `memberDisk`'s intended realization ties every binder to the files (WAL
  records, snapshot dbs, backend image), and the consistent index is not bounded by the WAL's commit.
- **The WAL** as a trusted records model under logically atomic `Save`/`SaveSnap`/`Release` (the
  release's premise is a saved snapshot record: the old latent `walBaseLb` gap), `Close` taking the
  purge right.
- **The compactor** needs no permit: auto-compaction is an environment step; its slot couples the
  configuration with `EnvCfg.autoCompact` only (plus the periodic `|ret| ≥ 10ns`, a real panic).
- **Membership and alarms** are TaDa views (`clusterSt`, `alarmSt`) the server's invariant ties to
  `State.members`/`State.alarms`; the conf-change validation is a stated relation (`ccResult`).
- The sweep's decided repairs: `NewMessage` with a close contract and a size premise, `purgeFile` and
  `adjustTicks` over `isServer`, zap loggers by `Zap.isLogger`, `envVerifyOff` in the backend's slot.

## Left out (with the reason)

- `TryTransferLeadershipOnShutdown`, `MoveLeader` (called by `Stop`, no old spec; their effect is a
  raft leadership transfer), `stopWithDelay`, `ReadyNotify`, `StopNotify`, `Defragment`, `Alarms`.
- To 2c: `interface.go`'s read-loop methods, `FeatureEnabled`. To 2d: `Process`, `IsIDRemoved`,
  `ReportUnreachable`, `ReportSnapshot` (I never wrote them; the coordinator's ownership call).
- `AlarmStore.restore` (names-only helper under `Recover`'s trusted claims), `passthroughQuota`'s
  constant methods, `RecoverSnapshotBackend` and `bootstrap`'s other helpers (untranslated, inside
  `bootstrap.spec`), every `wal.*` function (no translated caller: the WAL is reached through
  `serverstorage.Storage` and `bootstrap`), `electionServer.Observe` (no old spec), the corruption
  checker's methods (their only effect is a `CORRUPT` alarm, an environment step), the old trusted
  `clusterImageOk_restModel` and `Message__fields` (replaced by `memberDisk`'s realization and
  `isMessage`), `RaftCluster` methods only untranslated code calls (`VotingMembers`,
  `MemberByName`, ...), `isConnectedToQuorumAfterAddingNewMemberSince`, `longestConnected`.

## Open questions for the user

- **Q1 (K2, a deviation from W0's suggestion).** A joining member is started by a token per peer-URL
  set (`memberJoin γ urls`), not by `etcdLb` naming the member: `bootstrap` gives a joiner the id the
  cluster *currently* has for its URLs, so a token per id is unsound if those URLs were removed and
  re-added under another id. Cost: a removed initial member's URLs cannot be joined again. Accept?
- **Q2 (crashes).** `memberDisk` comes back from `HardStop`/`Stop` only. A restart after a crash needs
  the durable state client-owned *while running* (a persistent update the server fires at each WAL
  fsync, as raft's `readyEnter`), and a crash rule for commit-only states the WAL does not fsync.
  In scope now, or later?
- **Q3.** On a `NewServer` error the start right is lost (the directory may hold a half-made WAL or
  backend; a started raft node leaks if the transport fails). A program cannot retry a failed start.
- **Q4.** `bootstrap.spec` excludes `--force-new-cluster` and discovery (scope restrictions), and
  trusts the remote peers' membership answers (`GetClusterFromRemotePeers`,
  `isMemberBootstrapped`) to be `γ`'s members'.
- **Q5.** Members with different `--max-learners` could decide a learner add differently: a premise
  that all members share it?
- **Q6.** W0's `EnvCfg.leaseExpiry = false` mode needs a time-based deployment premise in the lessor's
  slot (no lease expires during the run); keep the mode?

## `req/` sections written (`## from 2e`)

`go_etcd_io_etcd_server_v3_etcdserver.md` (to 2c: `isServer` after the stop, the compactor's
`Compact`, `publishV3`, ownership; to 2d: `start`→`run`, the stop's deposit, the transport's entry
points before `Start` (2f's F4), `raftNodeBuilt`, `Save`'s update composition, `UpdateAttributes`'s
premise, `--max-learners`), `..._etcdserver_api_rafthttp.md` (2f's F1-F4: the handler at `/`,
re-serving after a restart, `SaveDBFrom` as an update over `snapDbs`, `raftOk` at `NewServer` time,
the slots), `go_etcd_io_raft_v3.md` (the restart snapshot's configuration at `ci > si`),
`..._storage_backend.md`, `..._storage_schema.md`, `..._storage_mvcc.md`, `..._lease.md`,
`..._auth.md`, `..._etcdserver_api_v3rpc.md`, `go_etcd_io_etcd_api_v3.md` (W0: K1/K2 as stated),
`go_etcd_io_etcd_api_v3_etcdserverpb.md`.

Requirements on 2e from others, checked: 2d's on `storage` (my `Save` is an update over `walRecs`
in which 2d fires `readyEnter`; `Close` keeps `walRecs` with its owner), on `membership` (the views
are TaDa; validation reads the backend's view), on `snap` (2d's `NewMessage` met; 2f's persistent
`dbSaved` answered by the update over `snapDbs`, F3). No `req/..._storage_wal.md` existed.
