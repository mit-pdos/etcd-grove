# Repair: group `server-boot` (etcdserver/api membership, snap, v2stats, v3alarm, v3compactor, v3election, v3lock; storage top level and wal; config; features)

Reports: the 2e parts of `A8-server-boot-transport-{provability,completeness}.md`, the v3lock/v3election
findings of `A3-client-users-completeness.md`, A7 completeness F2 (the compactor's contract, my
`v3compactor/Api.lean`), and the coordinator's relays from raft-core, lease-auth and client-users.
Paths are under `Spec/go_etcd_io/etcd/server/v3/` unless a path is given. I own no snippet package
(`etcdserverboot` is server-core's, `rafthttp` is rafthttp's), so snippet changes are requests.

## A8 provability

- **F1.1 `crashScope` parameterless; `disk_crash`.** Not fixed: `ApiBoot.lean` is server-core's.
  See the request below. The WAL and snapshot laws it needs now exist (F1.2, F1.3, F9).
- **F1.2 No WAL crash law.** Fixed in `storage/wal/Api.lean`:
  - new `walWriting wd R w`, a write in progress (`WalWrite`: `.save hs k es` or `.saveSnap s`),
    with `walWriting_timeless`, `_excl`, `_recs_excl`;
  - `WalWrite.apply` and `Recs.crashedDuring`;
  - two trusted crash laws, `walRecs_crash` (at rest: `Recs.crashed`) and `walWriting_crash`
    (in flight: `crashedDuring`). Both take the old generation's `crashed` and give `walRecs` at
    the next generation's heap `⟨hG.goose_globalGS, L'⟩`, as bbolt's `boltCrash` does. No OsFs
    `crashRest` is threaded: `walRecs` is a trusted ghost variable, not built over OsFs.
  - `storage.Save.spec` and `storage.SaveSnap.spec` now take two nested updates. The first moves
    `walRecs R` to `walWriting R w` before the first byte is written. The second moves it to
    `walRecs (w.apply R)` once the write (and its fsync, when `mustSync`) is done.
  - The "no crash in scope" notes are gone from the header, `Save`, `SaveSnap` and `Sync`.
    `Sync`'s margin says the synced commit is not raised. This is weaker than the code and lines
    up with raft's `wcommit`.
- **F1.3 `crashedMid` is missing the synced-new-state case.** Fixed. `Recs.crashedMid` now takes
  `hs` and has a second disjunct: all the entries with the new state record, not yet fsynced
  (`crashed {R.save hs k es with syncedCommit := R.syncedCommit}`).
  - **Coordination with raft-core** (their split `raftState_crash`, relayed): the WAL's two cases
    are exactly raft's two whole-record cases.
    - A prefix `j` with the old record is raft's first case: commit in `[wcommit, D.commit]`, given
      `walHolds`' correspondence `syncedCommit ↔ wcommit`, `hs.commit ↔ D.commit`.
    - All entries with the batch's record is raft's second case at `j = |b.ents|`.
    - An empty `hs` (no state record written) falls under the first case.
  - **What I assume** of raft:
    - `raftState_crash` as now stated;
    - raft's side condition `hs.commit ≤ last` holds because a state record's commit never exceeds
      the entries written before it (`walHolds`' realization, server-core's);
    - `confAboveOk` (their new durable invariant "at most one conf entry above `wcommit`") stays
      `crashScope`'s first conjunct, in server-core's `ApiBoot`.
  - `diskOk` now names the torn-tail assumption: a crash corrupts no record behind a surviving
    one, otherwise `ReadAll` fails with `ErrCRCMismatch` and `bootstrap` exits.
- **F1.4 The backend crash is unreachable from `disk_crash`; provisional names.** My half is fixed
  (see F5). The per-generation `disk_crash` that threads `crashRest` is server-core's (request).
- **F2 `diskAcc`'s masks.** Not fixed: `ApiBoot.lean` (request).
- **F3 Self-stop under in-flight reads.** Not mine: server-core's `run`/`srvGate`. It is a
  recorded-decision candidate (the fork's gate).
- **F4 Member ids reserved by raft.** Filed as `nonissues/etcd-member-id-raft-reserved.md`
  (blocks-proof: no; probability about 2^-63). `membership/Api.lean`'s `memberIdOf` docstring
  points to it. The premise on `cluster_alloc` is server-core's (request).
- **F5 Provisional storage names never bridged to 4a.** Fixed, except the hooks:
  - `Snap.beFile` is now an abbreviation of 4a's `Backend.beFile`. The duplicate laws are dropped
    (4a's `beFile_timeless`/`_excl` apply). `Snap.emptyImage` is gone (4a's `Image.empty`).
  - `OpenBackend.spec` is now 4a's `Backend.New.spec` passed through: the client's allocation
    step `Pk`/`K`, buckets `Bs`, hooks' footprint `Fh`, `isBackend`, `beDurInv`, `beSynced`. Its
    new premises are `Backend.envOk`, `Backend.safeRegOk`, `threadTok` (the commit loop's) and
    `cfg.MemoryMlock' = false`. 4a's `dbOpenOk` of the built config is `diskOk`'s.
  - `OpenSnapshotBackend.spec` is restated the same way. The allocation step receives the image
    through `Q (some img)`; the error arm gives the thread token back.
  - **`os.Rename` vs the snapshotter's model.** Fixed by a trusted bridge, `Snap.dbFile_rename.spec`:
    a triple for `os.Rename(dbPathOf sd i, dst)` over `snapDbs`/`snapGone`/`beFile`.
    `DBFilePath.spec` now returns `path = dbPathOf sd id` (new opaque pure `dbPathOf`).
    `OpenSnapshotBackend`'s sketch now cites these. I chose a use-specific trusted triple over the
    reviewer's `snapDbs ↔ osMeta` bridge, because `snapDbs` is itself a trusted ghost variable that
    is not realized over OsFs.
  - `ServerStorage.beOpen` is marked superseded. It stays declared only because server-core's
    `bootstrap`, `applySnapshot` and `bootstrapped*.Close` still mention it (request).
  - **Not fixed:** `beReadable` and `beTx` are still provisional. The hooks'
    `OnPreCommitUnsafe.spec` does not yet give 4a's `hookOk γ (hooksIface h) Fh Pk`, which the
    allocation step needs. That requires `cindex`'s backend vocabulary (server-core). I added
    `hooksIface`.
- **F6 v3lock/v3election prefix.** Fixed, together with A3 F1 below.
- **F7 `diskOk`'s text.** Fixed. Its docstring (`storage/Api.lean` header) now lists every
  excluded failure: the WAL's I/O, the torn-tail crash assumption, `DBFilePath`'s `ReadDir`,
  `ReleaseSnapDBs`' open/list/remove, `SaveDBFrom`'s directory fsync, the install's rename and
  bbolt's open. Per spec:
  - `SaveDBFrom`'s error arm is now true: errors before the rename change nothing, and the
    directory fsync's error is `diskOk`'s;
  - `ReleaseSnapDBs`' and `DBFilePath`'s sketches name their `diskOk` cases.
- **F9 `snapDbs` and the crash.** Fixed in `snap/Api.lean`:
  - `snapSaving sd F i img`: a save between its rename and its directory fsync.
    `SaveDBFrom.spec` now has two nested updates: one at the rename, one after the directory
    fsync.
  - `snapGone sd H`: removed images a crash may bring back. Neither removals
    (`ReleaseSnapDBs`, the install's rename) nor any directory entry is fsynced.
    `ReleaseSnapDBs`, `storage.Release`, `OpenSnapshotBackend` and `dbFile_rename` now move it
    (`goneAdd`).
  - The transparent `snapCrashed F H F'`: a present file stays, and an absent one stays absent or
    comes back with an `H` image.
  - Trusted laws `snapDbs_crash` and `snapSaving_crash`, per generation.
  - Laws `snapSaving_timeless`/`_excl` and `snapGone_timeless`/`_excl`.
- **Second tier.**
  - `NewMember` reading `*now`: not changed (trusted; noted).
  - `ReqJoin`, `ReqStopAfterError`, `ReqStartThree`, the `Cleanup`-before-`Start` margin and
    `imgBytes` are other groups' (server-core, rafthttp, backend-schema).
  - `Http.Serve`'s handler bound is rafthttp's.

## A8 completeness

- **F1 `EtcdServer.MemberList`.** Server-core's (request).
- **F2 `urlsRight` raw vs `urlsNorm`; spent on refusal.** Not mine: W0's `urlsRight`
  (client-core, `api/v3/State.lean`), `urls_reserve`/`memberJoin` (server-core `ApiBoot`) and
  `EtcdServer.AddMember`/`UpdateMember` (server-core). See the requests.
- **F3 `RaftCluster.Version`/`SetVersion`/`SetDowngradeInfo`, `isCluster ⊢ clusterOk`.** Fixed in
  `membership/`. This also answers lease-auth's request.
  - New vocabulary:
    - `VerSt` (version and downgrade info) and `binaryVer` (trusted constant);
    - `verFits sv`: it parses back from `String()`, and the binary's major.minor is not below it
      (`MustDetectDowngrade`);
    - `VerSt.ok`;
    - `clusterVer γ v` (exclusive, timeless) and `beVer c v` (the backend's), with
      `clusterVer_timeless`/`_excl`;
    - `clusterVerN` and `clusterVerInv γ`, an invariant over `clusterVer`.
  - New trusted specs:
    - `RaftCluster.Version.spec`: a read update; `nil` or a fresh `Semver.verAt`.
    - `RaftCluster.SetVersion.spec`: premise `verFits`; the view always, the backend at
      `shouldApplyV3`; `onSet`'s contract as a WP premise.
    - `RaftCluster.SetDowngradeInfo.spec`.
  - **`clusterOk`:** I did not state a law with lease's `clusterOk` in it, since that would make
    membership import lease. `Version.spec` plus `clusterVerInv` is exactly lease's transparent
    `clusterOk` triple; the step from the interface call to the concrete method is the usual one.
    The server allocates `clusterVerInv` at `NewServer` (request).
  - `Apply.clusterVerOk ver` can now be defined as `∃ sv, Semver.parse ver = some sv ∧
    Membership.verFits sv` (apply-txn's; request).
  - **Not done:** `RaftCluster.Recover`'s own `MustDetectDowngrade` over the backend's stored
    version is not restated.
- **F4 v3lock/v3election messages tied to 3h's.** Fixed:
  - `V3lock.lockReq`/`unlockReq`/`lockResp`/`unlockResp` are now abbreviations of
    `V3lockpb.*`;
  - `V3election.LeaderKeyM` and the eight message predicates are abbreviations of
    `V3electionpb.*`.
  - Reading the key from `lockResp` (`resp.GetKey()`) needs a response field law of 3h's
    (request).
  - `v3client.New` stays the recorded gap.
- **F5 Server getters, `MoveLeader`, `Downgrade`, `PauseSending`.** Server-core's (request).
- **S4 `vars_init` docstring.** rafthttp's file (request).

## A3 completeness (v3lock/v3election) and client-users' relay

- **F1 Prefix.** Fixed. Every use is now `name ++ "/"`:
  - `lockServer.Lock`'s effect is `mutexEff (name ++ "/")`; its post is
    `lockedSince (name ++ "/") k cr σ`, plus `k = sessKey (name ++ "/") id` and `Reach σ0 σ`;
  - `electionServer.Campaign`'s effect is `campaignEff (name ++ "/")`; its post is
    `waitedFor (name ++ "/")`, plus `sessKey`, the session's lease in the reply, and the value held
    at a reached `σv`;
  - `electionServer.Leader`'s post is `firstCreate (name ++ "/")` and `Reach σ0 σ`.
  - In each, the session id is the request's lease when that lease is non-zero.
- **F1b `Proclaim` at rev 0.** Fixed. The post is now 1d's: `(ownerCmp x.key x.rev).holds
  σ.kv.store` at a reached `σ`, plus `etcdLb γ (putKey σ x.key value id)`. The false
  create-revision claim is gone.
- **F7 `P` returned.** Fixed on success for `Lock`, `Campaign`, `Proclaim` and `Resign`.
  - The error arms do not return it: the server's errors are not classified, and the margins say
    so.
  - client-users asked for "definite outcomes". 1d's `ErrSessionExpired`/`ErrElectionNotLeader`
    arms return `P`, but the server passes those errors through unclassified, so the caller cannot
    tell them from indefinite ones. Returning `P` there would require the posts to name those
    sentinels' globals.
  - `Unlock` is unchanged (W0's delete triple).
- **F3 `electionServer.Observe`.** Not fixed: its spec needs the `Election_ObserveServer` stream
  vocabulary (`Send`, `Context()`) of `v3electionpb`, which is grpc-v3rpc's (request). 1d's
  `observeAt_recvAu` is ready.

## A7 completeness F2 (the compactor's `Compactable`)

Fixed in `v3compactor/`:
- `compactable c R` is gated on `R`, which `start` publishes, as 3c's `ckptGate`. Its
  introduction restricts the context to a child of `Background()` (the compactor's
  `WithCancel(Background())`), so the server's proof gets `ctxNoIncoming`.
- `isCompactor cp R`, `isPeriodic p R` and `isRevision r R` carry `R`. `Run` takes `□ R`; `Pause`,
  `Resume` and `Stop` do not need it.
- All 14 spec files were updated, each with a `Changes: verify-round` line.

## Sentinel errors (cross-cutting)

- `Membership.vErr` was a Lean constant. It is replaced by `VErr.global` and `vErrs ev`, with a
  new `Membership.init.spec`: the variables are read-only, non-nil and pairwise distinct.
  `ValidateConfigurationChange.spec` now returns `globalAddr e.global ↦□ err`.
- The other sentinels in my packages (`snap.ErrNoDBSnapshot`, `v3election.ErrMissingLeaderKey`)
  appear in posts only as `err ≠ nil`.

## Requests to server-core

1. **`ApiBoot.lean`: `crashScope` and `disk_crash`** (A8 P F1.1, F1.4, F9). Make the scope a
   statement about the crashed disk: either a disjunct `crashOutOfScope γ ds` in `disk_crash`'s
   conclusion, or the scope as a premise of the raft loop's deposit. Then state `disk_crash` per
   generation:
   - `∀ L', … diskState γ ds k ∗ crashGone γ ds ∗ crashed ∗ crashRest(hG, L') Ps ⊢ |={⊤}=> ∃ k', …`
     at `⟨hG.goose_globalGS, L'⟩`;
   - its realization uses `Wal.walRecs_crash`/`walWriting_crash` (the in-flight batch:
     `walWriting R (.save hs k es)` with the batch's `readyEnter` unfired, then raft-core's split
     `raftState_crash`; the two WAL cases match its two record cases), `Snap.snapDbs_crash`/
     `snapSaving_crash` (with `snapGone`), and 4a's `beCrash`.
   - Name `crashGone`'s producer. Also give idle disks a crash law: `diskIdle` is lost otherwise.
   - Add raft-core's durable invariant, "at most one conf entry above `wcommit`", to
     `diskState`'s realization, since `crashScope`'s first conjunct relies on it.
2. **`ApiBoot.lean`: `diskAcc`** (F2). Make it an invariant-style accessor at `diskN`:
   `□ ∀ E, ⌜↑diskN ⊆ E⌝ → |={E, E ∖ ↑diskN}=> ∃ k, diskState k ∗ (∀ k', diskState k' ={E ∖ ↑diskN, E}=∗ True)`,
   with raft's namespace disjoint from `diskN`. The WAL writes now fire two updates (`walWriting`,
   then `walRecs`), each through the accessor; the second fires the batch's `readyEnter`.
3. **`ApiBoot.lean`: `cluster_alloc`** (F4). Add the premise `∀ m ∈ ms, m.id ≠ 0 ∧ isLocalTarget
   (W64 m.id) = false` (`nonissues/etcd-member-id-raft-reserved.md`). For adds, `freshIds_take`
   needs the same of `NewMember`'s id: a refusal disjunct or a scope note.
4. **The storage specs changed shape.** Update the users' sketches and specs:
   - `raftNode.start`: two updates per `Save`/`SaveSnap`;
   - `applySnapshot`, `bootstrap`, `NewServer`: `OpenBackend`/`OpenSnapshotBackend` now return 4a's
     `isBackend` through a client allocation step, with new premises `Backend.envOk`, `safeRegOk`,
     `threadTok`, `MemoryMlock = false`;
   - `bootstrapped*.Close`, `applySnapshot`: stop using `ServerStorage.beOpen`, which I delete once
     unused;
   - the snapshot directory's invariant now also holds `Snap.snapGone sd H`, allocated with
     `snapDbs` at `(fun _ _ => False)`.
   - `backendBootRes` should give `Backend.envOk` (define it, e.g. `envOk ∗ ⌜quota bound⌝`).
5. **`OnPreCommitUnsafe` and 4a's hook contract** (F5). To discharge the allocation step's
   `Backend.hookOk γ (hooksIface h) Fh (Pk γ)`, the hooks need `cindex`'s `UnsafeSave` over 4a's
   session. Say what cindex can give; I will restate `BackendHooks.OnPreCommitUnsafe.spec`/`isHooks`
   over it.
6. **`NewServer`**:
   - allocate `Membership.clusterVerInv γc` and use it with `RaftCluster.Version.spec` for 3c's
     `Lease.clusterOk` at `server.go:344`;
   - build the compactor's `compactable c R` with `R` your started-server resource (A7 F2), and
     pass `□ R` at `start`'s `Run`.
7. A8 completeness F1 (`EtcdServer.MemberList`), F5 (getters, `MoveLeader`, `Downgrade`,
   `PauseSending`/`ResumeSending`), and F2's `AddMember`/`UpdateMember` side (take `urlsRight`
   at `urlsNorm`, or a law). F2's second tier: return `urlsRight` on a fired refusal.
8. **Snippets** (`examples/specreq/etcdserverboot/`):
   - `lock.go` (`ReqLockOverInProc`): the key starts with `name + "/"`, as now stated;
   - `storage.go`/`snap.go`: their `Specs:` lines still hold, but the Go tests could add the crash
     cases (`crashedMid`'s second disjunct, `snapCrashed`), which are not runnable as Go tests;
   - S2: a ready-or-stop receive snippet.

## Requests to client-core (W0)

- A8 C F2: `urlsRight γ ss` is keyed by raw strings, while the server takes it at the parsed
  URLs. Add a law `urlsRight γ ss ⊢ urlsRight γ (urlsNorm ss)` (with `urlsNorm` idempotent and
  order-insensitive), or re-key it by `urlsNorm`.

## Requests to rafthttp

- S4: `Rafthttp.vars_init.spec`'s docstring must say that etcdmain/embed write
  `ConnReadTimeout`/`ConnWriteTimeout` (`embed/config.go:631-632`, `etcdmain/config.go:180-186`).
  Better: take their points-to with the `≥ 5s` fact as a premise of `Transport.Start`.
- `snapshotHandler.ServeHTTP` and `examples/specreq/rafthttp/snapshot.go`: `SaveDBFrom.spec` now has
  two nested updates (`snapSaving` in between). The handler's update builder must supply both.

## Requests to grpc-v3rpc (3h)

- A field or getter law for `V3lockpb.lockResp` (`resp.GetKey()`/`Key`) and for
  `V3electionpb.campaignResp`/`leaderResp`, so that callers can read the reply.
- The `Election_ObserveServer` stream vocabulary (`Context()`, `Send` of a `LeaderResponse`), so
  that `electionServer.Observe` can get a spec (A3 F3).

## Requests to apply-txn

- Define `Apply.clusterVerOk ver := ∃ sv, Semver.parse ver = some sv ∧ Membership.verFits sv`, and
  cite `RaftCluster.Version/SetVersion/SetDowngradeInfo.spec` and `beVer` (your `smAt` should hold
  `beVer c v` beside `beView`).

## Requests to backend-schema (4a)

- `beCrash` and an unsynced rename. `OpenSnapshotBackend` renames a snapshot file onto the
  backend's path with no directory fsync (`backend.go:61-70`; the next `SaveDBFrom`'s directory
  fsync makes it durable). A crash before that may revert the rename: the destination holds the
  backend file it held before. etcd recovers, because the WAL's snapshot index is then above that
  file's consistent index and `RecoverSnapshotBackend` finds the snapshot file again (my
  `snapCrashed` brings it back through `snapGone`).
  - `beCrash`'s conclusion, "one of `γ`'s committed images", is false for that file.
  - It needs a disjunct for a destination renamed onto and not yet synced: the previous file's
    `beFile` (from its own history). Alternatively, a joint law with the snapshotter's.
  - Until then, crash restarts after an install are unproved. This is also a new decision
    (below).

## New decisions

- **WAL and snapshot writes have two linearization points.** A crash needs to know a write is in
  flight, and `walRecs`/`snapDbs` alone cannot say so. So `storage.Save`/`SaveSnap` and
  `SaveDBFrom` now take two nested atomic updates, with an in-flight state (`walWriting`,
  `snapSaving`) between them. Every client fires both (the raft loop fires `readyEnter` in the
  second). The alternative was a single update fired at the start, with a crash relation that may
  lose the write. It was rejected: the model would claim states before they are durable.
- **The snapshot directory's removals are not durable** (`snapGone`). etcd fsyncs the snapshot
  directory only in `SaveDBFrom`, so removals and the install's rename can come back after a
  crash. The client keeps the removed images (`goneAdd`), as 4a's `beHist`, and the crash law only
  resurrects those. For the restart to use a resurrected file, the server's invariant must certify
  every image ever saved at an index, not only the present ones; this holds because the image of
  an index is determined by the committed log.
- **Install-then-crash** (the backend side of the unsynced rename) is not covered until 4a's
  `beCrash` handles it. The user may prefer a scope premise instead ("no crash between an install
  and the next snapshot save"), or a fork fix (fsync the snapshot directory in
  `OpenSnapshotBackend`, which makes the model simpler).
- **`os.Rename` at the snapshotter's files is a trusted triple** (`Snap.dbFile_rename`), not a
  bridge to OsFs. `snapDbs` is trusted the way `walRecs` is.

## Build

`etc/specs-build.sh --dir` over all my directories (wal, storage, snap, membership, v2stats,
v3alarm, v3compactor, v3election, v3lock, config, features): **`specs-build: OK (105 modules)`**.
An earlier run failed in `client/v3/Api.lean` (client-core's, being edited concurrently); the
reruns passed. Not built here: the other groups' modules that use the changed specs (server-core's
`NewServer`, `bootstrap`, `applySnapshot`, `raftNode.start` mention them only in comments or in
`ServerStorage.beOpen`, which is kept). The nonissue file is indexed (`python3 etc/issues-status.py --index`, then `--check` clean).

## Second pass

Items from `second-pass.md` and the coordinator's relays.

- **`electionServer.Observe`**: fixed. New `v3election/electionServer__Observe.lean`, over 3h's
  `observeStreamAt` and `observeStream_send`/`_context`, 1d's `Election.Observe` and
  `observeAt_recvAu`. It needs a read permission only (lease `-1`); its post is no panic, with the
  stream given back. The sent values' facts are not stated: `Send` carries only the reply's model.
- **Hooks over 4a's contract**: not fixed. cindex's `Api.lean` says in prose how `txStoredCI` is
  realized (the session's view of the meta cells, `ciCells`), but `ciCells` is not defined and no
  law relates `txStoredCI tx c` to 4a's `beSess`. Without that law, `isHooks_hookOk` (`isHooks h
  ci ∗ isCI … ⊢ Backend.hookOk γ (hooksIface h) Fh Pk`) cannot be stated over terms that exist.
  Request below.
- **`RaftCluster.Version` vs server-core's citations**: matches. Server-core's
  `EtcdServer.ClusterVersion` sketch says "the caller's `threadTok`". My spec takes none, since
  `Version` only takes the cluster mutex. A caller holding one keeps it.
- **`compactable_intro` gate**: matches `NewServer`/`start` (`R := srvStarted s γ id`, `Run` with
  `□ R`). I added server-core's `phys = false` restriction: the contract covers only
  `compactReqOwn r … rev false`, which is what both loops build (`periodic.go:142`,
  `revision.go:92`).
- **Membership sentinels in server-core's encoding**: fixed. New `membership/Errors.lean` with
  `VErr.etcd` (the `toGRPCErrorMap` mapping; `ErrIDRemoved` and `ErrIDNotFound` both map to
  `memberNotFound`) and `errs_srv.spec`: `isPkgInit membership ⊢ □ ∀ e, EtcdServer.sentinelAt
  e.global e.etcd`. It is a separate module because `membership/Api.lean` cannot import
  `errors/Api.lean` (cycle through lease, mvcc and schema). `init.spec` stays.
- **`SetVersion`'s notifier**: fixed. `SetVersionChangedNotifier.spec` now takes
  `Notify.notifierAt n γn` and `inv clusterNotifyN (∃ k, notifyCount γn k)` (new namespace in
  `Api.lean`). `SetVersion`'s sketch fires `Notifier.Notify.spec`'s update in that invariant.
- **`NewElectionServer` Users line** (and `NewLockServer`'s): fixed. The users are embed's
  `serve.go:149-150` and the integration framework, not `v3rpc.Server`.
- **`ID.String_ptr`**: fixed where my translated bodies call it (`RaftCluster.AddMember` and
  `RemoveMember`'s log lines, pointer receivers). Those sketches cite `Types.ID.String_ptr.spec`.
  The `URLs.*_ptr` calls are in `NewServer`/`setPeerURLsHeader` (server-core and rafthttp), not in
  my files.
- **Three-view `deniedSince`, `Context.Value`**: not mine. They concern 2c's `Range`/`Txn` and
  `raftRequest` (server-core); no spec here fires a denial or reads a context value.
- **`Proto.norm` survival**: nothing to do. I own no message relation: `V3lock.*` and
  `V3election.*` are abbreviations of 3h's relations, whose norm laws are grpc-v3rpc's.
- **raft-core's citation in `wal/Api.lean`**: fixed with their exact text. The second case is now
  bounded by the batch's commit, and the first case is cited with its `D.commit` bound.
  `ApiBoot.lean:130-133` is server-core's file; their report has the replacement text.

### Requests (second pass)

- **To server-core (cindex):**
  - Define `Cindex.ciCells : Backend.Fp` (the meta bucket's `consistent_index` and `term` cells).
  - Add a law tying `txStoredCI tx c` to 4a's session view: inside the pre-commit hook, `beSess γ
    q Fp.none S ∗ ⌜tx = btIface γ⌝ ⊢ txStoredCI tx c ∗ (txStoredCI tx c' -∗ ∃ S', beSess γ q
    ciCells S' ∗ ⌜hookWrites ciCells S S'⌝)`, with `c` read from `S.cur`.
  - The same for `schema.MustUnsafeSaveConfStateToBackend`'s `confState` cell (4b).
  - Then I restate `BackendHooks.OnPreCommitUnsafe.spec` and add `isHooks_hookOk` with
    `Fh := ciCells ∪ confState`.
- **To server-core:** `ApiBoot.lean:130-133`, raft-core's replacement text, if not yet applied.

### Build (second pass)

`etc/specs-build.sh --dir` over all my directories: **`specs-build: OK (107 modules)`**, which
includes the new `membership/Errors.lean` and `v3election/electionServer__Observe.lean`. One
intermediate run failed in `storage/schema/Api.lean` (backend-schema's, edited concurrently); the
rerun passed. I own no snippet packages, so there was nothing to vet.

## Last pass

- **Hooks over 4a's contract:** done.
  - `BackendHooks.OnPreCommitUnsafe.spec` now states 4a's `Backend.hookOk γ (hooksIface h)
    hookFp Pk` of etcd's hooks. It assumes `isHooks h (ciIface l)`, `Cindex.isCI l γci`,
    `Backend.bktsAre γ`, `beMade γ meta`, and the client's obligation `hooksPkOk γ γci Pk`.
  - `hooksPkOk` is transparent and persistent. From `Pk` it gives:
    1. `UnsafeSave`'s `ciState` update, guarded against the session's stored index;
    2. at its commit, the configuration cell's part `beCur γ confStateCells C`;
    3. for the final session, the visibility update of `hookFp` and the way back to `Pk`.
  - `hookFp := Cindex.ciCells ∪ Backend.confStateCells`.
  - The proof sketch cites cindex's `txStoredCI_sess`/`ciCells` and backend-schema's
    `confStateSave_hook`/`confStateCells`.
  - `beTx` is superseded. `OpenBackend`'s note now points to this spec.
- **Recorded gaps** (in the spec's header, as requests):
  - **(a) to backend-schema:** `confStateSave_hook` takes `beLive γ (btLoc γ) 1` and a session at
    `Fp.none`. 4a's `hookOk` lends the hook only `beSess γ q Fp.none S`, and the `UnsafeSave` step
    returns a session at `ciCells`. Either `hookOk` lends the transaction's liveness, or the save
    law takes a session at any footprint.
  - **(b)** The pending configuration's size bound has no source. `SetConfState.spec` (mine) could
    take it, but its model is `Raft.ConfState`, not a `Proto.Content`. This needs raft-conf-pb's
    `encSize` of a configuration; open.
  - **(c)** If server-core decides that `txStoredCI_sess` needs `beCur γ ciCells`, `hooksPkOk`
    gives it the way it gives `confStateCells`' part.
- **`beRevert`** (backend-schema's request): done.
  - `Snap.dbFile_rename.spec` now takes the destination's `Backend.beNoRevert dst`. On success it
    gives `beFile dst (some img) ∗ beRevert dst o`; on error it gives both back.
  - `SaveDBFrom.spec` takes `Backend.beRev p rv` for an entry `p` of its directory
    (`Snap.inDir sd p`, a new transparent definition). Its directory fsync gives `beNoRevert p` on
    success; on error it gives `beRev p rv` back.
  - New Config law `backendPath_entry.spec`: `backendPathOf d = snapDirOf d ++ "/db"`
    (`datadir.go:26-28`). It gives `inDir` for the backend file.
  - `OpenSnapshotBackend.spec` threads the revert state: `beNoRevert` before, `beRevert path o`
    after on success.
- **Requests:**
  - **To rafthttp:** the snapshot handler's `SaveDBFrom` call now passes the backend file's
    `beRev`; any `p` with `inDir` and `rv`, or `rv` from the server's invariant.
  - **To server-core:** `applySnapshot` holds the `beRevert` that `OpenSnapshotBackend` returns
    until the next `SaveDBFrom`. `bootstrap`'s opener needs `beNoRevert` of the backend file;
    4a's `beFile_of`/`beFile_none` give it.
- **Build:** `etc/specs-build.sh --dir` over all my directories: **`specs-build: OK (107
  modules)`**.

## Final relay round

- **`SaveDBFrom`'s revert state now sits in the second update** (rafthttp's request). The spec no
  longer holds `Backend.beRev p rv` for the whole call. The directory-fsync update, the real atomic
  point, is now `AU <{ ∃∃ rv, snapSaving sd F id img ∗ Backend.beRev p rv }> @ ⊤, ∅ <{ snapDbs sd
  (saveAt F id img) ∗ Backend.beNoRevert p, COMM Q }>`, for an entry `p` of the directory
  (`⌜inDir sd p⌝`). The call's pre and post are back to `au` and `Q` (or `au` returned on an error).
  Two concurrent snapshot handlers can each call it; rafthttp's `saveOk` can go back to two
  updates with no loan.
- **Build:** `etc/specs-build.sh --dir` over `snap` and `storage`: `specs-build: OK (26 modules)`.
