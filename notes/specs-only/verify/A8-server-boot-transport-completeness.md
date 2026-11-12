# A8 (server boot, storage, stop, membership, transport): completeness

Reviewer: completeness, verification round 2026-11-09, at `1aa6fc1337`. Batches 2e and 2f.
Read-only; the findings were written before `batch-*.md`, `integration-*.md` and `open-questions.md`
were read. Afterwards they were read only to mark which findings are recorded open decisions.

Go sources: `.lake/src/server` (`a4d2bb17`). Users:
- etcd's `embed` (`embed/etcd.go`, `serve.go`) and `etcdmain` (both in the module cache);
- the integration framework (`tests/v3@…a4d2bb1720b9/framework/integration/cluster.go`);
- `examples/lib/{etcdstart,cluster3}` and `examples/etcd/restart`;
- the callers in this repository with specs of their own (2a `v3rpc`, 2c/2d `etcdserver`, 3a `apply`,
  3c `lease`, 1c `client/v3`);
- W0's cluster contract (`top.md` K1-K8).

## Verdicts

| batch | verdict |
|---|---|
| **2e** (boot, stop, membership, storage, snap, WAL, v2stats, compactor, alarms, election/lock, config, features) | **FAIL**: 5 first-tier findings (F1-F5). Two more user patterns are open on recorded decisions: Q7 (embed's `Close` with gRPC's forced `Stop`) and Q8 (a join through etcd's peer handler). |
| **2f** (rafthttp) | **PASS WITH OPEN DECISIONS**: every user pattern of the transport closes except etcdmain/embed writing `ConnReadTimeout`/`ConnWriteTimeout` (open-questions 5.9). The docstring of `vars_init.spec` misdescribes that case (S4). |

Counts:
- **Specs read against users: 250 spec files.** 2e: 56 `etcdserver` files over `ApiBoot`, 23 membership, 8 snap, 8 v2stats, 14 v3compactor, 5 v3alarm, 6 v3election, 3 v3lock, 16 storage, 7 config, 1 features; `storage/wal` has none. 2f: 103 rafthttp files.
- **Snippets checked against users: 15.** `etcdserverboot`: `boot.go` 8, `lock.go` 1, `compactor.go` 1, plus `storage.go`/`snap.go`/`members.go`, which are Go tests of trusted models. `rafthttp`: `transport.go` 6, `snapshot.go` 2, `receive.go` 4 (read as a group).
- **User patterns: 2e 17, of which 10 close, 5 fail (F1-F5), 2 are open (Q7, Q8). 2f 9, of which 8 close and 1 is open (5.9).**
- **Callers' specs checked: 9**: v3rpc `ClusterServer.{MemberAdd,MemberList,MemberRemove,MemberUpdate,MemberPromote}`, `Server`, `maintenanceServer.{Status,MoveLeader,Downgrade}`; 3a `applierV3backend.{ClusterVersionSet,DowngradeInfoSet}`; 3c `NewLessor`; 2d `run`/`Process`. **Of these, 3 fit.**
- **Coverage against `specs-ref`:** in the area's directories, 5 old files have no successor (all internal helpers or field accessors). Among the server's own files, 2e's `EtcdServer.MemberList` and `checkMembershipOperationPermission` are gone, and several server getters with proved specs are too (S1).

## First-tier findings (2e)

**F1. `EtcdServer.MemberList` has no spec; the old proved one was dropped.** New; not recorded anywhere.
- The Go function: `server.go:1693-1704`. It does a linearizable read (`s.read.LinearizableReadNotify`), then `requireAuthInfo`, then `s.cluster.Members()`.
- Its caller: 2a's `ClusterServer.MemberList` (`v3rpc/member.go:93`). Its sketch (`v3rpc/ClusterServer__MemberList.lean:7`) cites "2e's spec: linearizable or the member's view, `clusterStep`'s `memberList`", which does not exist (`grep '^def EtcdServer.MemberList'`: nothing).
- Who depends on it, through the handler: 1c's `cluster.MemberList`, `Client.Sync`, and the snippet `clientv3client/cluster.go` (`ReqMemberAddThenList`).
- Old spec: `specs-ref/Spec/…/etcdserver/EtcdServer__MemberList.lean`, linked (`Proof/…/Link.lean`). PRINCIPLES, "A smaller API is not a narrower scope".
- The helper it shares with the membership writes, `checkMembershipOperationPermission`, also lost its spec. That is acceptable if `AddMember`'s trusted sketch covers it.
- Fix: add `EtcdServer.MemberList.spec`, shaped like `AddMember`'s: the caller's update for `srvStep pr tls (.memberList lin)`, which is `Model.lean:1271`'s `clusterStep` (`σ' = σ`, the members up to permutation when `lin`). The read is fired at the read index, as 2c's `Range` does. Post: `Membership.membersOwn sl ms` with `ms.Perm l`. Add a snippet in `etcdserverboot` (a linearizable member list after a member is added).

**F2. `urlsRight` is keyed by the request's URL strings, but `AddMember`/`UpdateMember` take it at the parsed URLs' strings.** No law bridges the two. New.
- `EtcdServer.AddMember.spec` (`EtcdServer__AddMember.lean:52-53`) needs `memb.RaftAttributes'.PeerURLs' ↦*□ urls ∗ urlsRight γ urls`. `UpdateMember` is the same.
- The only caller, `ClusterServer.MemberAdd` (`v3rpc/member.go`), builds `memb` from `types.NewURLs(r.PeerURLs)`. That gives `Types.urlsStrs us (urlsNorm ss)` (`types/NewURLs.lean`): the URLs re-rendered and sorted.
- The client holds W0's `urlsRight γ ss` at its own strings `ss` (1c's `reqRight`, `ApiClient.lean:380`).
- `urlsRight_excl` is the only law over `urlsRight` (`api/v3/State.lean:197`). Nothing turns `urlsRight γ ss` into `urlsRight γ (urlsNorm ss)` or a permutation of it. So the handler cannot establish `AddMember`'s pre for a request that lists two URLs out of order, or a URL that `url.Parse(…).String()` rewrites.
- The step the handler fires (`.memberAdd urls`) and the joiner's `memberJoin γ urls` / `diskCfgOk (.join urls)` must agree on which list is meant.
- Fix: state the right on the normalized set. Either a W0 law `urlsRight γ ss ⊢ urlsRight γ (urlsNorm ss)` (with `urlsNorm` idempotent and order-insensitive), or take `urlsRight γ ss` at any `ss` with `urlsNorm ss = urls` in `AddMember`/`UpdateMember`; key `memberJoin`/`urls_reserve` by `urlsNorm` too.
- Also, second-tier: the right is spent on every outcome, including a refusal that changes nothing (`ErrUnhealthy` from `StrictReconfigCheck`, `ErrPeerURLexist`, permission denied). A program that retries a refused `MemberAdd` with the same URLs, as `etcdctl member add` users do, cannot. On a fired refusal (`res = .err e`, `σ' = σ`) the post could return `urlsRight γ urls`. The Margin does not say this today.

**F3. The membership specs that 3a and 3c's specs cite do not exist.** Recorded as `integration-I5.md:126-127, 276, 329` (needs, not decisions). Open question 3.5(b) covers only the deployment premise `clusterVerOk`.
- 3a's `applierV3backend.ClusterVersionSet` (`apply/applierV3backend__ClusterVersionSet.lean:6`) cites `RaftCluster.Version`/`SetVersion` ("2e's, requested"). `DowngradeInfoSet` (`…__DowngradeInfoSet.lean:6`) cites `SetDowngradeInfo` ("requested"). The membership package has neither (`membership/` lists 23 specs, none of them these).
- 3c's `Lease.clusterOk` (`lease/Api.lean:348-352`) is still provisional and opaque. Its intended discharge, a 2e law `Membership.isCluster c γ cid lid ⊢ clusterOk (iface c)` with a spec of `RaftCluster.Version`, does not exist. So `NewServer`'s step 4 (`lease.NewLessor(…, srv.cluster, …)`, `server.go:344`) has no source for `NewLessor`'s `clusterOk` premise.
- 3a's `Apply.clusterVerOk` (`apply/Api.lean:531`, "provisional, 2e's") has no source either.
- Users: the apply thread on every `ClusterVersionSet`/`DowngradeInfoSet` entry (every cluster publishes its version: `monitorClusterVersions`); the lessor's checkpoints (`lessor.go:386`).
- Fix: add `RaftCluster.Version.spec` (returns `nil` or a readable version, under a read lock and a `threadTok`), `SetVersion.spec` and `SetDowngradeInfo.spec` (with `shouldApplyV3`, the backend written through the post-lock hook as `AddMember`'s is), and the law `isCluster_clusterOk`. Then settle `clusterVerOk` (3.5(b)).

**F4. v3lock/v3election's message predicates are still the provisional opaque ones, with no law to or from 3h's.** New as a finding; 3h's mapping table (`batch-3h.md:117-118`) says integration should replace them.
- `V3lock.lockReq`/`unlockReq`/`lockResp`/`unlockResp` (`v3lock/Api.lean:36-42`) and `V3election.campaignReq`…`leaderResp` (`v3election/Api.lean:49-65`) are opaque, with no introduction or elimination law.
- 3h's `V3lockpb.lockReq`… (`v3lock/v3lockpb/Api.lean:48-57`) and `V3electionpb.*` are the realized ones.
- `lockServer.Lock.spec` and the others take the 2e predicates. So:
  - no caller can establish `lockReq req name lease`: neither the gRPC handler `_Lock_Lock_Handler`, which decodes into `V3lockpb.lockReq`, nor `ReqLockOverInProc`, which builds `&LockRequest{Name: …}`;
  - no caller can read the key out of `lockResp resp k` (`resp.GetKey()`).
- Users: embed (`serve.go:149-150`, registering both services on every member's gRPC server) and the integration framework (`cluster.go:987-988`). Both also need `v3client.New`, which is untranslated and has no spec. That is recorded (`integration-I4.md:214-219`; open-questions 1.5 for the in-process client's watches), but the message predicates are not.
- Fix: make `V3lock.lockReq` etc. abbreviations of `V3lockpb.*` (same signatures, as 3h prepared), and the same for election. Keep `v3client.New` as the recorded gap and mark the two snippets as conditional on it.

**F5. Exported server methods that users call have no spec.** Some are cited by callers' sketches as 2e's.
- `maintenanceServer.Status` (`v3rpc/maintenance.go`) calls `CommittedIndex()`, `Backend()`, `Config()`, `ClusterVersion` (through the version adapter) and `Alarms()`. Its sketch says "2d/2e's getters". Of these, only `Alarms`, `AppliedIndex`, `Term`, `Leader` and `IsLearner` have specs. Old proved specs existed for `CommittedIndex`, `Backend`, `ClusterVersion`, `FeatureEnabled`, `AuthStore`.
- `maintenanceServer.MoveLeader` cites `ms.lt.MoveLeader` ("2d's transfer"). `EtcdServer.MoveLeader` has no spec; it is also called by `Stop` through `TryTransferLeadershipOnShutdown`.
- `maintenanceServer.Downgrade` cites `ms.d.Downgrade` ("2e"); `EtcdServer.Downgrade` has no spec.
- The integration framework's `Member.Pause/Resume` (`cluster.go:1166-1172`) call `PauseSending`/`ResumeSending`. Neither has a spec nor a snippet; `Transport.Pause/Resume` do have specs.
- Fix: getter specs over `srvMember`/`isServer` (any value; `Backend()` with 4a's handle at a share), `MoveLeader.spec` (an error or `nil`, no model change), `Downgrade.spec` (a refusal or a cluster-version step, as `etcdLocal` allows), `PauseSending`/`ResumeSending` (over `srvMember`, a `threadTok`). Add one snippet line for the pause pattern in `ReqPartition`.

## Recorded open decisions (they count, but are pending a user decision)

- **Q7 / open-questions 1.x, 3.6** (`batch-2e.md:250`): `Stop`/`HardStop` take the whole `srvGate s 1`.
  - `examples/etcd/restart` meets this: the stopped member serves no gRPC (`restart3.go:102`).
  - So does the integration framework's `Member.Close`, through `GracefulStop` then `HardStop` (`cluster.go:1188-1205`), provided 2a's `GracefulStop` gives the shares back. That branch is uncertain where it falls back to `Stop(); <-ch`: whether `GracefulStop` returns only after the handlers end depends on grpc's `waitForHandlers` default, which I did not check.
  - Embed's `Close` (`embed/etcd.go:428-470`) is not served: `stopServers` falls back to the non-draining `grpc.Stop` on a timeout, and always uses it for `secure && http` servers.
- **Q8 / open-questions 3.2**: a join through etcd's peer handler. Embed and the integration framework serve `etcdhttp.NewPeerHandler(lg, s)` (`cluster.go:992`), not just `RaftHandler`. Neither the handler (`/members`, `/leases`, `/version`) nor `LeaseHandler`/`HashKVHandler`/`DowngradeEnabledHandler` has a spec. `ReqJoin` closes only on its error branch.
- **Q3 / open-questions 3.3**: a failed `NewServer` loses `memberStart` (and with it `diskIdle`). The same holds after `Cleanup` before `Start` (embed's `InitialCheck` failure): `srvClosed ds` has no law back to `diskIdle`, so that directory cannot be restarted in the same run. Embed exits in both cases.
- **5.9** (2f): see S4.

## Second-tier

- **S1. Coverage gaps against `specs-ref`.**
  - Not in the area directories: `membership.RaftCluster.updateMembershipMetric`, `v3alarm.AlarmStore.restore` (both proved, internal helpers), `snap.Message__fields`, `rafthttp.streamType__String_ptr` (accessors), `clusterImageOk_restModel` (a law).
  - The server's own (owner 2e or 2c/2d; uncertain from the batch table): `MemberList` (F1), `checkMembershipOperationPermission`, `ClusterVersion`, `CommittedIndex`, `Backend`, `AuthStore`, `FeatureEnabled`, `ensureLeadership`, `isLeader`, `LeaderChangedNotify`, `FirstCommitInTermNotify`, `EtcdServer.NewUberApplier`, `getTxPostLockInsideApplyHook`.
  - `NewServer`'s sketch inlines the last two. An internal helper may simply be inlined (PRINCIPLES, "Scope"), but the exported getters are linked results.
- **S2. Uncovered snippet pattern: "wait for ready, or for the stop."** `embed/serve.go:134-136` (`StoppingNotify`/`ReadyNotify`), `etcdmain/etcd.go:187-188` (`ReadyNotify`/`StopNotify`), and the examples' tests (`<-s.ReadyNotify()`). The specs exist (`readyCh`, `doneCh`, `stoppingCh`), but no snippet relies on a receive. Add one to `boot.go`.
- **S3. embed's `CorruptionChecker().InitialCheck()`** between `NewServer` and `Start` (`embed/etcd.go:271-280`, only when the member is initialized and `InitialCorruptCheck` is enabled) has no spec. The `NewServer` sketch notes this.
- **S4 (2f). `Rafthttp.vars_init.spec`'s docstring** (`rafthttp/Api.lean:535-547`) says no one writes `ConnReadTimeout`/`ConnWriteTimeout` after initialization, "which etcdmain meets by clamping". It does not:
  - embed's flag set binds both variables (`embed/config.go:631-632`, `fs.DurationVar(&rafthttp.ConnReadTimeout, …)`);
  - etcdmain then assigns them (`etcdmain/config.go:180-186`).
  
  The law gives `↦□` from `isPkgInit`, so a program that writes them, even before any server starts, is outside the spec. It is recorded as a scope premise (5.9), but the docstring should say that etcdmain is excluded. Better: have `Transport.Start` (or `vars_init`) take the variables' points-to with the `≥ 5s` fact as a premise the program establishes after its writes. etcdmain's clamp then meets it.
- **S5. K2 versus the specs.** `top.md` K2 describes the join right as `etcdLb γ σ` with the member in `σ.members`. The specs use `memberJoin` from `urls_reserve`, a single-use URL right (A15, decided). `top.md` should be updated to match.

## Patterns and call sites (one per pattern)

2e:
1. A new one-member cluster: `etcdstart.StartServer` (`common.go:105-115`). `ReqStartOne`; closes. `cluster_alloc` → `disk_new` → `memberStart_disk` → `NewServer` → `Start`.
2. A three-member cluster, raft handler served before `Start`: `etcdstart.NewMember`, `cluster3.StartMember` (`cluster3.go:104-128`). `ReqStartThree`; closes (`RaftHandler` over `srvMember`; `srvNet_agree` with `cluster_alloc`'s protocol).
3. A restart on the same directory after `HardStop`: `restart3.restartCheck` (`restart3.go:158-176`), integration `Member.Restart`. `ReqRestart`; closes (`memberDisk` = `diskIdle (.member id)`, kind `.member` admits `NewCluster = true`).
4. A crash restart: `ReqCrashRecover`; closes under `crashScope`.
5. A join: integration `Cluster.AddMember` + `Launch`. Open (Q8); also F2.
6. A stop with gRPC drained: restart3, integration `Close`. Closes (the integration framework's fallback is uncertain; see Q7).
7. A stop with gRPC forced: embed's `Close`. Open (Q7).
8. A stop after a server error / waiting on `StopNotify`: etcdmain (`etcd.go:187-190`). `ReqStopAfterError`; closes.
9. `Cleanup` before `Start`: embed (`etcd.go:277`). `ReqCleanupBeforeStart`; closes.
10. Partitions: `cluster3.PeerStep` (`cluster3.go:140-152`). `ReqPartition`; closes. Pause/Resume: F5.
11. Membership writes through gRPC: v3rpc `ClusterServer.Member{Add,Update}`. F2. `Remove`/`Promote` close.
12. The member list through gRPC: F1.
13. Status, MoveLeader, Downgrade: F5.
14. Lock/Election on the member's gRPC server: F4.
15. The compactor's lifecycle (`NewServer`/`start`/`run`/`Cleanup`): `ReqCompactorLifecycle`; closes (the periodic retention premise is needed: `getRetentions` divides by `period/10`, `periodic.go:178`).
16. The raft loop's WAL/snapshot writes, `bootstrap`'s reads: trusted models with Go tests (`storage.go`, `snap.go`); consistent with `bootstrap.spec`.
17. The apply thread and lessor through the membership view: F3. `AddMember`/`RemoveMember`/`Members`/`IsIDRemoved` close (`members.go`).

2f, all closing except where marked:
1. The transport literal, `Start`, `AddRemote`, `AddPeer` (`server.go:412-438`; `ReqStartTransport`).
2. `Send` of a `Ready`'s messages (`raft.go:250,329`; `ReqSendReady`).
3. Membership changes (`server.go:1157-1166,2075-2101`; `ReqMembership`).
4. Health heuristics (`util.go:52-100`, `server.go:504,1655`; `ReqConnected`).
5. Stop and the test hooks (`raft.go:440-456`, `server.go:2196-2210`; `ReqStop`).
6. Errors on `ErrorC`: `ReqErrorC`.
7. The handler served on a mux, at the root, and re-served after a restart (embed's peer mux, `etcdstart.NewMember`, `restart3`; `receive.go`).
8. Merged snapshot send and receive (`server.go:1886`; `snapshot.go`).
9. The timeout globals written by etcdmain/embed flags: open (5.9, S4).

## Bugs in the Go code

None found that are not already filed. The divide-by-zero for a periodic retention below 10ns (`periodic.go:178`) is excluded by `V3compactor.bootCfg_on`, and is already filed (`issues/etcd-compactor-periodic-tiny-retention.md`).
