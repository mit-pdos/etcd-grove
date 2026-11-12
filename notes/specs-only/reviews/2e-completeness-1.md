# Batch 2e (bootstrap, storage, stop, WAL, snap, membership, v2stats, compactor, alarm, election/lock, config, features, leasehttp): completeness review, round 1

Reviewer: completeness. HEAD `e6d943c00b`; the 2e files are in `b5cecfd608`, `22051298eb` and
`e6d943c00b`. Read: `ApiBoot.lean`, the lifecycle specs (`NewServer`, `EtcdServer.{Start,Stop,HardStop,
Cleanup,MemberID,RaftHandler,CutPeer,MendPeer,StoppingNotify}`), the vocabularies of `config`,
`features`, `storage`, `storage/wal`, `api/{membership,snap,v2stats,v3compactor,v3alarm,v3election,
v3lock}`, `lease/leasehttp`, and their specs where a snippet or a user reaches them. Also the
snippets `examples/specreq/etcdserverboot/*.go`, and the users: `embed/etcd.go` (`StartEtcd`,
`Close`, `servePeers`), `embed/serve.go`, the integration framework
(`tests/v3@…a4d2bb1720b9/framework/integration/cluster.go`: `Launch`, `Close`, `Stop`, `Restart`,
`Terminate`, `addMember`, `RemoveMember`), `examples/lib/{etcdstart,cluster3}`, every example main that
starts a cluster (`examples/etcd/{putget,putget3,restart,partition,compacted,compactwatch,cache,
auth,lease,leasegrant,leaseexpiry,leasecatchup,watch,txnlin}`, `examples/k8s/{etcd3,compactor}`),
`top.md` K1-K8, `req/go_etcd_io_etcd_server_v3_etcdserver.md` (from W0, 2a, 2f, 2e), and
`req/go_etcd_io_etcd_api_v3.md` "from 2e". `batch-2e.md` was read only after the findings below were
formed. I did not build anything. `etc/lean-check.py` was run on `api/v3lock/*` and
`api/v3election/*` only, for F9.

## The patterns

| # | pattern | real call sites | what the caller relies on | snippet |
|---|---|---|---|---|
| P1 | single-member start | `etcdstart.StartServer`/`StartCompactingServer`/`StartPeriodicServer` (`common.go:104-144`), `auth/authkv.go:113`, `embed/etcd.go:262,282` | NewServer's pre can be established from the config it builds. The post gives a started server that `v3rpc.Server` turns into `servesAt` (K3) | `ReqStartOne` (it does not serve) |
| P2 | multi-member static bootstrap | `etcdstart.NewMember`/`StartMember` (`common.go:160-185`), `cluster3.StartMember`/`StartCluster` (`cluster3.go:102,194`), `putget3.go:47-54`, `restart3.go:123-133` | one `memberBoot` per member. The raft handler is served before `Start`. The members have distinct ids (`PeerStep` cuts `sb.MemberID()`) | `ReqStartThree` |
| P3 | a joining member (MemberAdd, then a start with `NewCluster=false`) | integration `addMember` (`cluster.go:295-325`), etcd's documented runtime reconfiguration | the add is answered. The joiner starts and runs as an id other than the existing members' | `ReqJoin` |
| P4 | restart after a graceful stop | `restart3.go:96-104,170` (HardStop, peer listener closed, BuildServer again on the same dir), integration `Stop`+`Restart` (`cluster.go:1223,1257`), `embed.Close` → `Stop` | `memberDisk` gives a start on the same directory. The restarted member serves the same γ: a read through it sees writes made while it was down | `ReqRestart` (one member, no snapshot) |
| P5 | restart after a crash | W0 `req/…etcdserver.md` item 5 ("a crash … and a restart from disk loses no answered step") | durable state while running | none (Q2) |
| P6 | snapshot-triggered WAL release and purge before a restart | `restart3` (`SnapCount = 1`, `SnapCatchUp = 1`: "the restarted member finds a snapshot in its WAL and is caught up by a snapshot"), embed's defaults (`MaxWalFiles = 5`, `MaxSnapFiles = 5`) | restart from a released or purged WAL | none |
| P7 | member removal | integration `RemoveMember` (`cluster.go:346-374`: `<-m.Server.StopNotify()` then `Terminate`) | the removed member stops itself. `StopNotify` fires. A later stop or terminate does not panic | `ReqStopAfterError`, partly (it calls the unspecified `StopNotify`) |
| P8 | auto-compactor modes | `StartPeriodicServer` (`compacted`, `cache`: 10ms), `StartCompactingServer` (`compactwatch`: revision, retention 1; `k8s/compactor`: 0) | the compactor's mode is accepted. **compactwatch's C3 check** (`compactkv.go:140-155`): a compaction stays at least the retention behind a revision reached | `ReqCompactorLifecycle` (fakes, not a server) |
| P9 | alarm raise and disarm | apply's `Alarm` (`apply/backend.go:109-133`), the uber applier's `Get` (`uber_applier.go:71-72`), `restoreAlarms`, quota alarms (2a item 5) | `Activate`/`Deactivate`/`Get` on the client's raw `AlarmType` | none |
| P10 | v3lock/v3election RPCs | `embed/serve.go:149-150,185-186`, integration `Launch` (`cluster.go:986-988`): over `v3client.New(s)` | a lock or election server over the in-process client, with the per-call principal of a forwarded token | none |
| P11 | server stop with requests in flight | `embed.Close` (`etcd.go:438-470`: `stopServers` falls back to `grpc.Stop`, then `Server.Stop`), integration `Close` (`cluster.go:1194-1206`: GracefulStop for 2s, then `Stop`, then `HardStop`) | a stop while handlers still run. The member's directory is then restartable | none |
| P12 | a built server never started | `embed/etcd.go:270-280` (InitialCheck fails → `Cleanup`) | `Cleanup` without `Start` | `ReqCleanupBeforeStart` |
| P13 | partitions | `cluster3.PeerStep` (`cluster3.go:140-152`) | `CutPeer`/`MendPeer` at any time | `ReqPartition` |
| P14 | the stopped-member checks | `restart3.go:99` (`AppliedIndex`), `:149` (`Leader() == MemberID()`) | getters do not panic | covered by the getters' specs; no snippet |

## First tier

### F1. NewServer's precondition cannot be established by any caller: seven provisional slots and `cfgHeap` have no introduction law

**Principle:** Complete (each caller can establish the pre); every premise has a source the caller sees.

**Evidence:**
- `ApiBoot.lean`, lines 245-283, declares four opaque `Prop` slots (`raftNodeBootCfg`, `v3rpcBootCfg`, `mvccBootCfg`, `rafthttpBootCfg`) and three opaque `IProp` slots (`backendBootRes`, `leaseBootRes`, `authBootRes`). None has a definition or an intro law.
- `Config.cfgHeap` (`config/Api.lean:114-122`) has only persistence, timelessness and agreement. Nothing produces it from the points-to facts of the URL slices and the map that the caller builds.
- `NewServer.spec` takes all eight. So does `bootstrap.spec:72`.
- Compare the one slot done right: `V3compactor.bootCfg` has `bootCfg_off`/`bootCfg_on`.

**Affected:** every start in the snippets (`ReqStartOne`, `ReqStartThree`, `ReqRestart`, `ReqJoin`) and every real call site of P1-P4 (`etcdstart.newServerMode`, `authkv.startServer`). Under the stated laws none of them is provable. The snippets' comments ("TickMs > 0 and ElectionTicks > 1: raftNodeBootCfg", `boot.go:21-25`) claim intros that do not exist.

**Fix:** give each slot, now, the intro law its eventual owner must keep, stated over the configuration fields the starters set:
- `raftNodeBootCfg_intro`: `0 < TickMs`, `1 < ElectionTicks`, ….
- `v3rpcBootCfg_intro`: `MaxTxnOps ≤ 4999`, `MaxRequestBytes ≤ …`.
- `mvccBootCfg_intro`: `0 ≤ CompactionBatchLimit`.
- `rafthttpBootCfg_intro`.
- `backendBootRes_intro`: from a named program-start resource for `ETCD_VERIFY` unset, which W0's adequacy statement must list.
- `leaseBootRes_intro`: `ecfg.leaseExpiry = true`, or the named deployment premise.
- `authBootRes_intro`: `AuthToken ∈ {"", "simple"}`, ….

Alternatively, make the provisional ones transparent definitions of those conditions until the owner seals them.

Add `cfgHeap_intro` from `↦□` of the `types.URLs` slices and the `URLsMap`, with `c` their `url.URL.String()` forms. It needs a source for the strings: a `net/url` spec, or a pure model of `String`. Name the program-level source of `dataDirFresh` (the adequacy theorem's per-directory token) in W0's adequacy statement too. Today it lives only in a header comment.

### F2. Stopping a server with requests in flight (P11) is not served, and 2e's hand-off to 2c asks for something false

**Principle:** Sound and complete; read the definitions of the resources a spec takes.

**Evidence:**
- `isServer` is persistent and "stays valid after the stop … every request-path spec over it must hold on a stopped server, answering an indefinite error" (`req/…etcdserver.md`, "from 2e", To 2c item 1).
- `HardStop.spec` and `Stop.spec` take only `srvRunning` and give `memberDisk`, through `Cleanup`, which closes the backend (`server.go:943-963`).
- Nothing in the fork stops a serializable `Range` (`v3_server.go:136-151`) from reading the closed backend. That is the already recorded `issues/etcd-read-after-backend-close-panic.md`, reached on removal (P7) and after `embed.Close`'s fallback to `grpc.Stop` (P11). The issue's "Proof" section says the mvcc API makes a proved stop path wait for every reader token, "exactly what etcd's `Cleanup` does not wait for".
- So, as stated, `HardStop.spec` (whose `Cleanup` needs `beOpen` whole, rebuilt from the store's readers) is not provable while `isServer` lets readers run. The 2c obligation (an indefinite error after the stop) is false in Go.

**Affected:** 2c (asked to prove the false obligation); embed's and the integration framework's `Close`; `ReqStopAfterError` (a removed or failed member with `isServer` still usable).

**Fix:** pick one and state it:
- (a) A fork fix (a gate: reads take it shared, `Cleanup` takes it exclusively after the server is marked stopped, later reads fail with `ErrStopped`). Then the 2c obligation is true; keep the spec and record the fork commit.
- (b) A scope premise that `HardStop`/`Stop` take: the request-path reader tokens back (`isServer` fractional, returned by the program once it has stopped and drained its gRPC server). Then `restart3`'s pattern (its stopped member serves no gRPC) still fits, embed's forced-stop path does not, and the issue gets `blocks-proof: yes` for that path.

Either way, withdraw item 1 of the 2c hand-off as written. Add a snippet: a `Range` from another goroutine racing `HardStop`, the program's assumption stated.

### F3. Snippets that call functions with no spec (unprovable as written)

**Principle:** Snippets provable; a snippet that only calls the API checks that its preconditions can be met.

**Evidence:**
- `ReqStopAfterError` calls `s.StopNotify()`. No spec exists; `batch-2e.md` "Left out" lists `ReadyNotify`, `StopNotify`. Its real users: integration `RemoveMember` (`cluster.go:362`), `embed/serve.go:136` (`ReadyNotify`), `etcdmain`.
- `ReqJoin` calls `membership.NewMember` and `s1.AddMember`; `ReqMembers` calls `NewClusterFromURLsMap`, `NewMember`, `schema.NewMembershipBackend`, `MustCreateBackendBuckets`. None has a spec. `api/membership/` has no `NewMember`, `NewMemberAsLearner` or `NewClusterFromURLsMap`; no `EtcdServer__AddMember.lean` exists anywhere.
- `ReqSaveOrder` (`storage.go:157-195`) calls `wal.Create`, `wal.Open`, `ReadAll` and `(*WAL).Close`, which the batch deliberately leaves without specs (`wal/Api.lean`: "no translated code calls a `wal.*` function directly"). Its panic at line 192 can only be discharged through those missing specs.

**Fix:** add `StopNotify`/`ReadyNotify` (getters over `srvMember`: a channel, receivable from any goroutine, like `stoppingCh`). Add the membership constructors (`NewMember`, `NewMemberAsLearner`, `NewClusterFromURLsMap`: 2a's MemberAdd sketch needs the first two, F4). Restate `ReqSaveOrder` through the restart (`HardStop` → `memberStart_restart` → `NewServer`) or through `bootstrap.spec`'s contract, or add trusted specs of `wal.Create`/`Open`/`ReadAll`/`Close` with the `walRecs` model they already share. For `ReqMembers`, either cite 4b's schema specs (request them in `req/…storage_schema.md`) or start from `beView`.

### F4. 2a's request item 7 is unanswered: the server's membership methods and getters have no spec, and no batch owns them

**Principle:** Complete for every caller; one spec per function in scope.

**Evidence:**
- `req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2a", item 7, asks 2e for `AddMember`, `RemoveMember`, `UpdateMember`, `PromoteMember` and `MemberList` (in `SrvCallTriple`'s shape), and the getters `Cluster().ID()`, `KV().Rev()`, `Backend()`, `IsLearner`, `IsMemberExist`, `Alarms`.
- 2a's `ClusterServer__MemberAdd.lean:7` cites "`NewMember`/`NewMemberAsLearner` (2e) and `cs.server.AddMember(ctx, m)` (2e's spec)".
- These are in `server.go` (`:1406`, `:1465`, `:1483`, `:1676`, `:1779` `configure`; `:627`, `:2415`, `:2455`, `:2460`, `:2465`). The batch table gives `server.go`'s start/stop to 2e and its apply/raft parts to 2d, so nobody owns them. `batch-2e.md`'s "Requirements on 2e from others, checked" does not mention 2a.

**Affected:** P3's `MemberAdd` (the join pattern itself: `ReqJoin`'s first call); W0's `clusterStep`; 2a's `ClusterServer.*` and maintenance `Alarm`/`Status` sketches.

**Fix:** write `EtcdServer.{AddMember,RemoveMember,PromoteMember,UpdateMember}` (over `isServer`, the caller's update over `Step`'s `memberAdd …`, the `configure` path with `ValidateConfigurationChange`'s `ccResult`, the `ErrIDRemoved`/`ErrIDExists`/`ErrPeerURLexists` refusals that `memberJoin`'s realization leans on) and the getters. Or hand them explicitly to 2c in `batches.md`, with a note in 2a's req file saying who.

### F5. NewServer's post does not give what P1-P3 check about the member id

**Principle:** The postcondition says what the caller inspects; complete.

**Evidence:**
- `NewServer.spec`'s post is `∃ id, srvMember s γ id ∗ srvBuilt s γ id cfg`, and `memberStart` forgets which token it came from. No law makes `srvBuilt`/`srvRunning` exclusive per `(γ, id)`, gives `id ≠ 0`, or gives `id < 2 ^ 64`. `MemberID.spec` returns `#(W64 id)`.
- So `ReqStartOne`'s `MemberID() == 0` panic (`boot.go:77`), `ReqStartThree`'s duplicate-id panic (`:109`) and `ReqJoin`'s `s2.MemberID() == s1.MemberID()` panic (`:178`) are not provable.
- Real reliance: `cluster3.PeerStep` cuts `sb.MemberID()` and must not cut itself; `restart3.go:149` compares `Leader()` with `MemberID()`.
- The code knows the facts: `bootstrap` fails on an id `0` or a duplicate (`NewClusterFromURLsMap`; the header says so), and a running member holds `raftState γ.raft id` exclusively (`memberDisk_excl` already rests on it).

**Fix:** add `⌜id ≠ 0 ∧ id < 2 ^ 64⌝` to the post, and laws `srvBuilt_excl_id`/`srvRunning_excl_id` (two of the same `γ` and `id` give `False`), and `srvBuilt_running_excl`. A restart would also like `id` to be the `memberDisk`'s: index `memberStart` by an optional id, or add `memberStart_restart`'s `id` to the post through a variant law (second tier, F11).

### F6. compactwatch's retention check (C3) is not served: the environment's compaction step forgets the compactor's retention

**Principle:** Complete for every caller: a real example's panic guard.

**Evidence:**
- `examples/etcd/compactwatch/compactkv.go:135-155` panics if `lresp.Header.Revision < crev + retention`, "C3: every compaction is at least the retention behind a revision the cluster has reached".
- W0's `EnvStep.compact` (`Model.lean:1207-1208`) allows any `r ≤ σ.kv.rev` when `autoCompact`. 2e's slot `bootCfg mode ret ac` couples only a `Bool`, and `compactable c` says "any response", so no statement carries the revision mode's `rev − retention`.
- The revision compactor computes `rg.Rev() - retention` (`revision.go`). The old proof had the guarantee (the example's header).

**Affected:** `examples/etcd/compactwatch` (adequacy); `top.md` §2's etcd3-store story, which tolerates every compaction "but the compaction below what it reads".

**Fix:** together with W0 (a `req/…api_v3.md` section): `EnvCfg` carries the auto-compactor's lag (`autoCompact : Option Nat`, or `compactLag : Nat`, 0 for periodic) and `EnvStep.compact` requires `r + lag ≤ σ.kv.rev`. 2e's `bootCfg` ties `ret` to the lag in revision mode (`bootCfg_on` at `lag ≤ ret`), and the `Compactable` the server builds commits only `EnvStep.compact` at the compactor's revision. The compactor's spec must then say which revision it compacts at, through a `compactable` that takes the revision's bound, not "any request".

### F7. `compactable` and `revGetter` have no introduction law, so neither the server nor `ReqCompactorLifecycle` can call `V3compactor.New`

**Principle:** Every premise has a source; a contract an implementation must meet is a law the implementation can prove.

**Evidence:**
- `v3compactor/Api.lean:92-104` gives only persistence. `New.spec:40` takes both.
- `NewServer`'s sketch (step 5) builds `compactable` of the server "from 2c's `EtcdServer.Compact.spec`", but no law turns a `Compact` triple into `compactable`.
- The snippet's `fakeRev{}` and `fakeCompactable{}` (`compactor.go:13-21`) cannot get them either.

**Fix:** `compactable_intro`: from `□ ∀ ctx r, {ctxOk ctx ∗ …} c.Compact ctx r {…}` (the method triple at the interface receiver, the bundle convention). Likewise `revGetter_intro`. 3e then proves `revGetter_intro` for the store, and the server proves `compactable_intro` for itself.

### F8. Restart after a crash (P5) is still unresolved against W0's requirement

**Principle:** Complete against the contract the batch serves.

**Evidence:**
- W0's `req/…etcdserver.md` item 5 requires that "a crash of any minority, or of the whole cluster and a restart from disk, loses no answered step". `memberDisk` comes only from `HardStop`/`Stop`.
- 2e recorded this as open question Q2 (`batch-2e.md`), and told W0 in `req/…api_v3.md` "from 2e" item 3.
- `top.md` K6 still promises an answered step "durable on a quorum (no crash transition in the model)".

**Fix:** not a spec change in this round. Have the user decide Q2, and make W0's item 5 or K6 say "graceful stop only" until then, so the contract does not claim what no spec gives. Until it is decided, every durability claim that rests on K6 holds only for graceful stops.

### F9. v3lock/v3election: the real caller cannot meet the principal premise, and the specs do not type-check

**Principle:** A premise inherited from a callee is checked against the value the caller actually passes. Specs that do not type-check are not specs.

**Evidence:**
- `lockServer__Lock.lean:34` (and `Unlock`, every `electionServer__*`) takes `ClientV3.isClient c γ who ∗ ClientV3.ctxPrin ctx who`. `ctxPrin` is `ctxPrin (dflt) (ctx) (p)` (`client/v3/Api.lean:542`). `lean-check` reports `Application type mismatch … ctxPrin ctx` in `lockServer.Lock`, `electionServer.{Leader,Proclaim,Resign,session}`, and `Unknown identifier keysEff` (1d's in-progress `concurrency/Api.lean`). This is 2e's own arity error, not only the 1d blocker `batch-2e.md` reports.
- The only real caller passes `v3client.New(s)` (`embed/serve.go:149-150`, integration `cluster.go:986-988`): a client whose default principal is `none` (`ClientV3.clientBare_assemble`) while each call's principal is the forwarded token's user. So the statement must be `isClient c γ none ∗ ctxPrin none ctx p` with the steps at `p`. Tying both to one `who` forces `p = none`, which an auth-on deployment never has.
- `v3client` is not translated and nothing produces `isClient` for it.
- There is no snippet (P10).

**Fix:**
- Restate it as `isClient c γ dflt ∗ ctxPrin dflt ctx p`, with the effects under `p`.
- Request `v3client.New`'s spec, or the producing law from `isServer`, in W0's or 1c's req file.
- Add `etcdserverboot/lock.go` (`ReqLockOverInProc`: lock, then unlock, with a token in the context).
- Rebuild when 1d settles.

## Second tier

- **F10. Uncovered patterns without a snippet.**
  - P6: snapshot release and WAL purge before a restart. Add a `ReqRestart` variant with `SnapshotCount = 1`, `SnapshotCatchUpEntries = 1`, `MaxWALFiles = 1`, many puts, stop, restart, read. It exercises `memberDisk`'s `R.readable` and `walPurgeRight` handoff, which `restart3` relies on.
  - P8 on a real server: `StartPeriodicServer` with 10ms. This checks `bootCfg_on` at `ac = true` against a real config.
  - P9: alarms. `Activate` NOSPACE, `Get`, `Deactivate`.
  - Graceful `Stop()` (embed's `Close`): no snippet uses it.
  - Start, then serve (K3): `v3rpc.Server` + serve + `clientv3.New` + `Put`/`Get`. `ApiBoot`'s header says the snippets are "started and served", but none serves.
  - `ApiBoot.lean:150-152` lists snippet files `stop.go` and `config.go` that do not exist. Fix the list or write them.
- **F11. A restart forgets the member's id.** `memberStart_restart` maps `memberDisk γ id ds` to an id-less `memberStart`, and the post's `∃ id` does not say it is the same member. A program that keys ghost state by member (a per-member `leaseViewLb`-style fact, a `PeerStep` table) loses it across a restart. Index `memberStart` by `Option Nat` (or give the post `id = id₀` when started by `memberStart_restart`).
- **F12. `memberUrls_take` forbids rejoining a removed member's peer URLs** (`∀ u ∈ U, ¬ u.Perm urls`). etcd's documented "replace a failed member" procedure (remove, then add a member, often at the same address) and any program that restarts a removed member's host fall outside it. It is a scope restriction (`batch-2e.md` Q1). Record it as such in `issues/`/`nonissues/` or the decisions, or key the reuse on a proof that the old id's removal is committed (`etcdLb` with the id in `σ.removed`).
- **F13. `AlarmStore.Deactivate`/`Activate` take `kindOf at' = some k`.** The applier passes the client's raw `AlarmType` (`apply/backend.go:116-131`: ACTIVATE of NONE is filtered, DEACTIVATE is not). `Deactivate(id, NONE)` or an unknown type returns `nil` with the view unchanged (`alarms.go:76-90`), so the premise is not needed. Relax it to a case on `kindOf at'`: `none` returns `p = null`, view unchanged. W0's model has no client ACTIVATE (`Model.lean:463-466`); an unknown-type ACTIVATE from a client reaches `Activate` (raw type): 3a or W0 must say what the model does with it. Write it in the alarm section of `req/…api_v3.md`.
- **F14. The peer and client addresses on restart.** `restart3` and the integration framework re-listen on the same peer and client addresses after a stop. 2a's `Serve` binds an address "once" (`addrAt` persistent), and 2f's `protoOwn a P` is held by the first `http.Serve`. `HardStop`'s post gives back neither. 2e asked 2f (its req section), but nothing records the client-address side for 2a. Check that the restart's re-serve has a source on both sides.
- **F15. `leasehttp`'s server side** (`NewHandler`, served by embed's `etcdhttp.NewPeerHandler`, `embed/etcd.go:594`, and by the integration framework) has no spec and no owner. A follower's `LeaseRenew` forwards to it. The examples serve only `RaftHandler`, so a keep-alive through a follower gets a 404 there (`RenewHTTP`'s error disjunct covers it). Fine for the examples; record that embed's pattern is out of scope.
- **F16. `embed`'s `InitialCheck` between `NewServer` and `Start`** (`CorruptionChecker()`, `InitialCheck`) has no spec. It is used only by untranslated code, so mark it out of scope in `NewServer`'s Users.
- **F17. The membership header's claim** "a program learns a concrete value only by running Go (`boot.go` prints them)" (`membership/Api.lean:16-17`) is false: `boot.go` prints nothing. Drop the claim or add the print.

## What is good

- One `NewServer` triple for every mode, with the start right `memberStart` introduced three ways. This is the right shape for K2. The joiner keyed by its URLs rather than its id is a real soundness point (the `bootstrap` id lookup), argued in the header.
- `memberDisk`'s realization ties every binder to the files (the R2d'a lesson) and does not bound `ci` by the WAL commit (R1's round-1 point).
- `HardStop`/`Stop` give back exactly what `memberStart_restart` takes. `restart3`'s pattern (stop a follower, write through others, restart, read) is served once F1 and F2 are fixed. The old `srvBootApplied` wait is no longer needed because R1 dropped the bootstrap-length premise.
- `V3compactor.bootCfg` is a model slot (intro and narrow elimination laws). The others should copy it (F1).
- The membership and alarm views are TaDa (`clusterSt`, `alarmSt`), and `IsLocalMemberLearner`'s spec matches the fork's fix (`cluster.go:786-795`).
- `members.go`'s and `snap.go`'s guards test the facts their users rely on: a removed id stays removed (rafthttp's 403), a released snapshot db is gone (apply's `DBFilePath`).

## Ranking by need of revision

1. **`ApiBoot.lean` + `NewServer`/`HardStop`/`Stop`** (F1, F2, F4, F5, F3's `StopNotify`, F11): the hub. No start or stop is provable as stated.
2. **`api/v3compactor`** (F6, F7).
3. **`api/v3lock`, `api/v3election`** (F9).
4. **`api/membership`** (F3: the constructors; F4's `NewMember`; F12).
5. **`storage`/`storage/wal`** (F3: `ReqSaveOrder`; F10's purge snippet).
6. **`api/v3alarm`** (F13; no snippet).
7. **`config`** (F1: `cfgHeap_intro`), **`features`**, **`api/snap`**, **`api/v2stats`**, **`lease/leasehttp`**: minor.

No new Go bug found. The stop-with-reads crash of F2 is already `issues/etcd-read-after-backend-close-panic.md`.

## Verdict

Not done. Nine first-tier findings.
- F1: no start can establish NewServer's pre.
- F2: the stop path is not provable on the fork's code while `isServer` serves reads, and the 2c obligation 2e wrote is false.
- F3: snippets call functions with no specs.
- F4: 2a's membership and getter needs are unowned.
- F5: the posts do not give the member-id facts the snippets check.
- F6: compactwatch's retention check.
- F7: the compactor's contracts have no intros.
- F8: crash restart unresolved against W0.
- F9: v3lock/v3election principal premise and type errors.

F8 is a user decision (Q2). The others are repairs to 2e's statements and snippets, plus one hand-off to W0 for F6.
