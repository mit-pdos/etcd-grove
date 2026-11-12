# A7 (batches 2c, 2d): server request path and apply thread: completeness

Reviewer: independent verification round, kind **completeness** (2026-11-09). Read-only apart from
this file. I wrote the findings first. Only afterwards did I read `open-questions.md`,
`batch-2{c,d,e}.md` and `integration-*.md`, to mark what they already record.

Go: `S = .lake/src` (pinned `a4d2bb17`). Specs: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/` (2c's
request path, 2d's apply thread and raft node), `.../{read,cindex,errors}/`,
`SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/{wait,idutil,notify,schedule}/`.

## Verdicts

| batch | verdict |
|---|---|
| **2c** (request path, read loop, wait/idutil/notify) | **FAIL** (F1, F2, F3, F4, F5) |
| **2d** (apply thread, raft node, cindex, schedule) | **FAIL** (F1, F3, F6) |

Counts:
- **Use patterns:** 17 checked against the specs; 8 close.
- **Callers' specs (other areas):** 14 cross-checked; 7 close.
- **Snippets:** 49 snippet functions checked for coverage of the patterns. Three patterns have no
  faithful snippet (see "Snippets").
- **Coverage:** 25 functions had an old spec and have none here. 19 of them are `EtcdServer`
  methods, 11 of which have users.

## Users and patterns

| # | pattern (example call site) | specs used | closes? |
|---|---|---|---|
| U1 | gRPC KV handlers over `RaftKV` (`api/v3rpc/key.go:53,95,104,130`) | `Range/Put/DeleteRange/Txn.spec` (`SrvCallTriple`) through 2a's composition (`reqPrin_of_md`, `rpcCtx_reqCtxOk`, `txnCheck_checked`, `endsDecoded`) | yes |
| U2 | gRPC lease handlers (`lease.go:45,54,63,79`), keep-alive loop (`lease.go:136`) | `LeaseGrant/Revoke/TimeToLive/Leases/Renew.spec` | yes, except the keep-alive loop's gate (open question 3.6(a), recorded) |
| U3 | gRPC auth/maintenance/alarm handlers (`auth.go`, `maintenance.go`, `quota.go`) | `User*/Role*/Auth*/Alarm/Alarms.spec` | yes for the `SrvCallTriple` calls; **no** for `AuthStore()`, `Backend()`, `CommittedIndex()`, `ClusterVersion()` (F3) |
| U4 | `ClusterServer.MemberList` (`member.go:93`) | "2e's spec" of `EtcdServer.MemberList`: does not exist | **no** (F3) |
| U5 | lease expiry: `revokeExpiredLeases` → `LeaseRevoke(WithRoot(s.ctx))` (`server.go:855-895`) | `revokeExpiredLeases.spec`, `GoAttach.spec`, `LeaseRevoke.spec`, 3d `WithRoot.spec` | **no** (F1, F5, F3: `ensureLeadership`) |
| U6 | auto-compactor: `c.Compact(ctx, {Revision})` (`v3compactor/periodic.go:142`, `revision.go:92`) | `compactable_intro` ← `Compact.spec` | **no** (F1, F2) |
| U7 | lease checkpointer closure (`server.go:395-403`) | 3c `ckptOk` ← `ensureLeadership`, `raftRequest.spec` | **no** (F1, F3) |
| U8 | `NOSPACE` alarm from the apply (`server.go:2019-2026`) | `applyEntryNormal.spec` → `GoAttach`, `raftRequest.spec` | **no** (F1) |
| U9 | `publishV3`, `monitorClusterVersions`, `monitorStorageVersion`, `monitor*Hash` (`server.go:533-541`) | `raftRequest.spec`, `Notifier.Receive.spec`, `LinearizableReadNotify` | **no** (F1: no `threadTok`; F3: `EtcdServer.LinearizableReadNotify`) |
| U10 | the read loop's environment (`read/read.go:98-235`) | `readEnv` ← `Notifier.Receive`, `raftNode.ReadState/ReadIndex`, `timeList.Wait`, `Generator.Next` | **no** (F4) |
| U11 | linearizable reads inside the server (`v3_server.go:139,175,346,838`) | `Read.LinearizableReadNotify.spec` | yes |
| U12 | rafthttp `Raft` (`Process`, `IsIDRemoved`, `ReportUnreachable`, `ReportSnapshot`) | 2f's `raftOk` ← `EtcdServer.Process/IsIDRemoved/Report*.spec` | yes |
| U13 | wait registry: register/propose/trigger/GC (`v3_server.go:1107-1129`), the apply's trigger (`server.go:2007`), `IsRegistered` (`apply/apply.go:40`) | `Wait.*` | yes |
| U14 | `applyWait` (`server.go:985`, `read.go:135`, the token provider closure `server.go:353`) | `timeList.*` | yes |
| U15 | scheduler: `run`'s FIFO chain (`server.go:761,841`), mvcc's compaction jobs (`kvstore.go:107-310`) | `Schedule.*`, `isSched` | yes |
| U16 | consistent index: the apply thread, the hooks (`storage/hooks.go:46`), bootstrap, 3a's `Authenticate` (`apply/backend.go:158`) | `Cindex.*` | apply/hooks/bootstrap yes; **3a no** (F6) |
| U17 | health checks' empty-key range (`api/etcdhttp/health.go:224,435`), the `restart3` example (`AppliedIndex`, `Leader`, `HardStop`) | `Range.spec` (`emptyRangeStep`), 2e/2d getters | uncertain: etcdhttp is untranslated, and its handlers hold no gate share (cf. A7). Examples: yes |

## First-tier findings

### F1. Internal requesters cannot meet the request path's preconditions (2c, 2d)

**Principles:** Complete (every caller can establish the pre); No unneeded premise.

The server's own goroutines call 2c's methods (U5-U9). Their specs hold only `srvNode`/`srvStarted`,
but 2c's specs ask for three resources those goroutines cannot have:

- **`isServer s γ`.**
  - Which specs need it: `raftRequest.spec`, `LeaseRevoke.spec`, `Compact.spec` and `GoAttach.spec`
    all take it.
  - What the callers hold:
    - `run.spec` holds `srvNode ∗ srvStarted ∗ srvRunTok` (`EtcdServer__run.lean`).
    - `revokeExpiredLeases.spec` holds `srvNode ∗ srvStarted ∗ srvLessor ∗ …`, with no `isServer`.
    - `applyEntryNormal.spec` holds `srvNode ∗ srvStarted ∗ applyAt …`.
    - 3c's `ckptOk` gives the closure only `R := srvStarted s γ id` (`NewServer.lean:83`,
      `lease/Api.lean:356-369`).
  - Why they cannot get it: the only law is the elimination `isServer_names` (`ApiApply.lean:571`,
    `isServer ⊢ ∃ N id, srvNode ∗ srvStarted ∗ …`). Nothing introduces `isServer` from what these
    callers hold.
  - What fails: the sketches of `revokeExpiredLeases` (`GoAttach`, then `LeaseRevoke`), of
    `applyEntryNormal` (`GoAttach`, then `raftRequest` of the `NOSPACE` alarm), and of the
    checkpointer closure all fail at their first call.
- **`srvGate s q`.**
  - Which specs need it: `LeaseRevoke.spec` and `Compact.spec`.
  - Why the callers cannot hold it: `HardStop`/`Stop` take the whole `srvGate s 1`. The goroutines
    attached by `revokeExpiredLeases`, and the compactor goroutine, keep running through `HardStop`.
    The attached ones are waited for only in `run`'s deferred `s.wg.Wait()` (`server.go:821`); the
    compactor is stopped in `Cleanup` after the backend is closed (`server.go:960`). So no share can
    be reserved for them.
  - Why the premise is unneeded: Go does not need it on these paths. `LeaseRevoke` is
    `requireAuthInfo` + `raftRequest` (`v3_server.go:470-486`) and touches nothing that `Cleanup`
    closes. The compactor's `Compact` is never physical (`periodic.go:142`), so it skips
    `s.be.ForceCommit()` (`v3_server.go:402-415`).
- **`threadTok`.**
  - Which specs need it: `raftRequest.spec`, `GoAttach.spec` and `Notifier.Receive.spec` take one.
  - Which callers have none: `revokeExpiredLeases.spec`, `applyEntryNormal.spec` (for its
    `GoAttach`), `ckptOk`, `publishV3.spec`, `monitorClusterVersions.spec` and
    `monitorStorageVersion.spec`. Their pres are `isServer` (+ `srvPublish`), and nothing else.
  - What the Go code does: every one of them runs in an attached goroutine, and `GoAttach.spec` hands
    such a goroutine a token.
  - The per-lease goroutines of `revokeExpiredLeases`: one token each. The 16-slot channel `c`
    bounds how many are live at once, but no spec says where the tokens come from (uncertain how the
    bounds plan wants it).

**Fix.**
1. Give `run` (and through it `revokeExpiredLeases` and `applyEntryNormal`) `isServer s γ.etcd`.
   `start` makes `isServer` before `go s.run()`, so either take it in the pres or add a law
   `srvNode s γ id ∗ srvStarted s γ id ⊢ isServer s γ.etcd`. Make 3c's `R` `isServer`, or something
   that gives it.
2. Drop `srvGate` from `LeaseRevoke.spec`, and from `Compact.spec` when `phys = false`
   (`⌜phys = true⌝ → srvGate s q`). This is the same reasoning as open question 3.6(a) for
   `LeaseRenew`.
3. Add `threadTok` to the pres of the attached-goroutine specs (it is `GoAttach`'s gift), and to
   `ckptOk`.

**Recorded?** Partly. A7 and 3.6 record the gate for handlers (`LeaseKeepAlive`,
`Snapshot`), not for the internal requesters. `isServer` and `threadTok` are not recorded.

### F2. The compactor's `compactable` cannot be introduced from `Compact.spec` (2c's user; 2e's contract)

**Principle:** Complete.

**The contract.** `V3compactor.compactable_intro` (`v3compactor/Api.lean`) asks, for good
(persistent), from `NewServer` on, for any context with only `Context.ctxOk`, for
`WP Compact {threadTok}`. `NewServer.lean`'s step 5 says it is proved from `EtcdServer.Compact.spec`
and `envUpd`. It cannot be, for three reasons:

**(a) The server is not started when the contract is made.**
- `compactable` is needed by `v3compactor.New` at `server.go:380`, before `start`.
- `Compact.spec` needs `isServer`, which only `start` makes.
- In Go, a `Compact` before `start` panics: `s.w` is nil until `server.go:567`. That is why the
  comment at `server.go:384` says the compactor is run only by `start`.

**(b) The context is arbitrary.** `Compact.spec` takes `reqCtxOk ctx ∗ reqPrin ctx p tls`, and
neither holds of an arbitrary context. The compactor's real context is
`WithCancel(Background())`, which has `ctxNoIncoming`.

**(c) The gate.** The compactor has no `srvGate` share (F1).

**Fix.**
- Gate `compactable` on a resource `R` that `start` publishes, the way 3c's `ckptGate le R`
  works.
- Restrict the context to what `New` builds: a child of `Background`, giving
  `ctxNoIncoming ∗ reqCtxOk`.
- Apply F1's gate fix.

The snippet `ReqCompactorCompact` (`etcdserverreq/kv.go:138`) takes a generic started server and
context, so it hides all three points.

### F3. Specs cited by sketches and callers do not exist (coverage)

**Principles:** Complete; "A smaller API is not a narrower scope"; every premise has a source.

`batch-2d.md:120-121` hands "the request path's public accessors and checks (2c's: `AppliedIndex`,
`CommittedIndex`, …, `isLeader`, `isActive`, `ensureLeadership`, …)" to 2c. 2c wrote some of them
(`AppliedIndex`, `Term`, `Lead`, `Leader`) but not the rest. The specs that are missing, with the
users that need them:

**Functions with users:**
- `ensureLeadership` (`server.go:912`), cited as "2c's"/"2d's" by:
  - `revokeExpiredLeases.lean:8`;
  - `LeaseRenew.lean:8`;
  - `applyEntryNormal.lean:36`;
  - `NewServer.lean:83`;
  - 3c's `ckptOk` docstring.
- `isLeader` (`server.go:1263`): `LeaseRenew`, `applyEntryNormal`.
- `EtcdServer.LinearizableReadNotify` (`interface.go:46`): the corruption checker's hasher
  (`corrupt.go:187`) and the version monitor (`version/version.go:42,72`, reached from
  `monitorClusterVersions`).
- `AuthStore` (`server.go:2422`): v3rpc's `authMaintenanceServer.requireAuthInfo`,
  `AuthAdmin.isPermitted`, `serverWatchStream.isWatchPermitted` (their sketches call `AuthStore()`),
  and the snippet `ReqExpiryRevoke`.
- `Backend` (`server.go:2416`): v3rpc's `newBackendQuota` (whose sketch says "2e's spec"), and the
  maintenance handlers.
- `CommittedIndex` (`server.go:1764`): `maintenanceServer.Status` (`maintenance.go:277`).
- `ClusterVersion` (`server.go:2215`): `Status`, `Downgrade`, etcdhttp's version.
- `MemberList` (`server.go:1693`): `ClusterServer.MemberList` (its sketch cites "2e's spec").
- `FeatureEnabled` (`server.go:456`): v3rpc's health server (`health.go:39`).
- `NewUberApplier` (`server.go:1181`): `applySnapshot.lean:30`, and `NewServer`'s step 6.

**Functions that are only realized inline** (their old specs are dropped):
- `getTxPostLockInsideApplyHook`: proved inline in `NewServer`, but `applySnapshot` calls it too.
- The read-interface methods `ApplyWait`, `Done`, `LeaderChanged`, `NextRequestID`,
  `RequestTimeout`, `Stopping`, `FirstCommitInTermNotify`: realized only inside `readEnv`.
- `Backend`, `AuthStore`, `CommittedIndex`, `ClusterVersion`, `FeatureEnabled`: listed above.
- `read`'s `newNotifier`, `notifier.notify`, and `wait`'s `NewWithResponse`/`waitWithResponse.*`:
  no user outside tests (low priority).

**Fix:** one spec per function, over `isServer` (getters with the read-only facts their users need:
`Backend()` gives 2e's `beReadable`; `AuthStore()` gives 3d's `authStoreAt`; `CommittedIndex`, any
value), and specs of `ensureLeadership` (any boolean, given `isServer ∗ threadTok`) and `isLeader`.

**Recorded?** `batch-2d.md` "Left out" records the hand-off, but no file records it as not done.

### F4. The read loop's environment cannot be built from its callees' specs (2c `read/Api.lean` vs 2c `notify`, 2d `raftNode`)

**Principle:** Complete (a contract an implementation must meet, checked against the implementation's
specs). `readEnv` (`read/Api.lean:160-200`) is what `start` must prove for `s` and `&s.r`. Four rows
do not follow from the specs it would use:

1. **The `LeaderChanged`/`FirstCommitInTermNotify` rows have pre `True`.** These call
   `Notifier.Receive`, which takes `n.mu.RLock()` (`pkg/notify/notify.go:37-40`), and
   `Notifier.Receive.spec` takes a `threadTok`. Also, `Read.LinearizableReadLoop.spec` takes no
   `threadTok`, although `GoAttach` (`server.go:538`) gives it one.
2. **The `ReadState` row** gives `□ ∀ Φ, … -∗ recvAu` with no later credits. 2d's `readStateC_recv`
   (`ApiApply.lean:822-829`) needs `£ 1 ∗ £ 1` for each `recvAu`, so the row cannot be derived.
3. **The `ReadIndex` row's post is `⌜err = nil⌝ ∨ readErr err`.** `raftNode.ReadIndex.spec` gives R1's
   `nodeErr`, which is `errIs ErrStopped err`. But `EtcdServer.raftStoppedErr` is opaque
   (`errors/Api.lean:91`), and no law ties it to raft's `ErrStopped` (`errs_init`,
   `raft/v3/Api.lean:934`). The same missing law blocks `processInternalRaftRequestOnce`'s propose
   error, and `ErrProposalDropped` has no `srvErrShape` law at all. These are request-path
   provability gaps that show up here.
4. The `ApplyWait`, `NextRequestID` and `AppliedIndex` rows are fine (`timeChan_recv`,
   `Generator.Next`).

**Fix:**
- Rows 1 and 2: take `threadTok` in rows 1 (given back), and in `LinearizableReadLoop.spec`. Let the
  `ReadState` row take the receiver's credits, or restate `readStateC_recv` without them.
- Row 3: add a law `isPkgInit raft ∗ errIs ErrStopped e ⊢ ⌜e = raftStoppedErr⌝`, and a shape law
  for `ErrProposalDropped`.

**Recorded?** No.

### F5. The lease expiry's root context has no `reqPrin`/`reqCtxOk` (2c)

**Principle:** Every premise has a source the client sees.

- `LeaseRevoke.lean`'s header says the context `authStore.WithRoot(s.ctx)` has "`reqPrin` of 3d's
  `WithRoot` spec".
- But `authStore.WithRoot.spec`'s post gives only `ctx' = ctx ∨ ∃ tok, ctxToken ctx' (some tok) ∗
  tokenUser γ tok rootUser ∗ □(ctxPeerCN ctx c -∗ ctxCertUser ctx' c)`.
- 2c's introduction laws of `reqPrin` are `reqPrin_noIncoming`, `_child` and `_value`; 2a's is
  `reqPrin_of_md`, for gRPC run contexts. None of them applies to that context.
- Nothing gives `reqCtxOk ctx'` either: the post does not say `ctx'` is a value-child of `ctx`.

So `revokeExpiredLeases` cannot call `LeaseRevoke.spec` even after F1.

**Fix:**
- In 2c, add a law `ctxNoIncoming ctx ∗ ctxToken ctx' (some tok) ∗ tokenUser γ tok rootUser ∗ … ⊢
  reqPrin ctx' (some root) none`.
- In 3d, have `WithRoot`'s post give `Context.ctxValueAt ctx ctx'` at the incoming-metadata key, so
  that `reqCtxOk` follows from the value laws.

### F6. The cindex/apply thread owes 3a four predicates that have no introduction (2d)

**Principle:** Complete (the cindex API's user 3a is not served).

**What 3a's applier contract takes, and from where.** It takes `ciOk ci R` (`ConsistentIndex()`
under `R`, for `applierV3backend.Authenticate`, `apply/backend.go:158`), `snapSrvOk`, `statusOk` and
`authnIdx R γ name tok`, all marked "(provisional, 2d's)" in `apply/Api.lean:688-720`. It takes them
inside `optsOk` (`NewUberApplier`'s premise) and `nextOk` (`apply.Apply`'s).

**The gap.** No file introduces any of them. In particular, no law turns `Cindex.isCI ∗ ciState`
into `ciOk`, and nothing ties `authnIdx` to the apply thread's applying index. So
`applyEntryNormal`'s step "`apply.Apply.spec`, over the uber-applier's contract the thread holds",
and `applySnapshot`'s `NewUberApplier()`, have no source for these premises.

**Recorded?** As "left provisional" in `integration-I5.md:271`, with the to-do at `:306-308`. Not in
`open-questions.md`, and not resolved by X or Y.

## Second-tier findings

- **S1 (notify's user in membership, 2e).**
  - `RaftCluster.SetVersion` calls `c.versionChanged.Notify()` (`membership/cluster.go:620`).
  - `RaftCluster.SetVersionChangedNotifier.spec` records no `notifierAt n γ`, and `SetVersion` has no
    spec, so the notify API's third user is not served.
  - `monitorStorageVersion`'s receive on the same notifier needs `threadTok` (F1).
- **S2 (`rsSink`, `srvWatchable`, `txnChecked` still "provisional").** 2a has supplied their laws
  (`txnCheck_checked`, `rsSink` laws in v3rpc's `Api.lean`). The headers should drop "provisional".
- **S3 (health checks).** `ReqHealthRange` assumes a persistent read permission "the server's,
  2e's". No 2e law names it, and etcdhttp is untranslated (uncertain).
- **S4 (scheduler).** `NewFIFOScheduler.spec` forks the worker goroutine without taking a `threadTok`
  (bounds plan, not completeness; uncertain whether `wp_fork` needs one here).

## Snippets

The patterns are covered by `etcdserverreq/{kv,lease,auth,read}.go`, `etcdserverapply/*.go`,
`wait/*`, `cindex/*` and `schedule/*`, except:

- **No snippet for an internal requester running without a gate during a stop** (U5, U6: the aspect
  behind F1 and F2). Two snippets miss it:
  - `ReqExpiryRevoke` (`lease.go:28`) calls `s.AuthStore()`, which has no spec (F3), and assumes a
    gated caller.
  - `ReqCompactorCompact` assumes a started server and a generic context.
- **No snippet for the closure-before-start shape** (the compactor's `Compactable`, and the
  checkpointer's `ckptOk`).
- **No snippet for `EtcdServer.LinearizableReadNotify`**, the getters (`CommittedIndex`, `Backend`,
  `ClusterVersion`) or `MemberList`.

## Good

- The three-outcome `SrvCallTriple` fits 2a's handlers well: one composition paragraph in v3rpc's
  `Api.lean` covers every handler, with `srvStep_step`, `firedAns` = `srvFiredAns`, `srvErrShape` =
  `srvErrOk`.
- The wait registry (`waitDone`, `IsRegistered`), the time list, `idutil` and `schedule`
  (`schedTail`, `Pay`) serve their users exactly, including mvcc's cancelled compaction barrier.
- The rafthttp `Raft` bundle is met from `NewServer` on (`srvNode`).

## Ranking by need of revision

1. **F1:** the internal requesters (`revokeExpiredLeases`, `applyEntryNormal`, `run`, `ckptOk`,
   `publishV3`, `monitor*`; `LeaseRevoke`/`Compact`'s gate).
2. **F2:** compactor ↔ `Compact.spec`.
3. **F3:** the missing accessor and check specs.
4. **F4:** `readEnv` vs `Notifier.Receive`, `readStateC_recv`, and `raftStoppedErr`.
5. **F6:** `ciOk`/`authnIdx`/`snapSrvOk`/`statusOk`.
6. **F5:** `WithRoot` → `reqPrin`.
7. S1-S4.
