# Batch 2d, completeness review, round 1

Reviewer: completeness (independent of the author). Worktree `specs-only` at `011846a908` plus the
uncommitted batch files. Targets: `Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiApply.lean` and 2d's
specs in that directory (the apply thread, the atomics, `Process`/`Report*`/`IsIDRemoved`, the raft
node driver), `.../etcdserver/cindex/`, `Spec/go_etcd_io/etcd/pkg/v3/schedule/`; snippets
`examples/specreq/{etcdserverapply,cindex,schedule}/`. Go: the pinned server
`/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261107170612-a4d2bb1720b9`
(below `S/`), pkg `.../pkg/v3@...`, raft `565c2bd`. I formed the findings below before reading
`batch-2d.md`, then checked them against it (its "Open questions" and "Requirement sections").

## 1. Users and their patterns

I scanned the pinned etcd server/pkg (`grep` for `applyWait`, `s.w.`, `getAppliedIndex`,
`getCommittedIndex`, `errorc`, `cindex.`/`consistIndex.`, `schedule.`, `s.r.`), the req files of
2c, 2e, 2f, 2b, 2a, and the examples (`examples/lib/etcdstart`, `examples/etcd/{restart,leasesnap,
putget3}`). `schedule` and `cindex` have no users in Kubernetes or the examples.

| # | Pattern (what the user relies on) | Real call site | Snippet | Covered? |
|---|---|---|---|---|
| A1 | a proposed request's waiter gets a non-nil `*apply.Result`, the answer fixed at the commit (`x.(*apply2.Result)` panics on `nil`) | `S/etcdserver/v3_server.go:1107-1135` | `ReqWriteAnswered` | yes |
| A2 | NOSPACE: the refusal answered after the alarm is proposed | `S/etcdserver/server.go:2006-2029` | `ReqNoSpaceAlarm` | yes |
| A3 | a conf change's waiter: a `*confChangeResponse`, `raftAdvanceC` closes, `membs`/`err` mean the change was (not) applied to the membership | `S/etcdserver/server.go:1779-1821` (`configure`) | `ReqConfChangeAnswered` | snippet yes, spec no (F3) |
| A4 | `applyWait.Wait(i)` fires only once the member applied `i` | read loop (`read.go`, via `interface.go:23`), `waitAppliedIndex` (`v3_server.go:458`), leasehttp (`server.go:643`), auth simple tokens (`auth/simple_token.go:240`, closure `server.go:351-354`) | `ReqAppliedRead` | the index yes; what is read after it no (F1) |
| A5 | after the wait, the KV/lessor/auth/watch state read is at or past `histAt i` | 2c's `Range`/`Txn`/`doSerialize`/lease reads, 2b's `Watchable` | none | no (F1) |
| A6 | the read loop registers a read context with raft and gets it back on `ReadState` | `read.go` (`requestCurrentIndex`), 2c's `readEnv` | `ReqReadIndex` | snippet assumes a registration nothing provides (F2) |
| A7 | the read registry (`readReg_register`/`readReg_get`) | 2c's `EtcdServer__Range.lean:10,23` | none | no (F2) |
| A8 | `getAppliedIndex`/`getCommittedIndex`/`Term`: any value, no panic (gap check, maintenance `Status`, `isLearnerReady`); polling the applied index before a stop | `v3_server.go:1060-1061`, `v3rpc/maintenance.go:277-279`, `examples/etcd/restart/restart3.go:96-103` | `ReqAppliedRead` | yes (restart3's durability-at-stop rides on F4) |
| A9 | the transport's inbound `Process` (no panic, `procErr`), `IsIDRemoved`, `ReportUnreachable`, `ReportSnapshot`; a `MsgSnap`'s saved db reaching the install | rafthttp (`peer.go`, `stream.go`, `http.go`, `snapshot_sender.go`) | `ReqProcess` | `Process` yes; the other three have no snippet; the db hand-off no (F6) |
| A10 | `errorc`: rafthttp reports critical errors (`errMemberRemoved`, ...) and a removed member stops itself via `stopWithDelay`; `run` returns and shuts down | `rafthttp/stream.go:624`, `pipeline.go:170`, `snapshot_sender.go:113`; `server.go:1232` (`go s.stopWithDelay`), `server.go:1372`; `run` `server.go:845` | none in 2d (2e's `ReqStopAfterError` relies on it) | no, contradicted (F5) |
| A11 | start hands `run` its resources; stop drains the loop and gives back the member's durable state | `server.go:604` (`go s.run()`), `server.go:788-806` (deferred shutdown), 2e's `start.spec`, `HardStop.spec` | `ReqDriverLoop`, `ReqRestartContinues` | the handoff is not stated (F4) |
| A12 | snapshot at the applied index and raft-log compaction; merged snapshot; install | `server.go:1000-1017`, `1021-1179`, `2108-2194` | `ReqSnapshotCompact`, `ReqMergedSnapshot`, `ReqInstallSnapshot` | yes |
| A13 | restart / crash continue the history; lease expiry | `examples/etcd/restart`, etcdstart, robustness | `ReqRestartContinues`, `ReqCrashKeepsAnswered`, `ReqLeaseExpiry` | yes (top level) |
| A14 | readers of the current backend across a snapshot swap (`s.Backend()` under `bemu`) | `server.go:982`, `v3rpc/quota.go:93`, `v3rpc/maintenance.go:141,146,280` | none | no spec, no snippet (F8) |
| C1 | apply thread: applying index, consistent index (also through the post-lock hook) | `server.go:1925-1938, 1975-1977, 2042-2043, 2478-2484` | `ReqApplyMovesIndex` | yes |
| C2 | bootstrap / snapshot install: `SetBackend` then `ConsistentIndex()` is the backend's stored index | `bootstrap.go:257-273, 486-491, 629`, `server.go:1080,1100` | `ReqReloadAfterSetBackend` | yes |
| C3 | backend pre-commit hook `UnsafeSave(tx)` concurrently with the apply thread | `storage/hooks.go:46` | `ReqSaveInCommit` (sequential) | partly (second tier, S5) |
| C4 | the applier's `Authenticate` reads the index (token's issue index) | `apply/backend.go:158` | none | no snippet needed (same as C1, `ciWriter` lent by 3a) |
| D1 | FIFO chain, one at a time, each job sees the previous one's state | `server.go:761, 841` | `ReqFifoChain` | yes |
| D2 | `Stop` returns after every pending job ran | `server.go:798`, `mvcc/kvstore.go:297, 517` | `ReqStopRunsPending` | yes |
| D3 | a job sees its context done only after `Stop` (mvcc's `compactBarrier`) | `mvcc/kvstore.go:137-152, 201, 236-257` | `ReqCancelledCtx` | yes |
| D4 | a job schedules onto a (new) scheduler from inside a job (`compactBarrier`'s reschedule under `s.mu`) | `mvcc/kvstore.go:147-148` | none | second tier (S7) |
| D5 | `Restore`: `Stop` then a new scheduler in the same field | `mvcc/kvstore.go:292-311` | `ReqStopRunsPending` + `NewFIFOScheduler` | yes |

## 2. First tier (a user not served, a snippet unprovable)

**F1. The member's applied state is tied to the history by no law: linearizable and serializable
reads, lease reads and watches are not served.** (Complete; 2c's item 6, 2b's item 3.)
Evidence: `ApiApply.lean` gives `srvApplied s γ k ⊢ ∃ σ, histAt γ k σ` (`srvApplied_hist`) but nothing
that relates what a reader of `s.KV()`, the lessor or the auth store sees to `histAt`; 2d's own
answer to 2c (`req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2d" item 5) says "open at
integration" and `batch-2d.md`'s "Open questions" does not list it. Callers affected: 2c's
`EtcdServer__Range.lean:19-22` (`get` "at an applied point `kr ≥ kp`: the answer `res` is one `Step`
allows at `histAt γ kr σ`"), `Txn`, `doSerialize`, the lease reads after `waitAppliedIndex`, 2b's
`watchMemberAt`/`srvWatchable` (2c item 9: "2d/3f realize it"). `ReqAppliedRead` only checks the
applied index, not the state read after the wait, so the snippets do not capture the pattern the
read path relies on. Fix: state the reader's law now, over a provisional slot if 3e/3c/3d have none
yet: e.g. `srvReadAt s γ : □ (∀ k σ, srvApplied s γ k -∗ histAt γ k σ -∗ <mvcc reader's view is at
some histAt γ k' σ' with k ≤ k'>)`, and the lessor's and auth store's views alike, each a named slot
of the subsystem (the hub's slot convention); add a snippet `ReqReadAfterApplyWait` (wait at the
committed index, then a `txn.Range` over `s.KV()` that panics if a write committed before the
committed index was read is missing). If it must stay open, record it as an open question in the
batch's section of `batches.md`.

**F2. The read-context registration and the read registry that 2c's specs cite are missing from
2d's cluster invariant's laws.** (Complete; "every premise has a source the caller sees".)
Evidence: `ApiApply.lean`'s header says the cluster's invariant owns raft's `readCtxs` (lines 17,
74), but no law lets anyone register a context. 2c's `read/Api.lean:26-31` requires "the registration
of a read context ... The server holds raft's client-owned `readCtxs` and `committedOps` in its
cluster invariant, so it is the one that can register"; 2c's `EtcdServer__Range.lean:10,23` cites
"2d's `readReg_register`" and "`readReg_get`" (2c's item 5 with their statements); 2d's answers
(item list in `req/...etcdserver.md`, "from 2d") skip 2c's items 3 (registration) and 5 (registry).
2d's own `ReqReadIndex` says `Assumes: rctx was registered with raft (readCtx_register, the
server's)`, which no caller can establish without such a law. Callers affected: 2e's `start` (builds
`readEnv`, hence every linearizable read), 2c's `Range`, `Txn`, `RangeStream`, `Authenticate`. Fix:
add to `ApiApply.lean` (proved from the cluster invariant):
`readCtx_reg.spec : ∀ γ c Q E, ↑etcdN ⊆ E → ⌜c fresh⌝ -∗ ... ={E}=∗ Raft.readCtx γ.raft c Q` (in the
shape of 2c's `readEnv` registration, `readLbQ l`), and 2c's `readReg_register`/`readReg_get` (or the
replacement 2c and 2d agree), and say in `ReqReadIndex` which law establishes its assumption.

**F3. A conf change's answer is not tied to the history; `ReqConfChangeAnswered` is unprovable.**
(Complete; snippet provable.) Evidence: `apply.spec`'s sketch (`EtcdServer__apply.lean:16-19`) and
2d's answer to 2c (item 3) give the conf change's waiter only `advancedAt r rac last` and "the
members read from the membership view"; `applyConfChange.spec`'s post says only
`err = nil ∨ removed = false` (`EtcdServer__applyConfChange.lean:78-80`), and there is no
`answered`-like fact for conf-change entries, while `ApiApply.lean` says `histPropose` covers
`configure`. The snippet panics unless an accepted `AddNode` is in `resp.membs`
(`apply.go:66-72`): nothing states that. The real caller (`configure`, `server.go:1789-1806`, then
`AddMember`/`RemoveMember`/`UpdateMember`/`PromoteMember`, 2a's item 7 to 2e) needs `err = nil` ⇔ the
change was accepted at its index `k` and `membs` is the membership at `histAt γ k` (for the client's
`MemberAdd` linearization). Fix: make the wait registry's conf-change predicate carry
`answered γ k cc.ID res` (or a `confAnswered γ k id ok`) with `resp.err = nil ↔ ok` and `resp.membs`
the members of the state at `k`, state it in `apply.spec`'s post or a law, and put it in the req
answer to 2c/2e.

**F4. `run`'s precondition cannot be established by its one caller, and its post gives the stopper
nothing it can use.** (Complete: "each caller can establish the precondition and gets from the
postcondition what its proof needs".) Evidence: `run.spec` takes `srvNode s γ id ∗ srvStarted s γ id
∗ srvRunTok s γ id` and returns `True`, depositing `srvStopped s γ id` in an escrow
(`EtcdServer__run.lean:47-60`). `ApiApply.lean` has no law introducing `srvNode` (from `NewServer`),
`srvStarted` (from `start`) or `srvRunTok` (from `rnInit_place`'s `rnLoop`/`rnStopper`, the ready
handler's writers, the initial apply-thread state, the channels' rights, the escrow), and none
eliminating `srvStopped`. 2e's side: `EtcdServer__start.lean:9-11` builds "2d's `run` precondition"
from `srvBuilt`'s apply-thread slot, and `EtcdServer__HardStop.lean:12` expects `run` to deposit
`memberDisk γ id ds` (with `ds`, which 2d's `srvStopped s γ id` does not carry); 2d's req item 8
calls the conversion "a law of 2e's", but `srvStopped` is 2d's opaque predicate, so only 2d can
state it. Also the run sketch's `srvRunTok` "holds ... `applyThread s γ ep₀ p₀`", but `ep` is a
local allocated inside `run` (`server.go:810-816`): the token can hold only a location-free initial
state. The id types differ (2d `w64`, 2e `Nat`). Callers affected: 2e's `start.spec`,
`HardStop.spec`/`Stop.spec`, `examples/etcd/restart` (`restart3.go:96-103`: polls
`AppliedIndex() ≥ NBoot` and relies on the stop leaving those entries in the data directory).
Fix: in `ApiApply.lean`, `srvRunTok_intro` (from the exact pieces `start` holds: `isRaftNode`,
`rnLoop`, `rnStopper`, `readyHandler` pieces or the closure's precondition, a location-free
`applyInit s γ p₀ ci₀` with `ci₀ ≥ p₀.appliedi`, the channel rights, the escrow name), `srvNode`/
`srvStarted` intro laws (or make them 2e's slots), and `srvStopped_disk : srvStopped s γ id ∗
<what 2e adds: the closed backend, ds> ⊢ memberDisk γ id ds` (or have `run` deposit into an escrow
predicate 2e names); one id type.

**F5. `run` assumes nothing sends on `errorc`; 2f, 2e and 2d's own `applyEntries` send on it.**
(Complete; sound.) Evidence: `run`'s sketch: "`errorc` is never sent on (2e's invariant: nothing
writes it in the runs covered)" and Margin "`errorc`'s exit ... is outside: nothing sends on it"
(`EtcdServer__run.lean:28, 41`). But `applyEntries` forks `go s.stopWithDelay(...)` when the member
removed itself (`server.go:1231-1232`), which sends on `s.errorc` (`server.go:1371-1374`); the
transport's streams, pipelines and snapshot sender report critical errors on it
(`rafthttp/stream.go:624`, `pipeline.go:170`, `snapshot_sender.go:113`); 2f's
`Rafthttp/Api.lean:191-193` asks for `errChanOk srv.errorc` "(server, 2d)"; 2e's snippet
`ReqStopAfterError` (`examples/specreq/etcdserverboot/boot.go:200`) relies on `run` returning on a
transport error. `applyEntries`'s sketch also misdescribes the path ("an attached goroutine that
sends the stop request": it is a raw `go`, sending on `errorc`, not `s.stop`). Pattern A10
(MemberRemove of a running member; a member told it was removed) has no snippet. Fix: `run`'s
loop treats `errorc` as `stop` (same shutdown, same deposit; the post is unchanged); export
`errChanOk s.errorc` from `srvNode` (a law), give `stopWithDelay` a spec (2e or 2d) and fix
`applyEntries`'s sketch; add a snippet (`ReqRemovedSelfStops`: an accepted `RemoveNode` of the
member's own id, then `<-s.StopNotify()`, then `HardStop`, no panic).

**F6. The received snapshot's database does not reach the install.** (Complete against 2f; the
install's source.) Evidence: 2f's `raftOk` contract passes `recvd ν ss m` to `Process`, which for a
`MsgSnap` holds the saved database (`req/...etcdserver.md`, "from 2f" item 1, 3); 2d's own need (req
rafthttp, "from 2d" item 5) says it "must reach the apply thread's `applySnapshot`... (the server's
invariant keeps it from `Process` to the batch's install)", but `Process.spec`'s pre takes only
`msgSent`/`msgCredit` (`EtcdServer__Process.lean:50-51`), so the database resource is dropped, and
`applySnapshot`'s sketch then cites "2f delivered the db to the snapshotter" without a resource.
(2e's latest note, req rafthttp "from 2e" item 3, moves this to an update over `Snap.snapDbs`.)
Callers affected: rafthttp's snapshot handler; `examples/etcd/restart` (the restarted member is caught
up by a snapshot). Fix: decide with 2e/2f which resource carries the saved `.snap.db` (2e's
`snapDbs`/`saveAt` in the server's invariant is simplest) and make `Process.spec` and
`applySnapshot.spec`'s sketch name it; `ReqInstallSnapshot`'s `Assumes` should say where the db
comes from.

## 3. Second tier

- **S1. `ReportUnreachable`, `ReportSnapshot`, `IsIDRemoved` have no snippet** (`raftnode.go`'s
  header names them; only `ReqProcess` exists). One call-only snippet suffices.
- **S2. `srvNode`'s docstring contradicts the header**: "`s` is member `id`'s server ... (after
  `start`)" (`ApiApply.lean`, `srvNode`) vs "as `NewServer` built it (... `Process` may be called from
  then on)" (header) and `Process.spec`'s "Callable from `NewServer` on". 2f needs the latter (the
  transport starts inside `NewServer`, `server.go:412-426`). Fix the docstring.
- **S3. The auth store's simple-token waiter is a user of `applyWait` not listed** (`auth/
  simple_token.go:240`, the closure `server.go:351-354`, built in `NewServer` before `start` assigns
  `s.applyWait`, `server.go:568`): add it to `ReqAppliedRead`'s Users and tell 3d/2e that the
  closure's contract (`srvApplied` on the receive) holds only from `start` on.
- **S4. `raftNodeBootCfg` disagrees between 2e and 2d.** `ApiBoot.lean:274-276` says a positive
  heartbeat ("`time.NewTicker` panics at `≤ 0`"); `newRaftNode` handles `0` (`raft.go:152-153`), and
  2d's `newRaftNode.spec` takes `0 ≤`. ApiBoot's provisional `raftNodeBuilt rn γ id st` is also not
  2d's vocabulary (`rnInit`/`rnCfgOk`/`isRaftNode`). Integration item; 2d should say in its req answer
  which predicate replaces `raftNodeBuilt`.
- **S5. `ReqSaveInCommit` is sequential, the real use is concurrent.** `hooks.go:46` runs on the
  backend's commit goroutine while the apply thread moves the index; the snippet's `Assumes` admits
  it. What the restart relies on (a commit's stored index is the last entry whose effects that commit
  holds) is 2d's server invariant, captured only at the top (`ReqCrashKeepsAnswered`). Consider a
  snippet in `etcdserverapply` (a forced commit during an apply; after a crash and reopen, the stored
  index's entry's write is present and the next one's absent).
- **S6. `ReqDriverLoop` relies on what `rnStopped` does not give**: it reads `r.raftStorage` after
  `stop()`, but `raftNode.stop.spec`'s post `rnStopped r γ id` has no law returning the storage. No
  real caller reads it after stop (`run` calls `Cleanup`), so drop the read or add the law.
- **S7. A job scheduling from inside a job** (`mvcc/kvstore.go:147-148`, onto the store's *new*
  scheduler after `Restore`): the bundle allows it (a `schedOpen` fraction and a `True` tail in
  mvcc's `s.mu` invariant), but no snippet shows it; 3e's req could say so.
- **S8. `EtcdServer.Backend()` has no spec and the backend swap no snippet** (pattern A14:
  `applyAll`'s `VerifyBackendConsistency`, 2a's quota and maintenance). `srvNode`'s realization owns
  `bemu`'s invariant ("the current backend"), so 2d is the natural owner of the reader's contract
  (which backend a reader gets, what it may do after `applySnapshot` swaps and `go oldbe.Close()`s it:
  `Size`/`SizeInUse` only, 2e's `beReadable`). The pinned fork fixes the three blocks-proof issues of
  this swap (`issues/etcd-quota-stale-backend-after-snapshot.md`,
  `etcd-auth-snapshot-closed-backend-panic.md`, `etcd-alarm-store-snapshot-race.md`: alarm `Recover`,
  close after auth, `server.go:1116-1145`); the contract should say what keeps holding. Also
  `applySnapshot`'s sketch calls `go oldbe.Close()` "an attached goroutine": it is a raw `go`
  (`server.go:1137`), which `run`'s `s.wg.Wait()` does not wait for.
- **S9. Lease checkpoints and cluster-version entries** (the lessor's checkpointer through
  `raftRequestOnce`, `apply/backend.go:270-284`'s `ForceSnapshot` on a downgrade) are applied as
  "nothing observable" steps; no snippet exercises an entry with no waiter and no model change (e.g.
  the `ar == nil` return, `server.go:2002-2004`). Cheap to add.

## 4. Establishable and sufficient, one call site per pattern

- A1, `processInternalRaftRequestOnce` (`v3_server.go:1107-1135`): pre of the apply side is 2d's
  internal; what the requester gets is 2c's `P id x`, which 2d's req answer item 3 states
  (`answered γ k id res` and `applyResult`). Sufficient given 2c's ghost box (2d's item 2).
  Establishable: yes.
- A3, `configure`: insufficient (F3).
- A4, the read loop's `ApplyWait(confirmedIndex)`: the receive gives `srvApplied s γ i` (2c's
  `timeListAt` at `srvApplied`, `applyAll` triggers it); sufficient for the index, not for the read
  that follows (F1).
- A6, the read loop's `ReadIndex`: not establishable (F2).
- A9, rafthttp's `Process`: establishable (`srvNode`, a token, `recvd`'s `msgSent`/`msgCredit`);
  post `procErr` is what 2f needs. The `MsgSnap` db: F6.
- A11, `start`'s `go s.run()`: not establishable (F4); `HardStop`'s `<-s.done`: insufficient (F4).
- A12, `applyAll`'s snapshot/compaction/merge: establishable from the chain's invariant
  (`schedTail` with `applyThread` at `B.prev`) and `applyBatch`; posts sufficient for `run`.
- C1-C2, the apply thread and bootstrap: establishable (`ciWriter` held by the one writer;
  `beStoredCI` from 2e's `OpenBackend`/`OpenSnapshotBackend`, req backend item 1); sufficient.
- C3, `hooks.go:46`: establishable if the server's batch-lock invariant keeps `c ≤ idx` (the
  `UnsafeSave` AU's premise); after `SetBackend`, a final commit of the *old* backend
  (`go oldbe.Close()`) writes the new index into the old file through the same hooks: the premise
  still holds (`idx` is `0` or past the old stored index), harmless.
- D1-D3, `run` and mvcc: establishable (`NewFIFOScheduler` for any `Pay`; `run` with `Pay := True`,
  mvcc with "`stopc` closed"); `Stop` gives back the tail. Sufficient.

## 5. Relaxable premises

None found beyond S4 (2e's positive heartbeat). `applyAll`'s `uint.nat p.appliedi = B.prev` is what
the code needs (`applySnapshot`'s "outdated index" panic, `applyEntries`' index check). `Process`'s
`threadTok` is 2f's own contract.

## 6. Per target

**`ApiApply.lean` and the apply-thread specs.** Good: one history for every member, snapshot,
restart and crash (no restart premises, no window tokens); the merged-snapshot guard is the code's;
`applyAll` and its parts are over footprint-sized `applyThread`/`applyBatch`; the snippets cover the
write, NOSPACE, snapshot, merge, install, restart, crash and lease-expiry patterns. Findings: F1, F2,
F3, F4, F5 (and S2, S8, S9).

**The raft node driver and `Process`/`Report*`/`IsIDRemoved`.** Good: write-before-send for
followers and leader-first for the leader stated as R1's `readyEnter`/`readyCheck`; `sendable` is
exactly 2f's `outMsg`; `procErr_forbidden` meets 2f's contract. Findings: F6, F5 (the `errorc`
channel is the driver's peer's), S1, S4, S6.

**`cindex`.** Good: one client-owned logically atomic state with a writer's token fits every user
(apply thread, post-lock hook, bootstrap, the applier's `Authenticate`, the concurrent pre-commit
hook); the snippets cover the three patterns. Finding: S5 only.

**`schedule`.** Good: the chain end `schedTail` gives `run` its last state back and lets mvcc keep
`True`; `Pay` captures `compactBarrier`'s reliance exactly; all three users' patterns are covered.
Finding: S7 only.

## 7. Ranking by need of revision

1. `ApiApply.lean` with `run`/`apply`/`applyConfChange`/`applyEntries` (F1-F5).
2. The driver and the transport's inbound calls (`Process.spec`, F6; S1, S4, S6).
3. `cindex` (S5).
4. `schedule` (S7).

## Verdict

Not done. The snippets cover most patterns and the apply thread's internal chain is sound in shape,
but six first-tier gaps leave users unserved: the read path's state (F1), the read-context
registration and read registry (F2), the conf-change answer (F3), the start/stop hand-off of `run`
(F4), `errorc` (F5), and the received snapshot's database (F6). F1 and F2 were requested by 2c and
are not answered or recorded as open questions; F4 and F5 contradict what 2e and 2f wrote they need.
`cindex` and `schedule` are complete. No new Go bug found (the snapshot-swap issues S8 touches are
already recorded in `issues/` and fixed in the pinned fork).
