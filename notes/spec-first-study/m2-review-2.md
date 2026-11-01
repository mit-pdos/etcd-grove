# M2 spec skeleton, review round 2 (phase 1b)

*Copied to `lean` on 2026-11-01 from branch `m2` (M2's first attempt, paused after this round and superseded by `m2-storage-plan.md`/`m2-apply-plan.md`), which was then deleted: the commits this review names (`m2`'s, up to `98c3d7c6f2`) are no longer reachable.*

Reviewer: a new `spec-reviewer` agent, 2026-10-28. Worktree `/shared/etcd-grove-cp`, branch `m2`.
Commit under review: `9eaa0e34de`, which is `HEAD`. The changes since round 1 are the two commits
`f4629d8be1` (one family; `store.Compact` without `NoDelPutAt`) and `9eaa0e34de` (`NewServer`/`newServer`
as one statement each; `wsUnwatched`). `8950d80bf2` is not an ancestor of `HEAD`, so most of
`git diff 8950d80bf2..9eaa0e34de` comes from the merge base; I reviewed the two commits.
I read the Go code at the fork's `249d76bea` in `/shared/etcd-fork-m2`. I built nothing and did not
run `etc/tcb-report.py`, so every claim about the trust base below comes from reading the text.

## Summary (tier 1)

1. **`NewServer.spec`'s compactor-on case cannot be proved** (Q1). Its post gives
   `mvcc.watchTokPool γw`, and the compacting server must also make `wsUnwatched γw`. A pool with
   no tokens needs `⧗ a` with `receiptBound ≤ a + 1`, and no proof can produce that many receipts
   at construction. A pool that holds tokens leaves none for `wsUnwatched`. Separately,
   `mvcc.New.spec`'s post has already frozen the compaction right (`crevFrozen`, inside
   `isWatchableStore`), so `NewServer` has no `compactRight` to give the apply thread.
2. **The one family admits compaction on servers whose store is frozen.** `Compact.spec` and
   `reqPropOk` take the general `isServerReq`, so a compaction-off server, whose watchable store
   carries `crevFrozen`, can also commit a compaction entry. The apply arm (the `sorry` at
   `uberApplier__dispatch.lean:479`) has no way to discharge that case. `dispatch.spec`'s
   `kvOwn` holds no compaction right, and `applierTriples` has no `Compaction` triple. On a frozen
   store no right exists at all. The compaction mode is still a real server-wide property; the
   design moved it out of the statements without removing it.
3. **`compactResultIs` does not follow from `dispatchAnswer`'s compaction case** (Q2).
   `dispatchAnswer` says nothing of the response: neither its dynamic type, which
   `Compact`'s type assertion needs, nor ownership of the response and its header, which `Compact`
   writes. It also says nothing of the trace on an error, which `Compact` touches before it tests
   the error. So `specCompact` cannot be derived from the general `spec`, and its own proof is a
   bare `sorry` with no callees.
4. **Trust exposure.** The new `sorry`s now sit inside the general proofs: `NewServer.wp_proof`,
   `uberApplier.dispatch.wp_proof`, `syncWatchers.wp_proof`, `store.Compact.wp_proof`,
   `kiGet_avail`, and `dispatchAnswer_notNoSpace` (off and on). Every existing result therefore
   rests on them (`putget_safe`, `watch_safe`, `cache_safe`, ...). This is a consequence of
   having one family, but the baselines were not updated. `etc/tcb-baseline.txt:733-734` and
   `etc/tcb-collections/m2.txt` still list `NewServer.wp_proofCompact`, which `9eaa0e34de`
   removed, and they list none of the new `sorry`s. `--check` therefore fails, on reading (not run).

Answers to the author's questions are in the "Questions" section at the end.

---

## T1. The KV model: `plainCover`/`putgetKind`, `dispatchOk`, `dispatchStep`/`compactStep`, `dispatchAnswer`'s compaction case, `applyEntries_model` and the results over them

### Good
- `compactStep` (`apply/InvUber.lean:71`) agrees with the chain in Go. `applierV3Corrupt.Compaction`
  returns `ErrCorrupt` (`apply/corrupt.go:45-47`). The auth, quota and capped appliers do not
  override `Compaction` (grep `func (a *…)` in `apply/*.go`), and `needAdminPermission` is false
  for a compaction (`apply/auth.go:244-274`), so the request reaches the backend.
  `applierV3backend.Compaction` returns the store's error or success (`apply/backend.go:66-80`).
  `o = .applied log false` is right: a compaction changes no value at a revision it keeps, and the
  quota never reports `ErrNoSpace` for it. Matching only the top-level `.corrupt` is right because
  `alarmChain` puts `corrupt` outermost (`apply/Chain.lean:93-96`).
- The error disjunction in `dispatchAnswer`'s compaction case (`InvUber.lean:286-290`) matches
  `updateCompactRev` (`mvcc/kvstore.go:197-221`): `ErrCompacted` for `rev ≤ compactMainRev`,
  `ErrFutureRev` above `currentRev`, otherwise `nil`.
- `plainCover`'s compaction case (`KVModelDefs.lean:81-82`) and `rqOk`'s `True`
  (`apply/Chain.lean:285`) make `reqPropOk`'s first disjunct (non-write, `Qr` trivial) admit a
  compaction, as the plan intended. No separate compaction form of the permit is needed, and none
  was added.
- `chainLog_nonwrite` together with `writeKind` excluding `.compaction` keeps the KV model
  (`kvModel`) unchanged by compaction entries. So `applyEntries_model` and the read results stay
  true about values.

### Findings

**T1-1 (tier 1: true/sufficient; the main finding). The compaction arm cannot be discharged from
`dispatch.spec`.** `apply.uberApplier.dispatch.spec` (`Spec/.../apply/uberApplier__dispatch.lean:40-60`)
takes `apply.kvOwn E log` (`apply/Chain.lean:380-382`: reader, writer, leases, `E.RD`, `writerOwn`)
and `applierSpec E c a`. Neither has what the arm needs.
- `applierTriples` has no `Compaction` method. The file says so: "every method but `Compaction`,
  which is out of the model" (`Chain.lean:32`). The arm calls `a.applyV3.Compaction(...)` through
  the interface (`uber_applier.go:143-145`).
- No `compactRight` is in the apply thread's resources, and `store.Compact.spec` requires
  `compactRight γ c` (`Spec/.../mvcc/store__Compact.lean:66`).
- For a compaction-off server the right does not exist. `mvcc.New` freezes it:
  `newWatchableStore.lean:58` runs `crevFrozen_alloc … $$ Hright`, and `New.spec`'s post
  (`Spec/.../mvcc/New.lean:48-49`) gives no `compactRight`. But with one family that server's KV
  invariant and `reqPropOk` admit a compaction entry, and `EtcdServer.Compact.spec` takes
  `isServerReq` of any server. A gRPC client of `putget`'s server (v3rpc's `kvServer.Compact`
  reaches `EtcdServer.Compact`) can commit one, and the arm must then compact a store whose
  invariant `crevFrozen` says it never compacts.

*Affects:* every result over `dispatch` (`applyEntries_model`, the request path, all examples),
plus `Compact.spec`, `specCompact` and `putgetc_safe`.

*Restatement.* The mode is a fact about the server, so it should appear where compaction is
proposed, not in a second family:
- The proposal permit's compaction case and `Compact.spec` take a persistent `srvCmpOn E`. Only a
  compacting server's `NewServer` gives it. It is exclusive with `crevFrozen E.γ`: for example, a
  `dghostVar` mode allocated at `New`, or `inv` of the right's other half.
- `kvOwn` carries `(crevFrozen E.γ ∨ ∃ c, compactRight E.γ c ∗ srvCmpOn E)`. The arm's frozen case
  gets a contradiction from the entry's `srvCmpOn`, which the KV invariant records for compaction
  entries (as `entryClaim` does).
- `applierTriples` gets a `Compaction` triple over the right.
- `mvcc.New.spec` takes a ghost choice `cmp : Bool`: either freeze, or return `compactRight γ (-1)`
  with `wsUnwatched`.

This reaches `Compact.spec`, `reqPropOk`'s non-write case for compactions, `kvOwn`/`applierTriples`
and `New.spec`. It does not reach the KV readers or the write paths.

**T1-2 (tier 1: sufficient for the caller `specCompact`). `dispatchAnswer`'s compaction case is too
weak for what `Compact` does with the result.** The case (`InvUber.lean:286-290`) constrains only
`err`. `Compact`'s Go code:
- `resp := result.Resp.(*pb.CompactionResponse)` (`v3_server.go:422`) panics unless `Resp` has
  that dynamic type;
- writes `resp.Header.Revision` (`:428`), which needs `rp ↦ cv ∗ cv.Header' ↦ hv` when non-nil;
- calls `result.Trace.SetStartTime` (`:399`) before it tests `err`, which needs `traceRes
  v.Trace'` on the error path too.

`compactResultIs` (`CompactMode.lean:78-87`) asks for all three. `dispatchResult` gives `ar ↦□ v`
and `applyErrIs`. `resTrace` gives `traceRes` only when `Err' = nil` (`InvUber.lean:306-307`). The
put, delete and txn cases carry the response type and header (`putAnswerIs`,
`apply/Chain.lean:634-638`, `appliedHdr`); the compaction case is the odd one.

*Restatement:*
`| .compaction => ∃ r : Loc, ⌜resp = mkOk (Ptr CompactionResponse) #r⌝ ∗ match o with
 | .rejected k => ⌜r = null⌝ ∗ rejErrIs (…) k err | .applied _ ns => noSpaceErrIs ns err ∗ ⌜r ≠ null⌝
 ∗ ∃ cv, r ↦ cv ∗ ∃ hv, cv.Header' ↦ hv`.

This is true of Go: `backend.go:67-68` allocates both, and on error it returns a typed nil, which
the corrupt applier also does. For the trace there are two options:
- (a) `resTrace` loses its `Err' ≠ nil` escape. That is true where every error path's trace is
  either nil or owned. **Uncertain**: I did not check every applier method's error-path trace.
- (b) A compaction-specific clause in `dispatchResult` that the trace is `null` on rejection.
  This is true: `backend.go:74`, `corrupt.go:46`.

**T1-3 (tier 2: stale prose, which a reader of `interface/` sees).** These texts still say that
compaction is outside the model:
- `apply/Chain.lean:18`, `:32`, `:200-201` (`backendStep`'s "Compaction is out of the model
  (`False`)": the case is dead now that `storeKind` excludes it, but the docstring misleads);
- `apply/Results.lean:37`;
- `dispatch.spec`'s docstring ("the premise `dispatchOk`: not a compaction",
  `Spec/.../uberApplier__dispatch.lean:31-32`).

**T1-4 (tier 2: trust).** Two `dispatchAnswer_notNoSpace` `sorry`s, `NoSpaceDead.lean:200` and
`NoSpaceDeadOn.lean:147`. They should be discharged now. Under `compactStep` the compaction answer
is `ErrCorrupt`, `ErrCompacted`/`ErrFutureRev` or `nil`, never `ErrNoSpace`, so each is a short
proof by distinctness of the error variables. As they stand they are new `sorry`s under every
result.

---

## T2. `processInternalRaftRequestOnce.specCompact`, `compactResultIs`, `CompactMode.lean`

### Good
- Round 1's S2-2 (the trace owned twice) is **stale**: the success post is `compactResultIs`
  alone (`Spec/…/EtcdServer__processInternalRaftRequestOnce.lean:120`).
- S2-3 is **stale**: there is no revision bound. S2-4 and S2-6 are **stale**: `irrNoDelPut` and
  `dispatchOkC` are gone. S2-5 is **stale**: the docstring now says "on an error a nil one".
- `compactPropOk` is small and decidable.

### Findings

**T2-1 (tier 1: special-case family; checked only against an unproved statement).** `specCompact` is still a
third triple of the same function. Its proof is a bare `sorry` with no callee hypotheses
(`Proof/…/EtcdServer__processInternalRaftRequestOnce.lean:715-717`), and the comment there ("in
compaction mode") is stale. With one family it should be a corollary of `spec`:
`spec ⊢ specCompact`. That needs `reqPropOk`'s first disjunct for `compactPropOk rq`, which is
pure, and a law `resultIsW E γr rq' F res lb ⊢ compactResultIs res` for a compaction `rq'`. The
law cannot be proved until T1-2 is fixed. Proving the corollary now is glue, and it is the check
this skeleton phase calls for.
*Restatement:* `theorem specCompact_of_spec (h : processInternalRaftRequestOnce.spec) :
specCompact` in a proof file; `Compact`'s glue takes `spec` as its callee.

**T2-2 (tier 2: weakest statement).** On success, `compactResultIs` admits `rp = null` and
`Header' = null`. Go never produces those on success (`backend.go:67-68`). `Compact` copes with
them (`v3_server.go:423-427`), so this is harmless. Once T1-2 holds, the weaker form is a choice,
not a necessity.

---

## T3. `EtcdServer.Compact.spec`, `CompactEnv.lean`

### Good
- Round 1's S3-2 (`specOn`) is **stale**: it was removed. S3-3 is partly addressed:
  `errTreeOk_of_applyErrIs`, `errTreeOk_nil` and `compactableOk_server` exist
  (`CompactEnv.lean:39-99`), and `NewServer.wp_proof` takes `Compact.spec` and `store.Rev.spec`
  as hypotheses.
- `compactableOk_server` is law-based: it unfolds only its own `srvCompactR` and the frozen
  `compactableOk`.

### Findings

**T3-1 (tier 1: inherits T1-1).** `Compact.spec` is claimed for every `isServerReq` server. On a
compaction-off server its proof needs the arm on a frozen store. *Restatement:* add the premise
`srvCmpOn E` (T1-1).

**T3-2 (tier 2: weakest statement; the brief's question "is `revPermit (srvRevLb …)` still
needed?").** The permit is no longer used by `compactableOk_server`: since `f4629d8be1` the proof
drops `Hpm` (`CompactEnv.lean:85`). It should be stated for every `P : Int → IProp GF`, with no
`ret` and no `hret` (`hret` is unused). `srvRevLb` is still needed, but as `E.RevLb` for
`revGetterOk` (`v3compactor/Defs.lean:105-108`): the getter must return `v ≥ n` from `□ RevLb n`.
`srvRevLb`'s certificate passed as `store.Rev.spec`'s `log₀`
(`Spec/.../mvcc/store__Rev.lean:33-41`, `log₀ <+: log`) gives this. So `srvRevLb` stays, and only
`compactableOk_server` loses it.

**T3-3 (tier 2: carried over from round 1, not addressed).**
- S3-4: `v3rpc.kvServer.Compact.spec` still lacks `traceutil.ctxTraceIs ctx none` (grep: none in
  `Spec/.../v3rpc/kvServer__Compact.lean`).
- S3-6: `v3compactor/newRevision.lean:9` still imports `Proof...traceutil.CtxLaws`.
- S3-5: `Compact.spec`'s docstring still calls `storeReaderC` "the compaction-aware reader",
  although `storeReader := storeReaderC`.

---

## T4. `mvcc.store.Compact.spec`; `crevSafe`/`delKey`/`compactJobPre` without `NoDelPutAt`

### Good
- The spec matches `store.Compact`/`updateCompactRev` at the pin (`kvstore.go:197-221,272-287`):
  `ErrCompacted` for `rev ≤ c`, with the barrier's channel; `ErrFutureRev` with a nil channel and
  `c < rev` (Go tests `rev ≤ compactMainRev` first); and a certificate showing `rev` is beyond the
  log.
- Dropping `NoDelPutAt` is supported by the fix `e7bb9f2de2`, and the translated `doCompact` has it
  (`isRecreatedAt` is in `Code/.../mvcc.lean`, with its spec and proof). The model `genAdv`
  (`mvcc/Compact.lean:79-80`) matches the fixed loop (`key_index.go:271-284`): it advances past a
  tombstone below `atRev`, or at `atRev` when the next generation is re-created at `atRev`.
  `genRecreatedAt` of an empty generation is `false`, as in Go's `isRecreatedAt`. I checked by
  hand a txn that deletes, puts and deletes `k` within one revision: `doCompact` stops at the
  second generation, keeps `(c,2)` (the tombstone), and a read at `≥ c` finds `k` absent.
  `kiGet_avail` is therefore plausible without `NoDelPutAt`. **Uncertain** until its `sorry`
  (`Compact.lean:1756`) is re-proved.

### Findings

**T4-1 (tier 2: strength margin).** The success disjunct gives `crevLb γ.idx rev` but no
certificate showing that `rev` is below the log length. A caller that needs "the compaction
revision is a revision of the log" (the C3 stage) would have to get it from the store's invariant.
No caller needs it today.

**T4-2 (tier 2: `issues/`).** `issues/etcd-compaction-delete-then-put.md` still says "Status: open
(… no fix branch yet)". The pin now carries the fix (the fork's `goose-lean-compactfix`,
`e7bb9f2de2` and `249d76bea`). Its links (#22377, #22395) need a status line.

---

## T5. `isWatchableStore`'s `crevFrozen ∨ wsUnwatched`; `wsUnwatched`

### Good
- `wsUnwatched` (`InvWatchStore.lean:1378`) takes the whole budget into an invariant. Holding a
  token next to the budget's authority (`watchBudget_spend`) then gives a contradiction, so
  `watch`'s registration is unreachable in that branch. That makes `syncWatchers`' compaction case
  vacuous, which is the intent. The extra `sorry` (`watchableStore__syncWatchers.lean:182`) should
  be easy: an unsynced watcher implies a registration, which implies a token.

### Findings

**T5-1 (tier 1; Q1). The pool and `wsUnwatched` cannot be built together.** `watchTokPool γ`
(`InvWatchStore.lean:1365`) is `inv (∃ a n, ⧗ a ∗ ownToks γ.wt n ∗ ⌜receiptBound ≤ a + n + 1⌝)`.
`New` gives exactly `2^63 − 3` tokens (`New.lean:49`), and `wsUnwatched` takes all of them, so
`n = 0` and the pool needs `⧗ a` with `a ≥ receiptBound − 1`. Receipts are distinct and below
`receiptBound` (`Perennial/GooseLang/Receipts.lean`, `receipt_lt`, `receiptBound_elim`), and
`NewServer` cannot collect `receiptBound − 1` of them: the bound is only bounded above (≤ `2^48`,
≤ `N+1`, ≤ catch-up + 1). It holds only when `receiptBound = 1`.
`NewServer.spec`'s post requires the pool in both modes:
- `srvWatchBuilt` and `srvWatchReaders` (`InvWatchBuilt.lean:44,59`);
- v3rpc's `watchSrvOk` (`v3rpc/InvWatch.lean:151`), which `Serve` builds the watch server from.

So the on case is unprovable. The decisions entry's sentence "a compacting server's token pool
then holds none" (`notes/decisions.md`, last entry) is false as a construction.

Whether a watch handler would block: no. Tokens are ghost state, and Go never blocks on them.
v3rpc's handler takes its token from the client's create request (`v3rpc/InvWatch.lean:206-223`),
and the client spends it from the pool (`watchGRPCStream__run.lean:518,1619,2718`). If the empty
pool could be built, `watchTokPool_take` would derive `False` from the receipt bound. The client's
watch proofs would then hold vacuously, as if the step budget were exhausted. That is not a stuck
thread, but it would be a vacuous proof of reachable code. The fact that the pool cannot be built
is what prevents that.

*Restatement* (one of):
- (a) The pool becomes `watchTokPool γ ∨ wsUnwatched γ` in `srvWatchBuilt`/`srvWatchReaders`/
  `watchSrvOk`. Only v3rpc passes it through, since the handler's tokens come from the client.
  `client.watchTokPool_of_server` (`client/v3/ServerWatcher.lean:116`) takes a persistent
  "compactor off" fact that `StartServer` (retention 0) hands out. That is three callers:
  `linkv3p/WatchEnv.lean:82`, `watchkv/Served.lean:98`, `cache/v3/Results.lean:269`. This is the
  watch-API premise the decision rejected, but the reach is these three sites plus
  `InvWatch.lean:432` and `InvClientNewResult.lean:47`, not "every watch example".
- (b) The watch stage: compaction in `RespM`.

(a) is the smaller change. The `srvCmpOn` fact of T1-1 can serve as the "off" fact's complement
if the two are made exclusive.

**T5-2 (tier 1; with T1-1).** `isWatchableStore`'s disjunct is chosen inside `mvcc.New`
(`newWatchableStore.lean:58`, always `crevFrozen`), and `New.spec`'s post does not return the
compaction right. *Restatement:* `New.spec` takes a ghost `cmp : Bool`. At `false` its post is
today's. At `true` its `isWatchableStore` holds `wsUnwatched` and its post gives `compactRight γ.st
(-1)` and no `watchToks`.

---

## T6. `NewServer.spec` (retention premise, the "no snapshot" justification), `NewServer.specM`

### Good
- One statement with `retention = 0 ∨ (revision ∧ 0 < retention)` (`Spec/.../NewServer.lean:147-148`)
  matches Go: a compactor exists iff `num != 0` (`server.go:383-384`), and since `a20f6760f` it
  runs in `start` (`:597-599`).
- The on case's callees (`Compact.spec`, `store.Rev.spec`, and `h31` `v3compactor.New`) are
  hypotheses and are linked. That addresses round 1's S4-2 at the statement level.

### Findings

**T6-1 (tier 1).** The on case cannot be proved: T5-1 and T5-2. `NewServer.lean:1943-1948` hides
it.

**T6-2 (tier 2: Q3, "no snapshot"). The claim is sufficient for the linked results; I verified
this by reading.** The linked apply path uses only `applySnapshot.spec`, the empty-snapshot triple
under raft's `rnApP` contract (`EtcdServer__applyAll.lean:38,237`; `Link.lean:2091`).
`applySnapshot.specSnap`, the only route to `kv.Restore` through `SnapApplyWalk`/
`restorePre_of_apply`, has no linked caller (grep). `rnApP`'s `ap.snapshot = nil` comes from raft's
no-snapshot mode, which the run bound (`receiptBound ≤ SnapshotCatchUpEntries + 1`) gives for any
member list. So round 1's uncertain point (several members) resolves as safe: Restore is
unreachable whatever `γ.vs` is.

Two caveats:
- The justification is coupled to the D22 snapshot track, which aims to lift exactly this bound.
  The compactor case will silently depend on it. *Fix:* note in D22's plan (and in the premise
  comment) that the bound is also what excludes `Restore` for a compacting server, and that
  lifting it needs the compaction ghost state redesigned (`m2-plan.md`, "Restore").
- `restorePre_of_apply`'s `crevFrozen` `sorry` (`RestorePre.lean:78-79`) is still there. It is
  unlinked, so it is outside the trust base.

**T6-3 (tier 2: one family). `specM` no longer generalizes `spec`.** `NewServer.specM`
(`NewServer.lean:297`) keeps `retention = 0`, while `spec` admits the compactor. So `spec` is no
longer `specM false`, and `wp_proof` derives the off case from `wp_proofM false` but the on case
separately. *Restatement:* `specM on` takes the same disjunction with `on = true → retention = 0`
(auth-on compaction is out of scope), so that `spec` is `specM false` again.

**T6-4 (tier 2: stale prose).** The file header (`NewServer.lean:83-86`) describes the watch store
"with the watch-token pool allocated from `mvcc.New`'s tokens". In the on case it cannot be (T5-1).

---

## T7. `newServer.spec`, `StartCompactingServer`, `putgetc`

### Good
- One `newServer.spec` with `0 ≤ retention`, and `StartCompactingServer` linked by `gen-link` again
  (the hand link in `MainLinked.lean` is gone). This is the merge round 1 asked for (S2-7, S4-2).
- The Go matches: `common.go:71-72` always sets revision mode, and the compactor is created only
  when the retention is positive.

### Findings
**T7-1 (tier 1, inherited).** Everything rests on `NewServer`'s on case (T6-1). The post
`memberBuilt … false` hands out the same watch resources in both modes, so whatever fix T5-1 gets
must reach `memberBuilt`'s watch part, or make it mode-dependent through the "off" fact.

---

## Trust base (all targets)

**TB-1 (tier 1: process).** The baselines are stale, verified textually:
- `etc/tcb-baseline.txt:733-734` and `etc/tcb-collections/m2.txt` list `sorry
  NewServer.wp_proofCompact`, which no longer exists.
- `etc/tcb-collections/server.txt` lists only `processInternalRaftRequestOnce.wp_proofCompact`.
- None of the step-2 `sorry`s appears: `NewServer.wp_proof`, `uberApplier.dispatch.wp_proof`,
  `mvcc.watchableStore.syncWatchers.wp_proof`, `mvcc.store.Compact.wp_proof`, `kiGet_avail`,
  `dispatchAnswer_notNoSpace` (two).

Because they sit inside general proofs, the `putget`, `watchkv`, `cache`, ... collections also
change. *Fix:* `etc/tcb-report.py --check --update` on the baseline and every affected collection,
after `lake build`. Also record in `notes/decisions.md`'s "M2's one family" that one family puts
the compaction `sorry`s under every existing result. That is the cost round 1's S0 "Why a
variant" avoided.

---

## Questions

1. **Can a compacting server have a zero-token pool beside `wsUnwatched`? Can a watch handler
   then block, or be unprovable?** No pool can be built: it needs `receiptBound − 1` receipts at
   construction (T5-1). So `NewServer.spec`'s on case is unprovable, not merely awkward. A watch
   handler would not block, neither in Go nor in the logic. If the pool could be built, the
   client's token take would be vacuous (`False` from the receipt bound), which is worse than
   stuck. Fix: T5-1 (a).
2. **Does `compactResultIs`'s response shape agree with `dispatchAnswer`'s compaction case?** No.
   The case gives only the error. `compactResultIs` needs the response's dynamic type
   (`v3_server.go:422`'s assertion), ownership of the response and its header (`:428`), and the
   trace on error (`:399`) (T1-2).
3. **Is "no snapshot installed" (the run bound) enough to make `Restore` unreachable for a
   compacting server?** Yes, for the linked results and for any member list. Only the
   empty-snapshot `applySnapshot.spec` is linked, under raft's no-snapshot `rnApP`. Record the
   coupling to D22 (T6-2).
4. **Is there a frozen v3compactor spec that M2's callers still cannot use?** None, as far as I can
   see.
   - `New.spec`, `revGetterOk` (through `store.Rev.spec` with `log₀` the `srvRevLb` certificate)
     and `compactableOk` (through `compactableOk_server`) can all be met.
   - The permit `P` is now unused, so `compactableOk_server` should take every `P` (T3-2).
   - Two points are **uncertain**, because the on case is a `sorry`: whether `NewServer` has a
     spare `srvLeadTimeReader`, `srvLgReader`, `E.RD` and `storeReaderC` for `E.R = srvCompactR`
     beyond the 64 of each it gives `srvServeBuilt`, and whether `□ srvRevLb E.γ 0` is available
     at construction. I expect the latter to be, from the bootstrap log's certificate.
   - The blockers are on the server's side, not the compactor's: T1-1, T5-1, T5-2.

## Ranking (most in need of revision first)

1. `NewServer.spec`'s on case together with `isWatchableStore`/`wsUnwatched` and `mvcc.New.spec`
   (T5-1, T5-2, T6-1): unprovable as stated.
2. The apply side of the one family: `dispatch.spec`/`kvOwn`/`applierTriples`, plus where the mode
   lives (T1-1), with `Compact.spec` (T3-1). Compaction is admitted on frozen stores.
3. `dispatchAnswer`'s compaction case and `specCompact` (T1-2, T2-1): they do not connect, and
   `specCompact` is checked only against a bare `sorry`.
4. Trust baselines (TB-1) and the two easy `NoSpaceDead` `sorry`s (T1-4).
5. `NewServer.specM` divergence (T6-3), the stale docstrings (T1-3, T6-4), and round 1's carried
   items (T3-3).
6. `CompactEnv`'s permit generalization (T3-2), `store.Compact.spec`'s margin (T4-1), and
   `issues/` status (T4-2).
7. `newServer`/`StartCompactingServer`/`putgetc` (T7): sound in shape, but they inherit item 1.

Verified by reading code: T1-1, T1-2, T1-3, T1-4, T2-1, T3-2, T4 (spec against Go and `genAdv`
against `doCompact`), T5-1, T5-2, T6-2 (linkage), T6-3, TB-1 (text).
Uncertain: `kiGet_avail`'s re-proof, T1-2's option (a), `NewServer`'s spare reader slots, and
whether `tcb-report --check` actually fails (not run).
No new bug in the Go code. The one relevant issue file is stale (T4-2).
