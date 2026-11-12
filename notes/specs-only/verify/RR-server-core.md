# RR-server-core: second re-review of the server core (2c, 2d, boot)

Reviewer: fresh, independent (`reverify-brief.md`), 2026-11-09, at `41c6c3a39f` (branch `specs-only`),
diffed against `4a6a9b6b6e`. Read-only apart from this file. Go: `.lake/src/server` (`S/` below).
I wrote my verdicts on R-A7's N1-N5 before reading `repair-server-core.md` ("Re-review"); I read it
afterwards only to check where we disagree (on N5, below).

Scope: the top-level files of `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/` plus `read/`, `errors/`,
`cindex/`; `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/{wait,idutil,notify,schedule}/`; and the snippets in
`examples/specreq/{etcdserverreq,etcdserverapply,etcdserverboot,cindex,schedule,wait}`.

Out of scope, as the brief says, so not reviewed here:
- the crash laws in `ApiBoot.lean`;
- `Txn`'s read-only path and the stringer depth premise. Other agents are editing these files now
  (`EtcdServer__Txn.lean` and `EtcdServer__Range.lean` are modified in the worktree).

## Verdicts

| batch | verdict | new first-tier |
|---|---|---|
| **2c** request path (`ApiReq`, `v3_server.go`, `read/`, `errors/`, `pkg/{wait,idutil,notify}`) | **PASS WITH OPEN DECISIONS** (5.1 `histPropose` budget, C45 `GoAttach` token shape, C47 `reqCtxOk` at the entries, §6 F2 `WithRoot`'s `rootTokOk`/tracing) | none |
| **2d** apply side (`ApiApply`, `server.go` apply side, `raft.go`, `snapshot_merge.go`, `cindex/`, `pkg/schedule`) | **FAIL** | RR1 (the apply-side callers of `srvNode_member` hold no `srvStarted`), RR2 (`Process`, `NewServer` and `NewUberApplier` call getters before `srvMember` exists) |
| **boot** (`ApiBoot`, `EtcdServer__Start`, `etcdserverboot` snippets) | **FAIL** | RR3 (`start.spec` has no `threadTok` and no `srvMember`, and the compactor's `Run` keeps a token, so `Start`'s returned token cannot be proved), RR4 (`NewServer.spec` takes no `threadTok`) |

`go vet` is clean on all six snippet packages.

## The R-A7 first-tier findings

| # | finding | status | evidence at `HEAD` |
|---|---|---|---|
| N1 | the compactor's contract asks for `Compact` at `rev = 0` | **resolved** | See [N1](#n1). |
| N2 | no `Rev` right for `KV().Rev()` | **resolved** (second-tier header gaps) | See [N2](#n2). |
| N3 | `createMergedSnapshotMessage` and `newSnapshotReaderCloser` consume the apply thread's `threadTok` | **resolved** | See [N3](#n3). |
| N4 | `Start` consumes the caller's only `threadTok` | **resolved in the statement; the proof does not close** | See [N4](#n4) and RR3. |
| N5 | `srvNode_member` cannot be realized | **resolved differently, incompletely** | See [N5](#n5) and RR1, RR2. |

<a id="n1"></a>**N1: resolved.**
- **The contract now asks for a positive revision.** `compactable_intro` takes `⌜0 < rev⌝`
  (`api/v3compactor/Api.lean:134`).
- **`Compact.spec` can be applied.** It takes `rev : w64` with `rev ≠ W64 0`. You instantiate it at
  `W64 rev`, and `compactReqOwn_unfold` (`api/v3/Wire.lean:477-482`) gives the `int64` range.
- **`revGetter_intro`'s post now says `1 ≤ sint.Z n`.** The store's `KV.Rev.contract`
  (`mvcc/Api.lean:342-347`) returns `W64 σ.rev`. That is at least 1 by definition:
  - `σ.rev = σ.kv.rev = revs.length + 1` (`api/v3/Model.lean:164`);
  - `mvccState_reachable` gives `σ.rev + 1 < 2^63`, so it has no sign issue.
- **Both loops meet the contract.**
  - `Revision` skips `rev <= 0` (`S/etcdserver/api/v3compactor/revision.go:82`).
  - `Periodic` compacts `pc.revs[0]`, a value `Rev()` returned (`periodic.go:110,126`).
- **The snippet's fake meets it.** `fakeRev` returns 100.

<a id="n2"></a>**N2: resolved.**
- **The token is now exported.** `srvWatchable_mvcc` (`ApiReq.lean:366-367`) gives
  `∃ γs, watchableAt w γs ∗ mvccRevTok γs`.
- **It is realizable.** `NewServer` takes the persistent token from `mvccRevTok_of`
  (`NewServer.lean:85-88`), and `w = s.kv` is never reassigned.
- **`ReqReadAfterWrite` closes.**
  1. `readReg_register` (with a ticket `Q := ⌜Reach σput σ⌝`, from the put's `etcdLb`) supplies
     `committedLb l0`.
  2. `LinearizableReadNotify` returns `l` with `opsOf l0 <+: opsOf l` and `srvApplied l.length`.
  3. `srvApplied_read` gives `srvReadAt`.
  4. `srvWatchable_hist` gives `srvMvcc` at the same `γs`.
  5. `srvReadAt_mvcc`'s AU gives the AU of `KV.Rev.contract` at `rt = true` (`watchableAt_isMvcc`).
  6. At its `histAt γ k' σ`, with `k' ≥ l.length`, you apply `readReg_get`.
- **Second tier.**
  - The snippet header (`etcdserverreq/read.go:19-23`) still says the `Rev` step is "assumed of 3e,
    not checked against its statement here". That is stale: it closes as above.
  - The header does not cite `etcdLb_reach`, which the ticket's AU needs.

<a id="n3"></a>**N3: resolved.**
- **Both posts return `threadTok`.** See `EtcdServer__createMergedSnapshotMessage.lean:71` and
  `newSnapshotReaderCloser.lean:52`.
- **The new premise is met.** `createMergedSnapshotMessage` gained `srvStarted`, which its caller
  `applyAll` holds (it is persistent).
- **`applyAll`'s `msgSnapC` arm now closes** (`S/etcdserver/server.go:1011-1013`). `sendMergedSnap`
  takes `srvStarted` and `threadTok`, and returns `threadTok`.

<a id="n4"></a>**N4: resolved in the statement; the proof does not close.**
- **The statement.** `Start.spec`'s post now returns `threadTok` (`EtcdServer__Start.lean:54`).
  Each `GoAttach` returns the caller's token, as C45 requires.
- **The snippets.** `ReqStartThree` and `ReqRestart` close against the statement.
- **Why the proof does not close.** `Start` calls `start()`, and `start.spec` cannot be proved as
  stated (RR3).
- **Second tier.** `Start`'s sketch (lines 9-12) still says "the caller's one token for the read
  loop, the others from the pool … that `srvBuilt`'s realization keeps". That is the old `GoAttach`
  shape.

<a id="n5"></a>**N5: resolved differently, and incompletely.**
- **What changed.** The bridge is now `srvNode ∗ srvStarted ⊢ srvMember` (`ApiApply.lean:621-623`).
  That is realizable (fix (b) of R-A7).
- **What the repair report claims.** It says "Its users (the apply side, `ensureLeadership`, the read
  environment) hold `srvStarted`" (`repair-server-core.md`, "Re-review").
- **Why that is false.** Four apply-side specs do not hold it, plus the spec that calls two of them
  (RR1). Nor can any caller before `start` hold it (RR2). Fix (a) of R-A7 would have covered both
  cases.

## New first-tier findings

### RR1. Five apply-side specs call `srvMember`'s methods but hold no `srvStarted`

- **The missing premise.** These specs take `srvNode` and `applyThread`/`applyAt`, but not
  `srvStarted`:
  - `EtcdServer.applySnapshot.spec`;
  - `EtcdServer.applyConfChange.spec`;
  - `EtcdServer.snapshotIfNeededAndCompactRaftLog.spec`;
  - `EtcdServer.snapshot.spec`;
  - `EtcdServer.compactRaftLog.spec`.
- **No law gives it.** `applyThread` is opaque, and no law gives `srvStarted` or `srvMember` from
  it (`ApiApply.lean:330-336, 888, 916`).
- **What the Go code needs.**
  - `applySnapshot` calls `s.Logger()` (`S/etcdserver/server.go:1027`), which needs `srvMember` and
    `threadTok`. It also reads `s.r.transport` (`server.go:1157,1166`), which only `srvMember`'s
    realization holds (`ApiBoot.lean:108`).
  - `applyConfChange` calls `s.Logger()` (`server.go:2033`) and reads the transport
    (`server.go:2075,2085,2101`).
  - `snapshot` calls the logger at `server.go:2109,2111`.
  - `compactRaftLog` calls it at `server.go:2163`.
  - `snapshotIfNeededAndCompactRaftLog` calls `snapshot` and `compactRaftLog` (`server.go:1247-1248`).
- **The sketches are stale.** Each of these sketches says "The `srvMember` that `Logger` takes comes
  from `srvNode_member`". That premise is now unmet.
- **Why it is a regression.** It was introduced by the N5 repair, which changed the bridge's premise
  but not its users.
- **Who is affected:**
  - K6's snapshot install (snippet `ReqInstallSnapshot`);
  - every membership change being applied;
  - the apply thread's snapshot and compaction (`applyAll` → `snapshotIfNeeded…`).
- **Fix.** Add `srvStarted s γ id` to these five specs' preconditions. Their callers hold it, and it
  is persistent:
  - `applyAll` holds it, for `applySnapshot` and `snapshotIfNeeded…`;
  - `apply` holds it, for `applyConfChange`;
  - `snapshotIfNeeded…` would then hold it, for `snapshot` and `compactRaftLog`.

  An alternative is to have `applyThread`'s realization carry `srvStarted`, with a law. The first
  fix is more local.

### RR2. `Process`, `NewServer` and `NewUberApplier` call getters before `srvMember` (or `isServer`) exists

- **`Process`.** `Process.spec` takes `srvNode` only (`EtcdServer__Process.lean`). It must, because
  rafthttp may call it from `tr.Start()` on (`server.go:424`). That is before
  `srv.r.transport = tr` (`server.go:438`) and before `start`.
  - Its body calls `s.Logger()` (`server.go:701`) and `s.MemberID()` (`server.go:705,710`). Their
    specs (`EtcdServer__Logger.lean:39`, `EtcdServer__MemberID.lean:38`) take `srvMember`.
  - `srvMember` is now unreachable from `srvNode` without `srvStarted`. Before the N5 repair, the
    unrealizable bridge had hidden this.
- **`NewServer`** calls getters before it builds `srvMember` in its post:
  - `srv.Logger()` at `server.go:343`, `363` and `366` (twice);
  - `srv.FeatureEnabled(...)` at `server.go:387`, whose spec takes `srvMember ∗ threadTok`.

  Its sketch does not mention them (`NewServer.lean:14-40`).
- **`NewUberApplier`** calls `s.KV()` (`server.go:1184`). `KV.spec` takes `isServer`
  (`EtcdServer__KV.lean`). But its two users, `NewServer` (step 6) and `applySnapshot`, call it
  before `start` or without `isServer`. Its sketch says only "read the fields (`srvNode`)".
- **Who is affected:**
  - rafthttp's inbound path (2f, through `srvNode_raftOk`);
  - every `NewServer` (all boot snippets);
  - `applySnapshot`.
- **Fix: R-A7's option (a).**
  - Add a persistent `srvFields s γ id` for the fields the server literal sets: `lgMu`/`lg`,
    `memberID`, `Cfg`, `cluster` (`server.go:313-331`).
  - Add laws `srvNode ⊢ srvFields` and `srvMember ⊢ srvFields`.
  - State `Logger`, `MemberID`, `Config`, `FeatureEnabled`, `RequestTimeout`, `Cluster` and
    `ClusterVersion` over `srvFields`.
  - Keep `srvMember` (which holds the transport) for `CutPeer`, `MendPeer`, `PauseSending`,
    `ResumeSending` and `RaftHandler`.
  - For `KV()`, give `KV.spec` a persistent field premise, `s.kv ↦□ w`. Both `isServer` (via
    `srvWatchable`) and `srvStores_kv` supply it. The spec returns `w`, and leaves `srvWatchable` to
    a law from `isServer`.

### RR3. `start.spec` takes no `threadTok` and no `srvMember`, and the compactor's `Run` keeps a token

- **The spec.** `EtcdServer.start.spec` (`EtcdServer__start.lean`) takes
  `isPkgInit ∗ srvBuilt` only. `srvBuilt`'s stated realization (`ApiBoot.lean:110-115`) has neither
  `srvMember` nor thread tokens.
- **What the body does.** `start()` calls:
  - `s.Logger()` (`server.go:548`), which needs `srvMember ∗ threadTok`;
  - `s.ClusterVersion()` (`server.go:575`, `srvMember ∗ threadTok`);
  - `s.MemberID()` and `s.Cluster()` (`srvMember`);
  - `s.compactor.Run()` (`server.go:596`).
- **`Run` keeps the token.** `isCompactor_methods`' `Run` WP takes `threadTok` and has post `True`
  (`api/v3compactor/Api.lean:152-155`, `Periodic__Run.lean`). So a compacting server's `start`
  spends a token, and `Start.spec` (N4's fix) cannot return the caller's.
- **The Go code needs no transfer.** Both loops are forked goroutines (`periodic.go:105`,
  `revision.go:67`), and each gets its own token from the fork (`wp_fork_tok_body`).
- **Who is affected:** every `Start`:
  - `ReqStartOne`, `ReqStartThree`, `ReqRestart` and `ReqJoin`;
  - the compacting starters of `examples/lib/etcdstart`.
- **Fix.**
  - `start.spec` takes `srvMember s γ id ∗ threadTok` and returns `threadTok`.
  - `Start.spec` takes `srvMember` too (callers have it from `NewServer`'s post), or add a law
    `srvBuilt ⊢ srvMember`.
  - `Run`'s WP (in `isCompactor_methods`, `Periodic.Run.spec` and `Revision.Run.spec`) returns
    `threadTok`. Those files are A8's; the requirement is the boot batch's.
  - Update `Start`'s sketch to the C45 accounting.

### RR4. `NewServer.spec` takes no `threadTok`

- **The spec.** `NewServer.spec`'s precondition (`NewServer.lean:141-150`) has no `threadTok`.
- **What it calls that needs one:**
  - `lease.NewLessor`, whose precondition takes `threadTok` and whose post does not return it
    (`lease/NewLessor.lean:76`; the sketch says so at `NewServer.lean:104`);
  - `srv.Logger()` and `srv.FeatureEnabled` (RR2);
  - `NewUberApplier` (`EtcdServer__NewUberApplier.lean:52`);
  - `restoreAlarms`, the transport's `Start` and others.
- **History.** This predates `4a6a9b6b6e` (the statement is unchanged), and R-A7 did not record it.
  `NewServer` is arguably server-boot's file (A8); I record it here because every `etcdserverboot`
  snippet rests on it.
- **Fix.**
  - `NewServer.spec` takes and returns the caller's `threadTok`.
  - The lessor's run loop takes the token of its own fork. Either `NewLessor` returns the caller's
    token (`go l.runLoop()`, `lessor.go:245`), or `NewServer` takes a second token, kept in
    `srvBuilt` until `Cleanup`.

## Regressions: what closes

Spec files changed in scope since `4a6a9b6b6e`:
- `ApiApply`, `ApiReq`;
- `Range`, `RangeStream`, `Txn` (the `endsDecoded` removal only);
- `Start`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser`, `revokeExpiredLeases` (prose),
  `NewServer` (prose).

`read/`, `errors/`, `cindex/` and `pkg/v3/{wait,idutil,notify,schedule}` are unchanged, and R-A7's
verdict on them stands.

- **`srvStores_kv`** (the new `srvCurBe` and the whole `lessorSt`) is plausible. `s.lessor ↦□ le` is
  set once, before the apply thread runs (`server.go:343`). `srvCurBe` is the apply thread's half of
  `s.be`, with `bemu`'s invariant holding the other half.
  - **Second tier.** The law's closing wand returns `srvStores` only at the same `be` and `σ`. So
    `applySnapshot`, which moves to `newbe` and the snapshot's state, rebuilds `srvStores` from the
    internal realization, not from this law. That is fine for an internal predicate, but the
    docstring's "lent out and back" should say so.
- **`applyLent_opts`'s prose** (`idx ≥ 1`, `tok` free of `.`) adds no statement. The facts are
  requested of 3a; plausible (`GenTokenPrefix`, letters only).
- **`Range`, `RangeStream`, `Txn`: the `endsDecoded` removal.** `reqOwn_realize`
  (`api/v3/etcdserverpb/Realize.lean:80`) carries `endsOk c` inside the owned predicate, so the
  auth check's need is still met. I did not check `Txn`'s read-only path (out of scope).
- **`compactable_intro`'s comment** still says "its `isServer` and gate share from `R`"
  (`api/v3compactor/Api.lean:126`). `Compact` takes no gate at `phys = false`. This is stale prose,
  second tier, and was already noted by R-A7.

**Snippets.** Only `etcdserverreq/read.go` changed, and it closes (N2).
- `ReqStartThree` and `ReqRestart` close against `Start.spec` as stated, but they inherit RR3/RR4
  through their callees' proofs.
- `ReqInstallSnapshot` and `ReqMergedSnapshot` (apply side) inherit RR1.

## Bugs in the Go code

None found.

## Counts

- **R-A7 first-tier findings rechecked:** 5.
  - Resolved: 3 (N1, N2, N3).
  - Resolved in the statement but not provable: 1 (N4, see RR3).
  - Resolved differently but incompletely: 1 (N5, see RR1 and RR2).
- **New first-tier findings:** 4.
  - RR1 is a regression from the N5 repair.
  - RR2 was hidden until now by the unrealizable bridge.
  - RR3 goes with N4.
  - RR4 predates `4a6a9b6b6e`.
- **Second-tier findings:** 5.
  - `ReqReadAfterWrite`'s header (stale caveat; no `etcdLb_reach`).
  - `Start`'s sketch.
  - `srvStores_kv`'s "lent out and back".
  - `compactable_intro`'s comment.
  - The apply-side sketches citing `srvNode_member`.
- **Spec files re-read:** 13 changed, plus about 25 unchanged callers and callees checked against
  them.
- **Snippet packages vetted:** 6, all clean.
