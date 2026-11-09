# Integration I5: apply, txn, lease, auth (batches 3a, 3b, 3c, 3d)

2026-11-09. Directories: `Spec/go_etcd_io/etcd/server/v3/etcdserver/{apply,txn}/`,
`Spec/go_etcd_io/etcd/server/v3/lease/` (with `leasehttp/`), `Spec/go_etcd_io/etcd/server/v3/auth/`,
`Spec/golang_org/x/crypto/bcrypt/`; snippets `examples/specreq/{apply,txn,lease,auth}/`.
Each batch was integrated by its own agent (one section per batch below); this summary gives the
result across batches.

## Build

`etc/specs-build.sh --dir` over all six directories: **OK (250 modules)** after every change below
(apply 74, txn 48, lease + leasehttp 48, auth + bcrypt 80). `cd examples && go vet
./specreq/{apply,txn,lease,auth}/...` passes; `gofmt -l` clean. (Two intermediate builds failed on
other agents' in-progress edits of `Spec/go_etcd_io/raft/v3/Model.lean` and
`etcdserver/ApiApply.lean`; both passed once those files were fixed.) Another agent's commit
`629824d06e` ("4a round-1 repairs … WIP") swept part of 3a's edits into HEAD; the rest are
uncommitted in the worktree.

## Across batches

- **3a and 3d.** 3a's provisional `authOk`/`authSt`/`authRead`/`authRecordFits`/`permReads` are
  removed or defined over 3d's API (`authStoreAt`, `authCur`, `tokFrom`, `checkPost`, `recordsFit`,
  `authReached`), through the new `nextOk`, `permReads_writer` and `permReads_reader`. After 3a's pass,
  3d added:
  - `authHook`/`hookOut` in `AdminTriple`, `AuthEnable`, `AuthDisable`, `HasRole` and `RoleList`.
    This is the post-lock hook that 4b's `authBatchTx.Lock` runs. 3a's sketches take it from `R`;
    2d supplies it.
  - `recordsFit` on `AuthDisable`, which 3a's `nextOk` covers.
  - A revision bound in `checkPost`'s pass arm: `af.enabled → ar.rev ≤ rev`.
  - `authStoreAt_agree` (3a's request (b): met).

  `rngInverted` is now W0's `KeyRange.inverted`. 3a's `checksSane` is dropped, because W0's
  `State.invertedDeny` covers the refusal.
- **Left open between 3a and 3d** (3d's answers to 3a's requests (a) and (c)):
  - **(a)** `Apply.invRefused` stays provisional.
    - Why: the cache's answer on an inverted range is `adt.Contains` on an empty interval. That
      answer depends on the tree's insertion order, so it is not a function of W0's `AuthState`.
    - What a sound exact form would need: a per-index opaque `cacheInvRefused γa jc u t rng`,
      threaded through `isRangeOpPermitted`, `checkKeyInterval` and `cacheEntry`.
    - Until then, use `invRefused` only as "the cache's answer at the writer's state".
  - **(c)** 3d's spec does not exclude a token-provider error from `Authenticate`.
    - Such errors happen: the no-op provider always fails, and JWT fails when signing fails.
    - 3a's `opStep_authenticate` assumes success.
    - **Decision for the coordinator:** either add a provider flag on `tokenProviderAt` that only
      the simple provider gives, or have `opStep_authenticate` admit the error.
- **3a and 3c.** `lessorOk`/`lessorSt` are defined over `Lease.isLessor`/`lessorState`, and
  `lessorRead` is removed.
  - New law **`Lease.isLessor_agree`**: I5 added it after 3c's pass, at 3a's request. Lease builds.
  - 3c's `beOk` is no longer persistent (4a's request). It is held in the writer's token and lent out
    by `lessorState_beOk`. `Recover` returns the old backend's `beOk`.
- **3a and 3b.** No txn name that 3a uses moved. 3b dropped the history receipt `⧖ (Mvcc.evCount …)`
  from its write updates: 3e no longer supplies it, and no caller used it.
- **Trace.** 3a's 17 uses of `EtcdServer.traceAt` are now `TraceUtil.traceOpt`. **2c can drop the
  `traceAt` alias in `etcdserver/ApiReq.lean`.**

## New finding (outside I5's directories; the coordinator should file it as a nonissue)

3d found the following mismatch.
- **The mismatch:** take a `Range`/`DeleteRange` whose `RangeEnd` is a non-`nil` empty slice. The auth
  check covers only the key (`auth/range_perm_cache.go:124`), but mvcc reads every key from it on
  (`mvcc/index.go:99,116`; W0's `EtcdWire.endOf`).
- **Reachability:** not over gRPC, which decodes an empty end to `nil`. It takes an in-process
  adapter request that carries a token.
- **Effect on proofs:** at exactly that input, it blocks the proofs of 2c's and 3a's checks, which
  need a premise or a margin there.

Details are in the 3d section.

## What I5 needs from directories it does not own

- **2c** (`etcdserver/ApiReq.lean`):
  - Drop `traceAt`.
  - `CheckTxnAuth.spec` now takes `⌜t.readonly⌝` and no lessor fact.
  - An init law for `etcdserver/errors`: its sentinel errors are `srvErrVal`.
- **2d** (`etcdserver/`, `EtcdServer__applyEntryNormal.lean`, `applySnapshot`):
  - Supply `Apply.nextOk` for each applied entry.
  - Realize `authnIdx`, `kvSt`/`kvOk` (with 3e), `statusOk`, `ciOk` and `snapSrvOk`.
  - Put `Auth.authHook` and 3c's `beHook` inside `R`.
  - After `applySnapshot`: hold `Lease.rdOk`, and close the old backend with the returned `beOk`.
  - Give `Promote` its `ckptGate le R ∗ □ R`.
  - At shutdown, take `beOk` back through `lessorState_beOk`.
  - The link from the store's index to the cluster's (3d's S1).
  - Lease 0 is never loaded: `B 0 = none` on `NewLessor`/`Recover`, from the disk image (with 2e).
- **2e**:
  - `kindOf` maps unknown alarm types to `AlarmKind.other`.
  - Specs for `SetVersion`, `SetDowngradeInfo`, `clusterVerOk` and `RaftCluster.Version` (3c's
    `clusterOk`).
  - An exact `BackendQuota.Cost`.
  - `NewServer` hands the backend to `NewAuthStore` before setting the hook (`server.go:369` vs
    `409`).
- **3e** (`storage/mvcc/`):
  - `rangeResOwn`'s context error is none of mvcc's sentinels.
  - `kvSortOk`/`kvsFit` bound a record's lease to `int64`.
  - The writer fragment for 3a's `kvSt`.
  - An init law: mvcc's sentinel errors are `srvErrVal`.
  - Settle with 4a which of `Backend.hookRun`/`Mvcc.hookRun` the apply hook uses.
- **4a** (`storage/backend/`):
  - Laws that introduce `beOk`, `beHook` and `beLeases` for the lessor.
  - A way to establish `Auth.authHook` from the server's hook.
- **3h** (`api/v3/etcdserverpb/`, `api/v3/version`):
  - A decoding predicate at the `Irr` level (`irrDecodes`, `irrMsgAt`, `reqMsgAt`).
  - For `authReqAt`, `authRespAt`, `authnRespAt`: a `HashedPassword` field fact, models of the auth
    records, and a law on the response `Header`.
  - A stringer predicate (3b's `stringerOk`).
  - A readable `V3_6` after package init.
- **2a** (grpc/v3rpc): `ctxInMD`, `ctxCertUser`, the new `ctxPeerCN`, `metadata.New`,
  `NewIncomingContext`.
- **3f** (`pkg/v3/adt`): `Contains` answers `false` for a query starting at the empty key.
- **W0**:
  - A `Perm` that is nil or of an unknown type.
  - The order of list answers.
  - `context.TODO.spec` returns `GoInterface.ok context.todoCtxVal`, so that 4b's `ctxTraceIs_todo`
    applies to the `TODO()` that 3a passes to txn.
- **Coordinator**:
  - The `Authenticate` provider-error decision above.
  - Where lease's law "the errors are `srvErrVal`" lives. Putting it in lease would make lease import
    `etcdserver/errors`.
  - The open user decisions are unchanged: 3a's (members' TTLs, `ErrNoSpace`) and 3d's (`WithRoot`
    with the simple provider, the revision race).
- **Perennial** (still open): the `2^62` slice bound of the sort specs at `Revoke`/`Leases`.

## After the batch passes (I5)

`lease/Api.lean` has a new law `isLessor_agree.spec`, listed in the header's laws. 3a asked 3c for it
after 3c's pass, so 3a's section below, which lists it as needed, is now out of date: it is **met**.
So is 3a's request (b) to 3d (`authStoreAt_agree`). Requests (a) and (c) are answered above.
## Batch 3a (`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/`, `examples/specreq/apply/`)

### Changes, by file

- `Api.lean`:
  - **`checksSane` removed**, and so is its premise in `opStep_step`, `irrStep_step` and
    `applyStep_reach`.
    - Why: W0 round 5 admits the refusal of an inverted range (`State.invertedDeny`, allowed for
      range, delete and txn; a put's ranges are single keys).
    - `Auth.rngInverted rng` (non-empty key, `keyLe end key`) implies W0's `KeyRange.inverted`.
      `opErr`'s inverted refusal applies only with auth on and a non-root user, so it is W0's
      `invertedDeny`.
  - **`opErr` reports an inverted range as the cache does.**
    - Before, it always refused an inverted range. That was unprovable: Go's
      `checkKeyInterval`/`adt.Contains` answer an empty interval deterministically but in a way
      nobody models, and 3d's `checkPost` allows either answer.
    - Now: pass iff `covers ∧ (rngInverted → ¬ invRefused a u t rng)`.
    - New opaque `invRefused`, provisional for 3d.
  - **Credentials (W0 round 5's `pwHash`).**
    - `IrrOp.userAdd`/`userChangePassword` carry the stored credential (`HashedPassword = Auth.b64
      h`).
    - `IrrOp.ok` asks that it be a hash of some password: `np = false → ∃ pw, pwHash pw h`, and
      `∃ pw, pwHash pw h`. This is what 3d's `storeNext_adm` and W0's `Reach` need.
    - `opStep_userAdd`/`opStep_userChangePassword` are restated: W0's step at any such `pw`. The old
      form put the hash in the password's place, which is false under round 5.
  - **`authRecordFits` removed** from `IrrOp.ok`. It became the next-state fact `nextOk` (below).
  - **New `nextOk γ R op S`** (transparent, persistent): every next state `σ'` of the step `S`
    satisfies `Auth.authReached γ σ'.auth ∗ ⌜Auth.recordsFit σ'.auth⌝`, plus `authnIdx R γ name tok`
    for an `authenticate` op. This is what 3d's `AdminTriple` and `Authenticate` take.
  - **New opaque `authnIdx`**, provisional for 2d: under `R`, `ConsistentIndex()` is the applying
    index `idx`, `tokenUser γ (tok.idx) name` holds, and `idx` is above the previous `tokFrom`.
  - **Options slots:**
    - `authOk`: now a def, `∃ st γa, ⌜ast = mkOk authStore st⌝ ∗ Auth.authStoreAt st γ γa`.
    - `authSt`: now a def, `∃ st γ γa i n, … authStoreAt ∗ Auth.authCur γa i a ∗ Auth.tokFrom γa n`.
    - `lessorOk`: now a def over `Lease.isLessor p γl c` with `c.minTTL = mc.minLeaseTTL`.
    - `lessorSt`: now a def over `Lease.isLessor ∗ Lease.lessorState γl n ls`. It requires
      `ls.table = lt`, `itemMap` equal to the store's lease fields, and each live object's item set
      equal to its keys.
    - Removed: `authRead`, `lessorRead`.
    - The docstrings of `kvOk`/`kvSt`/`snapSrvOk` give the intended realization.
  - **`permReads ast le u rev A L C`** (was `permReads ast le A S`):
    - It takes the auth info, a per-check report `C : Check → GoInterface → IProp`, and `L` (lease
      checks allowed).
    - Why: 3d's reader check reports three views at their own recorded states, not one state, so
      the old `S`-states shape could not express the request path's instance.
    - New `Check.isLease`.
  - `reqAdmitted (.compact rev _)` is now `rev ≠ 0` (W0's scope, which 3e's `Compact` takes).
  - `persistent.spec` updated. New header section "Integration I5".
- `ApiResult.lean`:
  - `checksOut C cs err` is over the per-check report. New `chkExact σ u rev c err` (the writer's
    exact `checkErr`).
  - **New laws:**
    - `permReads_writer.spec`: `beAt ∗ beOpts ⊢ permReads … (stAt b σ) true (chkExact σ u rev)`.
    - `permReads_reader.spec`: `Auth.authStoreAt ∗ Auth.authLb γa i0 ⊢ permReads … emp false
      (chkPost γa i0 u rev)`.
  - `opBody` of a user change: `∃ pw, pwHash pw h ∧ b = .req (.userAdd name pw np)`, and the same for
    the password change.
  - `isUber_apply`'s method triple takes `nextOk γ R ir.op (irrStep …)`.
- `checkTxnReqsPermission`, `checkTxnPermission`, `checkPutAuth`, `checkLeasePuts`,
  `checkLeasePutsKeys`:
  - They are restated over `permReads … u rev A L C` / `checksOut C`.
  - A lease check needs `⌜L = true⌝`. The transaction checks take `⌜L = false → no lease check in
    cs⌝`.
- `CheckTxnAuth.lean`:
  - New premise `⌜t.readonly⌝`: 2c's only call (`v3_server.go:355`) is for a read-only transaction.
  - `lessorRead le` dropped: a read-only transaction never calls the lessor, and a reader could only
    call it with 3c's `lessorReaders` token.
  - The sketch goes through `checkTxnPermission.spec` at `permReads_reader`. The post is unchanged:
    it is exactly `checksOut (chkPost …)`.
- `uberApplier__Apply.lean`, `uberApplier__dispatch.lean`: take `nextOk … (irrStep mc σ ir v3)`.
- `applierV3backend__{UserAdd, UserDelete, UserChangePassword, UserGrantRole, UserRevokeRole,
  RoleAdd, RoleGrantPermission, RoleRevokePermission, RoleDelete, AuthEnable, AuthDisable,
  Authenticate}.lean`:
  - They take `nextOk … (layersStep … [Layer.backend])`.
  - Their sketches are restated over 3d's `AdminTriple`: `authCur`, `authReqAt … cred`,
    `storeNext`, and `authHook γa Pre Q` from `R`.
  - `Authenticate`'s sketch is restated over `authnCtx` and `tokFrom` (`n < idx`).
- `applierV3backend__{LeaseGrant, LeaseCheckpoint, LeaseRevoke, Put}.lean`: the sketches are restated
  against 3c's current `Grant`/`Checkpoint` (`beHook`, `Mvcc.hookRun`), `Revoke` (`rdOk`), and 3b's
  `Put` (pinned `σ₀`, `txnWriter`, `leasesLive`, `evsLs`).
- **17 files**: `EtcdServer.traceAt trace` is now `TraceUtil.traceOpt trace`. These are the
  `applierV3backend`, `authApplierV3`, `quotaApplierV3`, `applierV3Capped` and `applierV3Corrupt`
  methods `Put`, `Range`, `DeleteRange`, `Txn`, `Compaction`.
  - **For the server agent (2c):** 3a no longer uses `EtcdServer.traceAt`, so
    `ApiReq.lean`'s alias can be dropped.
- `examples/specreq/apply/auth.go`: `ReqCheckTxnAuth` returns early unless `txn.IsTxnReadonly(rt)`,
  which meets the new premise.

### Provisional names

**Resolved:**
- `authOk`, `authSt`: mapped to 3d's names.
- `authRead`: removed.
- `authRecordFits`: replaced by `nextOk` over 3d's `recordsFit`/`authReached`.
- `permReads`: its instances are laws over 3d's `checkPost` and the writer's exact check.
- `lessorOk`, `lessorSt`: mapped to 3c's names.
- `lessorRead`: removed.
- `EtcdServer.traceAt`: now 4b's `traceOpt`.
- `checksSane`: dropped, because W0 covers the case.

**Left provisional, with the reason:**
- `kvOk`, `kvSt` (3e/2d): the apply thread's authority over `Mvcc.mvccState` while 2c's readers fire
  on it (3b's S6). No owner defines a writer fragment. The intended realization is in the docstring.
- `statusOk`, `ciOk`, `snapSrvOk`, `authnIdx` (2d): 2d has no consistent-indexer or status
  predicate. It has only `forceSnapW s` for `ForceSnapshot`, and `snapSrvOk`'s docstring names it.
- `irrDecodes`, `irrMsgAt`, `reqMsgAt` (3h): 3h's `EtcdServerPb.IrrBody` is coarser than `Irr`. It
  has no credential, checkpoint or membership fields, and no header id. There is no `Irr` decoding
  predicate.
- `clusterVerOk` (2e): no `SetVersion`/`MustDetectDowngrade` spec in membership.
- `invRefused` (3d, new): see the requests below.
- `opStep` stays opaque by design. Its realization is the backend's computation.

### Sketches that did not fit, and the fix

1. **Admin methods.** 3d's `AdminTriple` needs `authReached γ (storeNext …)`, `recordsFit` and
   `authHook`, and nothing in 3a's pre supplied the first two.
   - Fix: `nextOk` is threaded from `isUber_apply` down to the backend's admin methods.
   - `authHook` is recorded as `R`'s; it is 4a/2d's.
2. **`Authenticate`.** 3d needs `authnCtx` (index and prefix, with `tokenUser`) and `tokFrom` with
   `n < idx`.
   - `tokFrom` is now in `authSt`.
   - The index fact is the new provisional `authnIdx` (2d).
   - **Remaining gap:** 3d's `Authenticate` allows a provider error (`err ≠ nil`) for a user with a
     password, which is JWT signing. `opStep_authenticate` says that case is `.ok .authenticate`. 3a
     assumes the provider assigns given `authnCtx`, which the simple and no-op providers do.
     Recorded, not fixed.
3. **`opErr` on inverted ranges** was unprovable from 3d's `checkPost`: see `invRefused` above.
4. **`CheckTxnAuth` through `checkTxnPermission`**: the old `permReads`' state-set `S` could not carry
   3d's three-view reports. Fixed by the per-check `C` and `permReads_reader`.
5. **`opStep_userAdd`** was false under W0 round 5, because the hash was in the password's place.
   Restated.

### What 3a needs from directories it does not own

- **2d** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/`, `EtcdServer__applyEntryNormal.lean`):
  - Supply `Apply.nextOk γ R ir.op (fun σ' => ∃ res, irrStep mc σ ir v3 σ' res)` for each applied
    entry. This is the history point after the committed entry, `histAt`: its `etcdLb` has the same
    auth state, because `ttlEq` keeps `auth`. `Auth.recordsFit` is a scope restriction 2d must carry.
  - Realize `authnIdx R γ name tok`: `ConsistentIndex()` under `R` answers the entry's index, and
    `tokenUser γ (tok ++ "." ++ idx) name` holds from the committed `Authenticate` entry.
  - Define `kvSt`/`kvOk` (with 3e), `statusOk`, `ciOk`, and `snapSrvOk` (with `forceSnapW s` in `R`).
  - Supply `Auth.authHook γa Pre Q` for the admin steps, in `R`.
  - Supply the closure's `Lease.rdOk` after `applySnapshot`.
- **2c** (`ApiReq.lean`):
  - Drop the `traceAt` alias.
  - `CheckTxnAuth.spec` now takes `⌜t.readonly⌝` and no lessor fact. `EtcdServer.Txn`'s sketch
    calls it only for a read-only transaction.
  - `opBody` of a user change is the client's request with a password whose hash is the credential.
- **3d** (`Spec/go_etcd_io/etcd/server/v3/auth/Api.lean`):
  - (a) `checkPost`/`checkOk`/`checkDenied` should report an inverted range exactly at the cache's
    state, by a function of `ac`, for example `Apply.invRefused ac u t rng` moved to `Auth`. Today
    the nil arm with `covers` cannot tell the writer's exact answer.
  - (b) A law `authStoreAt_agree : authStoreAt st γ γa ∗ authStoreAt st γ' γa' ⊢ ⌜γ = γ' ∧ γa =
    γa'⌝`, so that `optsOk`'s `authOk` and `optsSt`'s `authSt` name the same store.
  - (c) The `Authenticate` provider-error case above.
- **3c** (`lease/Api.lean`): a law `isLessor_agree : isLessor p γ c ∗ isLessor p γ' c' ⊢ ⌜γ = γ' ∧ c =
  c'⌝`, for the same reason.
- **3h** (`etcdserverpb/Api.lean`): an `Irr`-level decoding predicate in place of `irrDecodes`, plus
  `irrMsgAt`/`reqMsgAt`. 3h's `IrrBody` lacks the credential, checkpoint, membership and header id.
- **2e**:
  - `v3alarm.kindOf` maps unknown types to W0's `AlarmKind.other n` (S2 still open).
  - Specs of `RaftCluster.SetVersion`/`SetDowngradeInfo` and `clusterVerOk`.
  - `BackendQuota.Cost` exact.
- **3e**:
  - `kvSt`'s writer fragment (with 2d), above.
  - `Compact`'s `compactChanOk` vs 3a's `Read.recvAny`: the bodies are the same per 3e's note.

### Requests

- **Addressed to 3a** (`req/go_etcd_io_etcd_server_v3_etcdserver_apply.md`):
  - **2c:**
    - Items 1-3 are met. The trace is now `traceOpt`, and `CheckTxnAuth` is over 3d's
      `checkPost`, with the read-only premise.
  - **2d:**
    - Items 1-4 are met.
    - Round 1 item 1 is superseded by round 1b (per-member configuration).
    - Round 1b items 1-2 are met: `applyStep_ttl_same`, `applyStep_reach`. `applyStep_reach` no
      longer needs `checksSane`.
  - **3c:**
    - Met in the sketches: `Grant`, `Revoke` via `rdOk`, `Checkpoint`, `Lookup`/`Keys` via
      `permReads_writer`.
    - Round 1 is met: the `rdOk` owner (2d) and `beHook`.
  - **3d:**
    - Items 1-5 are met, with round 1's changes: `AdminTriple`/`storeNext`/`authReqAt … cred`;
      `checkPost`'s old-revision arm and, now, the nil arm's revision bound match `preErr`.
    - Except: an inverted range's answer at the writer, request (a) above.
  - **3b:** the `errIs` mapping is noted. It relies on 3b's open item 3 (cross-package sentinel
    laws).
  - **3e:** `compactChanOk` is noted, and `rev ≠ 0` is now in `reqAdmitted`.
- **3a's own requests of others:**
  - **W0:** met. `noSpace` is indefinite, the stored credential is `pwHash`/`pwMatch`, and
    `etcdLb_noEmptyUser` exists. Equal grant TTLs across members was declined, and that remains a
    user decision.
  - **2c:** `waitNever`/`waitDone` are used by `Apply.spec` and met.
  - **3b:** met, per 3b's I5 report.
  - **3c:** met, per 3c's I5 report.
  - **3d:** the revision bound is met. The inverted-range report is new, as (a).
  - **3e:** see above.
  - **3h:** `irrDecodes` etc. are not met.
  - **2e:** `SetVersion`, `SetDowngradeInfo`, `kindOf` of unknown types and `Cost` exact are not met.
  - **4b:** `pbutil.MustUnmarshalMessage`, not checked further.

### Build

- `etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/etcdserver/apply`: **OK (74 modules)**.
  - This was built against the current tree, with ApiReq and 3h's `IrrBody.authToken name` as they now
    stand. `opBody` follows 3h's single-argument `authToken`.
- `cd examples && go vet ./specreq/apply/...` passes, and `gofmt -l` is clean.
- **Note:** another agent's commit `629824d06e` ("4a round-1 repairs … WIP") swept part of these
  edits into HEAD. The rest are uncommitted in the worktree.
## Batch 3b (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/`, `examples/specreq/txn/`)

### Changes, by file

- `Put.lean`, `DeleteRange.lean`, `Txn.lean`: the history receipt `⧖ (Mvcc.evCount …)` is removed from
  the first step of the caller's pinned write update (`au`). 3e's round 1 (C-F7) took it out of
  `Txn.End.contract`'s update, so txn has nothing to supply it from. That made the three write specs
  unprovable. No caller uses the receipt: there is no mention in 3a, 2c or 2d.
- `Range.lean`, `executeRange.lean`: the context-error disjunct now also gives
  `⌜rm.countOnly = false⌝`. This follows from mvcc's `rangeOut` `.ctxErr` case, which requires
  `CountOnly = false`. Without it, `Count.spec` (which has no context-error outcome) did not follow
  from `Range.spec` as its sketch claimed. The post is now stronger, so this is safe for callers.
- `Count.lean`: the sketch now says how the context-error case is excluded.
- `Api.lean`:
  - `Txn.endOf` is now `abbrev endOf sl e := EtcdWire.endOf sl e`. W0 (round 5) added the same
    function; the name is kept and the definition is shared.
  - The header records which laws are not yet provable from the callees (below).
- `checkLease.lean`: the sketch now follows 3c's round-1 lessor API:
  - `lessorState_at` gives `lessorAt γl n ls`;
  - `lessorState_reader` lends the `lessorReaders γl 1` that `Lookup` now takes;
  - the lease id goes through `putReqOwn`'s `int64` field.
- Snippets: unchanged. `go vet ./specreq/txn/...` passes and `gofmt -l` is clean.

### API changes (for 3a / 2c)

No exported name was removed or renamed. No Lean file outside `txn/` imports txn's `Api.lean`; 3a and
2c cite txn only in sketches. The visible changes:

- `Put.spec`, `DeleteRange.spec` and the writing `Txn.spec`: the caller's update now asks only
  `mvccState γ (σ₀.notify evs)` at its first step, with no receipt. The caller receives less and
  needs nothing new.
- `Range.spec`: its post is stronger.
- `endOf` is now an abbreviation of W0's.

### Provisional names

- `stringerOk` (3h): kept. 3h's batch and API have no stringer predicate yet. It is requested in
  `req/go_etcd_io_etcd_api_v3_etcdserverpb.md`, "Stringers", which is unanswered.
- The mvcc slots were already replaced in round 1. 3e's round-2 items need no change in txn:
  - `kbLocked B D0 D`, the two-step `Unlock` and `Schema.bucketAt` are internal to mvcc's storage
    rows; txn sees only `mvccBackend`, `hookIs`/`hookRun` and `KV.Write`/`Txn.End`.
  - `Mvcc.traceOwn` is now an abbrev of 4b's `TraceUtil.traceOwn`, which closes 3b's request 3.
  - The reader tokens (`mvccReaders γ 1`) were already in place.

### Sketches checked against callees as they are now

These hold as they stand:
- 3e: `KV.Read`/`KV.Write`/`Txn.Range`/`Txn.Put`/`Txn.DeleteRange`/`Txn.End`/`Rev`/`FirstRev`/`Changes`
  and `NewReadOnlyTxnWrite`.
  - `KV.Write`'s update is a peek at the pinned update: abort it and keep it, with `R σ := ⌜σ = σ₀⌝ ∗ au`.
  - `Txn.End`'s `∃∃ σ, … ⌜σ = σ₀⌝` is met by the pinned update.
  - On an error after the begin, `End` with no events is a no-op on the state, because
    `KVHist.commit [] = h`, so the update is given back.
- 4b: `EnsureTrace` against `ctxTraceOwn`/`traceBack`, and `Get`.
- 3c: `Lookup` against `checkLease`.
- W0: `Context.TODO.spec`'s `□ (ctxDone -∗ False)`, which a writing `Txn` needs; `endOf`.

These do not fit and could not be fixed on txn's side, so they are recorded:
1. **`ctxErr_not_errIs`** (needed by `Range`/`executeRange`/`deleteRange` callers and 2c's `srvIndef`).
   3e's `rangeResOwn` `.ctxErr` gives only `err ≠ nil`. Still unmet:
   `req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 3b", item 1. Needed in
   `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, `rangeResOwn`: the `.ctxErr` error is
   none of mvcc's sentinels. A fresh value, or not `ErrCompacted`'s/`ErrFutureRev`'s value, would do.
2. **`rrOwn`'s `kvFits`**, which `compareKV`, the `kvSort*.Less` specs and `sortRangeResults` use.
   3e's `kvsFit`/`kvSortOk` bound the revisions and the version, not the lease. Still unmet: same
   file, item 2. Needed in `storage/mvcc/Model.lean`: `kvSortOk` (or a reachable-state law) gives
   `-2^63 ≤ kv.lease < 2^63`.
3. **`errIs_agree`, and `errIs_ne_nil` at `.keyNotFound`.**
   - What exists: mvcc's `init` (ErrCompacted ≠ ErrFutureRev) and lease's `init` (its own four
     distinct) are each package-local.
   - What is missing: no law relates sentinels across packages, and `etcdserver/errors` has no
     initialization law for `ErrKeyNotFound`.
   - Wanted from each owner: "the variable holds 2c's `EtcdServer.srvErrVal e`". That is mvcc
     (`ErrCompacted`/`ErrFutureRev`), lease (`ErrLeaseNotFound`: 3c, the sibling) and 2c's
     `Spec/go_etcd_io/etcd/server/v3/etcdserver/errors/Api.lean` (`ErrKeyNotFound`).
   - With 2c's `srvErrOf_fun`, both laws then follow.
4. **`context.TODO()`'s trace.** 3a passes `context.TODO()`, and txn's entry points need
   `TraceUtil.ctxTraceIs ctx o`. 4b's `ctxTraceIs_todo` is stated at `GoInterface.ok
   context.todoCtxVal`, but `Context.TODO.spec` (`Spec/context/Api.lean`, W0) does not say its
   result is that value. Needed: `TODO.spec` returns `ctx = GoInterface.ok context.todoCtxVal` (and
   the same for `Background`), or 4b states `ctxTraceIs` in `TODO`'s post.

### Requests

To 3b (`req/go_etcd_io_etcd_server_v3_etcdserver_txn.md`):
- 2c items 1-3: met by `Range.spec` with `rangeOut_answers`, `Txn.spec` read-only with `run_txnRun`
  and `runEvs_readonly`, and `Count.spec`.
- 3c: met (`checkLease.spec`).
- 3a items 1-4: met by txn's specs.
  - Determinism (`putAns`, `rangeOut`, `run`), `skip` (`run_txnRun`'s last conjunct), and no panic
    given `txnSafe` and the context never done.
  - The warnings rest on `stringerOk`, provisional (3h).
  - What 3a still owes: the bridge from `Apply.reqAdmitted` to `txnSafe`/`targetOk`, and the
    composition S6, the apply thread's authority over `mvccState` (3a and 2d).

By 3b:
- 3e items 1 and 2: unmet (above).
- 3e item 3: met.
- 3e item 4: noted, no change.
- W0 `endOf`: met.
- 2c and 3a: the `errIs` mapping was sent. It depends on item 3 above.

### Build

`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/etcdserver/txn`: OK (48 modules), after another agent's in-progress `raft/v3/Model.lean` edit, which had briefly broken the shared import chain, built again
## Batch 3c (lease, leasehttp): integration I5

### Changes, by file

`Spec/go_etcd_io/etcd/server/v3/lease/`:
- `Api.lean`:
  - **new law `isLessor_ne_null.spec`** (`isLessor le γ c ⊢ ⌜le ≠ null⌝`). This is 3e's item 1: mvcc's `delete` calls `GetLease` unconditionally.
  - **`beOk` is no longer persistent** (4a's new request, `req/..._lease.md`, "from 4a"). `LockOutsideApply`/`ForceCommit` after the backend's `Close` panic. It is now an open share held in the writer's token. Its conjunct is removed from `persistent.spec`. **New law `lessorState_beOk.spec`** lends it out (for the server's shutdown, before `Backend.close`). The header and the realization were updated to match.
  - The provisional names' docstrings now give their intended realization over the owners' current vocabulary:
    - `beLeases`: 4b's `Schema.txRd`/`txWr`, `R V`, `Schema.leaseBktIs`, with `B i = (L (W64 i)).map (sint.Z ·.2.1)`.
    - `beHook`: 4a's `Backend.isBackend ∗ Backend.beHook γb discard f`.
    - `beTxHeld`: mvcc's `Mvcc.kbHeld`, which is `mvccDeleter_rdOk`'s premise.
    - `beOk`: `Backend.isBackend ∗ Backend.beOpen γb q`.
    - `clusterOk`: 2e has nothing yet.
- `lessor__Renew.lean`: **bug fixed: the reader token was lost on the error paths.** The post was `lessorReaders γ 1 ∗ (ok) ∨ (notFound) ∨ notPrimary`. `∗` binds tighter than `∨`, so the token was only in the success disjunct. The disjunction is now parenthesized. I checked every other lease post for the same pattern and found none.
- `lessor__Recover.lean`: the post also hands back the old backend's `beOk ls.be` (follows from `beOk` no longer being persistent).
- `lessor__initAndRecover.lean`: the post gives `beOk ls.be` back.
- `Lease__persistTo.lean`: takes and returns `beOk b`. 4a's `LockInsideApply` needs the open share.
- `NewLessor.lean`: the docstring says `beOk` is kept in the token. The statement is unchanged.
- Sketches restated against the current callee specs:
  - `persistTo`, `Grant`, `Checkpoint`: `Schema.MustUnsafePutLease.spec` over `txWr`, with the local struct made a message by `Schema.leaseMsg_of_struct`; the token's `beOk`.
  - `Revoke`: `Schema.UnsafeDeleteLease.spec` over `txWr`, the lock held by `beTxHeld` = `Mvcc.kbHeld`.
  - `initAndRecover`, `Recover`: `MustUnsafeGetAllLeases` gives the records "each id once, in some order" (not in id order).
  - `greaterOrEqual`: `version.LessThan.spec` is 3h's (`Spec/go_etcd_io/etcd/api/v3/version/LessThan.lean`), not 4b's.
  - `shouldPersistCheckpoints`: `V3_6` is 3h's package variable; `clusterOk` is still provisional.

`Spec/go_etcd_io/etcd/server/v3/lease/leasehttp/`:
- `Api.lean`: `rtOk` is no longer an opaque provisional. It is now `abbrev rtOk rt := Http.roundTripperOk rt` (`Spec/net/http/Api.lean`, which `rafthttp.NewRoundTripper.spec` gives). The name is kept, and `import Spec.net.http.Api` and `[sem : go.Semantics]` were added.
- `RenewHTTP.lean`: the docstring was updated to match.

Snippets (`examples/specreq/lease/`): unchanged.

### Provisional names

- **Resolved:**
  - `Leasehttp.rtOk` is now `Http.roundTripperOk`.
  - `beTxHeld` = `Mvcc.kbHeld B`. mvcc's `mvccDeleter_rdOk.spec` takes the identification `□ (kbHeld B ∗-∗ Lease.beTxHeld _)` as a premise. 4a realizes `kbHeld` as the lent session. The name stays as the lessor's vocabulary.
- **Left provisional:**
  - `beOk`, `beHook`, `beLeases`. 4a is still repairing and has no lessor-side law: nothing in `Backend/` introduces a lessor's share, hook fact or lease-bucket view. 4b's realization of `beLeases` is recorded in the docstring.
  - Also left: 4a's `hookRun` (`Backend.hookRun γ q Pk f Pre Q`, which threads `beSess`) differs from mvcc's `Mvcc.hookRun Pk f Pre Q`, which the lessor cites. 4a/3e must decide which one the apply's hook contract is. The lessor will follow mvcc's.
  - `clusterOk`: 2e's `membership/` has no `RaftCluster.Version` spec and no law into `clusterOk`.

### Sketches that did not fit, and the fix

- `Renew`'s post lost the reader token (above). Fixed in the statement.
- `persistTo`/`Grant`/`Checkpoint`/`initAndRecover`/`Recover`: 4a's `LockInsideApply`/`LockOutsideApply`/`ForceCommit` need an open share (`beOpen`), which a persistent `beOk` could not soundly give after `Close`. Fixed: `beOk` is held by the token, handed through `persistTo` and `initAndRecover`, and handed back by `Recover` and `lessorState_beOk`.
- `MustUnsafeGetAllLeases` order: the sketch no longer assumes id order (`loaded` does not depend on it; the ids are distinct).
- `greaterOrEqual`: the callee is 3h's `LessThan.spec`, not a 4b boundary.

### Requests

**Addressed to 3c (`req/go_etcd_io_etcd_server_v3_lease.md`):**
- **2c** items 1–3 are met:
  - `Lookup`, `Leases`, `Keys`, `Remaining`, `Demoted`, `Renew` answer from `lessorAt` states `≥` the bound.
  - `RenewHTTP` returns any TTL or error.
  - **2c round 1 is not met:** `lease`'s sentinels holding `EtcdServer.srvErrVal e`. `init.spec` gives only distinct non-nil values, and `errors/Api.lean` says the law is the owner's. Adding a law to `lease/Api.lean` would import `etcdserver/errors/Api` into lease (a heavier dependency; the coupling direction needs the coordinator's decision). **Open: a decision for the server/errors owner.** It could instead be stated in `errors/` as a law over `Lease.errIs`.
- **2d** items: met (`expiredCh`/`expiredCh_recv` with `c.expiry`; `Promote`/`Demote`; `Recover`; `lessorAt` as the read slot).
- **2e** items:
  - `leaseBootRes`: 3c's side is `NewLessor`'s `exp = false → leasesOutliveRun`. 2e can realize it as `ecfg.leaseExpiry = true ∨ leasesOutliveRun`.
  - `Stop` once: `lessorStop`.
- **3b** items:
  - 1 is met: `Lookup` at the writer's bound.
  - 3: `attached` is 3b's.
  - **Item 2 (lease 0 never live) is not met as a law, and cannot be one as the specs stand.** `NewLessor` and `Recover` load whatever bucket the backend holds. `initAndRecover` does not skip id 0, and nothing says the bucket lacks it. It would need a premise `B 0 = none` on `NewLessor`/`Recover`, which 2e/2d discharge from the disk image (only `Grant` writes the bucket, and it refuses 0). Left as 3b's `attached` premise. Record: a decision for 2e/2d if they can carry `B 0 = none`.
- **3a**: met (`Grant`'s three refusals and `grantTTL`; `Revoke` via `rdOk`; `Checkpoint` always `nil` with the table unchanged, since `persist` moves only `bkt`; `Lookup`/`Keys`).
- **3e**:
  - 1 is met (new `isLessor_ne_null`).
  - 2 (the method-call form) is bridged in mvcc's `mvccDeleter_rdOk` proof.
  - 3 is met by mvcc's premise.
  - 4 is met (`GetLease` with `lessorState_at`/`le`).
- **4b, 4b round 1**: met in the sketches and the `beLeases` realization (some order; `leaseMsg_of_struct`; `LessThan` is 3h's).
- **4a** (new): met (`beOk` held, not persistent; `lessorState_beOk`). Its other two points (`beApplyTok` is now `beHook` + `hookRun`; `beTxHeld` = `beSess`) are recorded in the docstrings. The `hookRun` mismatch is above.

**Requests 3c made of others, and their state:**
- **mvcc (3e)**: met (`putLs`, `delsLs`, `RestoreLs`, `mvccDeleter_rdOk`, `kbHeld`).
- **schema (4b)**: met.
- **backend (4a)**: not yet. No lessor law: `beOk` intro from `isBackend ∗ beOpen`; `beHook` from `isBackend ∗ beHook γb`; the lease bucket's view for the lessor's scope; the crash image of the lease bucket.
- **membership (2e)**: not met (`clusterOk`, `RaftCluster.Version`).
- **etcdserver (2d, "from 3c (round 1)")**: `rdOk` for `Recover`'s closure, `ckptGate`/`□ srvStarted` for `Promote`, reader tokens. Not visible in the server's current specs:
  - `EtcdServer__applyEntryNormal.lean` still describes `Promote` as needing nothing. It needs `Lease.ckptGate le R ∗ □ R`.
  - `applySnapshot` must hold `rdOk` for its closure and now also receives the old backend's `beOk`.

### What 3c needs from directories it does not own (by file and name)

- `Spec/go_etcd_io/etcd/server/v3/storage/backend/` (4a): laws introducing `Lease.beOk`, `Lease.beHook`, `Lease.beLeases` for a backend (or the backend's own names, to replace them), and the choice between `Backend.hookRun` and `Mvcc.hookRun`.
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/` (2e): a spec of `RaftCluster.Version` and a law `isCluster c … ⊢ Lease.clusterOk (iface c)`.
- `Spec/go_etcd_io/etcd/api/v3/version/` (3h): `V3_6`'s value readable after `isPkgInit` (an init law), for `shouldPersistCheckpoints`.
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/` (2d):
  - `EtcdServer.applyEntryNormal.spec` provides `ckptGate le R ∗ □ R` to `Promote`.
  - `applySnapshot` keeps `rdOk` of the closure and closes the old backend with the returned `beOk ls.be`.
  - The shutdown takes `beOk` through `lessorState_beOk`.
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/errors/` (2c): the `srvErrVal` law for lease's sentinels (see above).
- Still open from round 1: the `2^62` bound of Perennial's sort at `Revoke` and `Leases`.

### API changes (for 3a, 3b, 3e, 2d, 2e)

- Added: `isLessor_ne_null.spec`, `lessorState_beOk.spec`.
- `beOk` is not persistent (removed from `persistent.spec`). Its only users are inside lease, but 2e's `NewServer` gives it once and the shutdown must take it back.
- `lessor.Recover.spec`'s post adds `beOk ls.be`.
- `lessor.Renew.spec`'s post keeps the reader token on every outcome (strictly stronger).
- `Lease.persistTo.spec` and `lessor.initAndRecover.spec` (internal) thread `beOk`.
- `Leasehttp.rtOk` is now an `abbrev` of `Http.roundTripperOk` and needs `[go.Semantics]`.

No name was renamed or removed.

### Build

- `etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/lease Spec/go_etcd_io/etcd/server/v3/lease/leasehttp`: OK (48 modules).
- The importers of `lease/Api.lean` (`Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api`, `...etcdserver.txn.Api`, `...etcdserver.apply.checkLeasePutsKeys`): OK (3 modules).
- `go vet ./specreq/lease/...` and `gofmt -l`: clean.
- Before that, the build was blocked for a while by another agent's work-in-progress `Spec/go_etcd_io/raft/v3/Model.lean`, which had a docstring before an `export`. It is now fixed.
## 3d (auth store, bcrypt)

Build: `etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/auth Spec/golang_org/x/crypto/bcrypt`:
OK (80 modules). `Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Api` (3a's, imports auth's Api)
still builds after the changes (OK). Snippets: `go vet ./specreq/auth/...` and `gofmt -l` clean.

### Changed, by file

- `auth/Api.lean`
  - `rngInverted` is now `abbrev rngInverted r := r.inverted` (W0's `KeyRange.inverted`). The old
    body was `key ≠ [] ∧ keyLe end key` with a proper end. That is the same set of ranges: a proper
    end is never `≤ []`. The name stays for 3a's `opErr`/`checksSane`.
  - `validPerms` is now over W0's `KeyRange.validPerm`. The meaning is unchanged.
  - **New `authHook γa Pre Q`** (opaque, one use; provisional for 4a/2d): the backend's post-lock
    hook takes `Pre` to `Q`.
  - **New `hookOut γa Pre Q`**: `Q ∨ (Pre ∗ authHook γa Pre Q)`.
  - **`AdminTriple`** keeps its signature. Its `∀` now binds `Pre Q`; the pre adds
    `Pre ∗ authHook γa Pre Q` and the post adds `hookOut γa Pre Q`.
  - **`checkPost`'s pass arm** adds `af.enabled = true → ar.rev ≤ uint.nat rev` (3a's round-1
    item 5). The docstring says what this does not give (below).
  - **New `ctxPeerCN ctx c`** (provisional, 2a): the TLS peer's common name, whatever the incoming
    metadata.
  - **New law `errOf_srvErrVal.spec`**: `ae.etcd = some e → errOf ae = EtcdServer.srvErrVal e`
    (2c's round-1 item 3). For this, Api now imports `etcdserver/errors/Api`.
  - Docstrings:
    - `recordsFit` is 3d's own, with its realization over 4b's `Schema.putFits`.
    - `authBackendAt` is 3d's own, since 4b declined the slot. Its realization is over 4b's
      `authEnabledOf`, `authRevOf`, `recsWf`, `retOk`, `rdSect`, `wrSect`, `txRd`, `txRange`, `txWr`.
    - `ctxInMD`: still 2a's. 2a has `rpcCtx`/`rpcCtx_vals` but no law yet.
    - `authReqAt`, `authRespAt`, `authnRespAt` are marked provisional for 3h, with their intended
      realization over `Proto.msgAt` + `reqHolds`/`bodyHolds`.
    - The header now lists the vocabulary used from W0.
- `authStore__AuthEnable.lean`, `authStore__HasRole.lean`: add `Pre ∗ authHook γa Pre Q`.
  - AuthEnable's post is `hookOut`.
  - HasRole's post is `Q`: it always locks.
- `authStore__AuthDisable.lean`: the same `Pre ∗ authHook γa Pre Q`, plus the premise
  `⌜recordsFit (storeNext .authDisable [] a)⌝`. Its sketch calls `commitRevision`, whose spec
  requires `recordsFit` of the next state (the bumped revision must fit the atomic).
- `authStore__WithRoot.lean`: the TLS clause changes.
  - It was `□ (ctxCertUser ctx none -∗ ctxCertUser ctx' none)`. That is **false** for a context with
    a TLS peer but no incoming metadata (or a gateway request): there `ctxCertUser` is `none`, and
    `NewIncomingContext` adds metadata without `grpcgateway-accept`, so `ctx'` gets the peer's CN.
  - It is now `□ (∀ c, ctxPeerCN ctx c -∗ ctxCertUser ctx' c)`.
- `authStore__IsRangePermitted.lean`, `authStore__IsDeleteRangePermitted.lean`: Margin adds the
  empty-range-end mismatch (finding below).
- Sketches fixed:
  - `authStore__UserGet`, `authStore__Authenticate`: `GetUser` is a read-transaction section, not
    the batch transaction.
  - `authStore__RoleList`: `GetAllRoles` uses the batch lock, so the hook runs.
  - `authStore__UserList`: 4b's `entsAny` order; no lock.
  - `authStore__RoleGet`: no lock.
  - `NewAuthStore`: the hook is not set yet at that call (`server.go:369` vs `409`).
  - `checkKeyInterval`: the gap in 3f's `Contains` spec (below).
- `bcrypt/GenerateFromPassword.lean`: the Users list now says `selectPassword`'s plain-password path
  is out of scope.
- `examples/specreq/auth/{admin,check}.go`: the writer's Assumes now include the post-lock hook.

### Provisional names

Resolved:
- `rngInverted` is now W0's `KeyRange.inverted`.
- `validPerms` is over W0's `validPerm`.
- `authBackendAt` is no longer provisional: 3d owns it (4b's answer).
- `recordsFit`'s bbolt half is 4b's `putFits`.
- W0's round-5/6 renames were already used: `pwHash`/`pwMatch`, `permittedSince`, `invertedDeny`,
  `tokenUser_agree`.

Left provisional, with why:
- `ctxInMD`, `ctxCertUser`, new `ctxPeerCN` (2a): 2a's `FromIncomingContext.spec`/`peer.FromContext.spec`
  cover only a run's context (`rpcCtx`). There is no any-context or no-metadata form, no law
  `rpcCtx ⊢ ctxInMD (some md)`, and no `metadata.New`/`NewIncomingContext` spec.
- `authReqAt`, `authRespAt`, `authnRespAt` (3h): 3h has `reqHolds`/`bodyHolds`, but no fact about
  the `HashedPassword` field (`b64 cred`), no `authpb` record models, and no `Header` field law.
- `recordsFit` stays opaque: 3h has no `authpb` record contents to state it over.
- `b64` (no `encoding/base64` boundary exists).
- `jwtTokOk` (the JWT boundary / 2d's `tokenUser` realization).
- `authHook` (new; 4a/2d).

### Sketches that did not fit, and the fix

1. **The post-lock hook** (4b's `authBatchTx.Lock` needs `callOk tx "LockInsideApply" P Q ∗ P`).
   - The admin methods, `AuthEnable`, `AuthDisable`, `HasRole` and `RoleList` (`GetAllRoles`) lock
     the batch transaction with `LockInsideApply`, which runs the server's hook. Their specs took no
     pre for it.
   - Fixed by `authHook`/`hookOut`, as 3c did with `beHook`/`Mvcc.hookRun`.
   - `NewAuthStore` runs before the hook is set; this is recorded in its sketch for 2e and 4a.
2. **`AuthDisable`** lacked the `recordsFit` that `commitRevision.spec` needs. Added.
3. **`WithRoot`'s TLS clause** was false (above). Restated.
4. **`checkKeyInterval`** (3f's `intervalTree.Contains.spec` is exact only under `affLt b e`).
   - With the empty key (the affine top) and a proper or open end, `b = true → covers` needs
     `Contains` to answer `false`. Go does: `Visit` meets nothing.
   - 3f's spec does not say so. This was requested in `req/go_etcd_io_etcd_pkg_v3_adt.md`, "from
     3d", item 3, and is still open. The spec is kept, and the sketch notes the dependency.
5. **`UserGet`/`Authenticate`** cited the batch transaction; `GetUser` is the read transaction.
   This was a wording fix only: between writer calls every view is at `a`.

### `checkPost` and 3a's revision-bound request

- What 3d now gives: on a pass with auth on, the store's revision atomic read at `jr ≥ i0` is at
  most the `AuthInfo`'s revision (`ar.rev ≤ uint.nat rev`).
- What it does **not** give: `jx`, `jc` (the backend and the cache) are not bounded above by `jr`.
  The revision is read before them, and a change may land in between.
- Consequence for 3a: one state for all of a request path's passing checks is not derivable. The Go
  race is `nonissues/etcd-auth-revision-before-visible.md`; W0's `permittedSince` admits it for reads.
- For the writer, every view is at `a` (`authCur_at`, `authAt_le`), so its checks are exact.

### Finding (to be filed as a nonissue: outside my directories)

- The auth check of a range with a **non-`nil` empty `RangeEnd`** checks the key alone.
  `isRangeOpPermitted` tests `len(rangeEnd) == 0` and calls `checkKeyPoint`
  (`auth/range_perm_cache.go:124`).
- mvcc reads the same request as every key from `key` on. `treeIndex.Revisions` tests
  `end == nil`, and `unsafeVisit`'s bound is skipped for an empty end
  (`storage/mvcc/index.go:99,116`; W0's `EtcdWire.endOf`).
- So a `Range`/`DeleteRange` carrying `RangeEnd = []byte{}` is checked for one key and reads or
  deletes the suffix.
- Not over gRPC: proto3 drops empty bytes, so the request decodes to `nil`, and so does the apply
  entry. It needs an in-process adapter request (`WithRange("")` through `v3client`) whose context
  carries a token.
- Code reading only; blocks-proof: yes for 2c/3a. Their request ranges (`endOf`) differ from the
  check's range (`{key, e}` raw) exactly there. They need a premise (a non-`nil` empty end does not
  reach the auth checks) or a margin.
- 3d's specs state the code's behavior (`rangeEnd := e`), noted in the Margin of `IsRangePermitted`
  and `IsDeleteRangePermitted`.

### API changes (for 3a and the other callers)

- `AdminTriple` (all 13 admin specs), `AuthEnable.spec`, `AuthDisable.spec`, `HasRole.spec`: the
  caller supplies `Pre ∗ authHook γa Pre Q`. It gets back `hookOut γa Pre Q`; HasRole gives `Q`.
- `AuthDisable.spec` takes `⌜recordsFit (storeNext .authDisable [] a)⌝`.
- `checkPost`'s pass arm is stronger: the added conjunct is a post, so callers are unaffected.
- `WithRoot.spec`'s TLS clause is over `ctxPeerCN`. The callers (2d's lessor, health checks) use
  `s.ctx` or HTTP contexts, which have no peer (`ctxPeerCN ctx none`, 2a's).
- New names: `authHook`, `hookOut`, `ctxPeerCN`, `errOf_srvErrVal.spec`. `rngInverted` is now an
  `abbrev` of W0's (3a's `Api.lean` builds).
- Nothing was renamed or removed.

### What I need from directories I don't own

- **3a** (`apply/`):
  - thread `Pre ∗ authHook γa Pre Q` into every auth-store writer call (`applierV3backend.Auth*`,
    `User*`, `Role*`; `authApplierV3.RoleGet`'s `HasRole`);
  - supply `recordsFit` for `AuthDisable`;
  - replace `authOk`/`authSt`/`authRead`/`authRecordFits`/`permReads` by `authStoreAt`/`authCur`/
    `authLb`/`recordsFit`/`checkPost` (`req/…_etcdserver_apply.md`, "from 3d");
  - `checksSane` can now say `¬ rng.inverted` (it is W0's).
- **4a/2d**: an intro law for `Auth.authHook` from the server's hook (4a's
  `beHook`/`hookRun` of the backend the store holds, after `Recover` the snapshot backend's hook,
  `server.go:1098`).
- **2e**: `NewServer` hands `authBackendAt` over before setting the hook (`server.go:369` before
  `409`).
- **2a** (`Spec/google_golang_org/grpc/`, `req/google_golang_org_grpc.md`, "from 3d"):
  - `ctxInMD` for any context (`none` without incoming metadata), and
    `rpcCtx ctx md ⊢ Auth.ctxInMD ctx (some md)`;
  - `ctxCertUser`, `ctxPeerCN` (with `ctxPeerCN ctx none` for contexts without a peer);
  - specs of `metadata.New` and `metadata.NewIncomingContext` (peer kept).
- **3h** (`etcdserverpb/Api.lean`):
  - `authReqAt`'s `HashedPassword` field;
  - the `authpb` record contents (for `recordsFit`, and 4b's `userName`/`roleName`);
  - the auth responses' `Header` field law.
- **3f** (`adt/intervalTree__Contains.lean`): `Contains` of a query whose begin is the affine top
  answers `false`, or `Contains` exact for `IvlS.queryOk` as its docstring claims.
- **W0** (open from 3d's round 1, unchanged): `roleGrantPermission` with a nil or unknown-typed
  `Perm`; the list answer orders.
- **2d**: the store-index to cluster-index link (round-1 S1, its round-1 item 1: `srvReadAt` to
  `authLb`); `waiterOk` only from `start` (2d's item 2).
- **coordinator**: file the empty-range-end nonissue above.

### Requests addressed to 3d: status

- 2b items 1-3: met.
- 2c items 1-4: met. 2c round 1:
  - item 1 is 2c's realization;
  - item 2 is met except that a prefix or `assign` error returns `ctx`, which the code allows;
  - item 3 is met by the new `errOf_srvErrVal`.
- 2b round 1 (TLS principal): the store side is `AuthInfoFromTLS`; the principal's definition is
  2a's/W0's.
- 2e items: `authBootRes` is 2e's slot; `Close` needs only the handle.
- 2d round 1: item 1 depends on 2d's link; item 2 is 2d's.
- 3a items 1-4 and round 1 item 5: item 5 is met as far as the code allows (above).
- 4b and 4b round 1:
  - `authBackendAt` is 3d's own;
  - the hook's pre is now the caller's (`authHook`);
  - `putFits` is in `recordsFit`'s realization;
  - `entsAny` is accepted (responses are permutations).

### 3a's follow-up requests (after its fork finished)

1. **`Apply.invRefused`: an inverted range's refusal, exactly at the cache's state.** Not met, and
   recorded here.
   - The refusal comes from `Contains` of an empty interval. Its answer depends on the interval
     tree's shape, and the shape depends on the order the store inserted the permissions in: the
     store's sorted lists, re-sorted by an unstable sort on key.
   - W0's `AuthState` keeps the lists only up to permutation. So "the cache built from `a` refuses"
     is not known to be a function of `a`, and a 3d name over `a` alone could be false.
   - A sound exact report would be per recorded index: an opaque `cacheInvRefused γa jc u t rng`
     in `checkPost`.
   - The cost is the internal chain: `isRangeOpPermitted`, `checkKeyInterval` and `cacheEntry`
     would have to carry the index. That is not cheap, so it is left for a later round.
   - Meanwhile 3a's `invRefused` stays provisional. Its writer use is sound only if 3a takes it as
     the cache's answer at the writer's state, not as a function of `a`.
2. **`authStoreAt_agree`: met.** A new law in `auth/Api.lean`:
   `authStoreAt st γ γa ∗ authStoreAt st γ' γa' ⊢ ⌜γ = γ' ∧ γa = γa'⌝`. Built: auth 80 modules OK,
   `apply.Api` OK.
3. **`Authenticate`'s provider error: not excluded**, because the spec is generic over the
   provider (`tokenProviderAt`/`tpOpen`).
   - Simple provider: its `assign` succeeds from an `authnCtx`.
   - No-op provider: `assign` always fails with `ErrAuthFailed`.
   - JWT: `assign` can fail when signing.
   - Excluding the error needs a provider flag on `tokenProviderAt`, like `rt` for root tokens:
     say `aok`, "assign succeeds from an `authnCtx`", given only by `simple_provider`. Then
     `Authenticate.spec` could drop the error disjunct when `aok`.
   - The alternative is for 3a's `opStep_authenticate` to admit a provider error (the honest
     model for nop and JWT).
   - Not done here: it touches the bundle's laws and `NewAuthStore`/`NewTokenProvider`. A decision
     for 3a or the coordinator.
- Not renamed: `checkPost`, `AdminTriple`, `storeNext`, `recordsFit`, `authReached`. 3a's
  `nextOk`/`permReads_writer`/`permReads_reader` rest on them.
