# A9 (apply, txn, lease, auth, bcrypt): provability review

Reviewer: independent provability agent, 2026-11-09, at `1aa6fc1337`. Scope: batches 3a
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/`), 3b (`.../etcdserver/txn/`), 3c
(`Spec/go_etcd_io/etcd/server/v3/lease/`, `lease/leasehttp/`), 3d (`Spec/go_etcd_io/etcd/server/v3/auth/`,
`Spec/golang_org/x/crypto/bcrypt/`); snippets `examples/specreq/{apply,txn,lease,auth}/`. Target: an
applied client request is exactly W0's `Step` (`Spec/go_etcd_io/etcd/api/v3/Model.lean:1296`) in every
mode. Go sources: `/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261107170612-a4d2bb1720b9`
(below `S/`).

I wrote the findings before reading `batch-*.md`/`integration-*.md`/`open-questions.md`; afterwards I
checked each finding against them, and say so where one is already recorded.

## Verdicts

| batch | verdict | why |
|---|---|---|
| 3a apply | **FAIL** | F1 (a spec false of the code: `Txn` panics under its premise), F2 (no source for `leasesLive` and the range deleter's contract), F3 (no source for the lessor's and auth store's hook contracts), F4 (`opStep_step` too weak: `ReqApplyWrite` cannot be proved), F5 (minor: the `authInfo` mutex invariant) |
| 3b txn | **PASS WITH OPEN GAPS** | Every triple closes against 3e/3c/4b as stated. Three laws are not provable from the callees as they are; the batch records them itself (`txn/Api.lean:73`), and they are owed by 3e and `etcdserver/errors`, not by a user decision. Every snippet closes |
| 3c lease | **PASS WITH OPEN GAPS** | The specs I checked close against the code. The provisional backend slots (`beOk`, `beHook`, `beHookRun`, `beLeases`, `beTxHeld`) and `clusterOk` still have no introduction laws in 4a/2e (recorded, `integration-I5.md:559`). The snippets close; one cites a stale name |
| 3d auth | **PASS WITH OPEN DECISIONS** | Closes, except that `Apply.invRefused`/`checkPost`'s report on an inverted range is pending (open question 3.12). `recordsFit`, `authReqAt` and `b64` are provisional (3h) |
| 3d bcrypt | **PASS** | Two trust-boundary triples, true of x/crypto v0.57.0 |

The target ("exactly W0's `Step`") holds at the level of the model laws, with one exception (F4).
`irrStep_step`, `opStep_step`, `applyStep_reach`, `irrStep_alarm`, `irrStep_env`, `irrStep_quiet`,
`irrStep_noV3`, `irrStep_oldRev` and `irrStep_read` are all plausible from `irrStep`'s definition and
the backend's realization: I checked every gate case against `S/etcdserver/apply/{auth,corrupt,capped,quota,backend,uber_applier}.go`
(below). F4 is that the bridge's conclusion is all of `Step`, refusals included, so a client cannot
learn that a valid write was **not** refused.

## First-tier findings

**F1. `applierV3backend.Txn.spec` (and through it `uberApplier.Apply.spec`, `isUber_apply`) is false
of the code: its premise admits a transaction that panics.**
- Premise: `op.ok` (`applierV3backend__Txn.lean:42`). For a txn, `op.ok` is `txnAdmitted t`
  (`apply/Api.lean:535`): `t.valid` and `putOnce` of every run. `putOnce` counts only puts.
- The body calls `txn.Txn` (`S/etcdserver/apply/backend.go:62-64`), whose spec requires
  `⌜txnSafe t⌝` (`txn/Txn.lean:79`, `txn/Api.lean:446`): no ignore-put after a delete that covers its
  key.
- Counterexample: `Then: [Delete k, Put k IgnoreValue]` with `k` present.
  - It is `t.valid`, and `putOnce` holds (one put), so `op.ok` holds.
  - `checkTxn` reads the pre-transaction view and passes.
  - `executeTxn` deletes `k`, then `getPrevKV` reads the in-transaction store (empty), and `put`
    indexes `prevKV.KVs[0]` (`S/etcdserver/txn/put.go:55`): an index panic.
  - This is `issues/etcd-txn-delete-then-ignore-put.md`. The fork's `checkIntervals` refuses the
    transaction at the gRPC layer, but the apply's premise does not record that.
- The batch records the gap as owed ("the bridge from `Apply.reqAdmitted` to `txnSafe`/`targetOk`",
  `integration-I5.md:470`). It is still open at HEAD.
- Fix: add `Txn.txnSafe t` to `txnAdmitted`. The server gets it from `txnChecked` through 2c's
  `txnChecked_safe` (`ApiReq.lean:186`). `targetOk` already follows from `t.valid`'s `validSort`.
- Related (uncertain): I found no law that gives `txnAdmitted`'s `t.valid ∧ putOnce` from 2c's
  `irrWf`/`txnChecked`. The server needs one to supply `ir.op.ok`.

**F2. No premise supplies `leasesLive`, `ls.rd ≠ nil` or `Lease.rdOk` to the backend applier; the
backend `Put`, `Txn` and `LeaseRevoke` proofs need all three.**
- `txn.Put.spec` and `txn.Txn.spec` require `leasesLive σ₀.kv.store ls` (`Put.lean:75`,
  `Txn.lean:82`): mvcc's `Attach` of a dead lease panics.
- `lessor.Revoke.spec` requires `ls.rd ≠ func.nil ∗ rdOk γ ls.rd n ls P D Q`
  (`lease/lessor__Revoke.lean`).
- `applierV3backend__Put.lean:9` says `leasesLive` comes from `lessorSt`. But `lessorSt`
  (`apply/Api.lean:666`) only says:
  - `ls.table = lt`;
  - `items` are the store's lease fields;
  - each live lease's key set is its items.

  Nothing in it says that a key's lease is live.
- `applierV3backend__LeaseRevoke.lean:6` puts `rdOk` "inside `stAt`" (also `Api.lean:664`). But
  `stAt`'s realization is `optsSt`'s content, which has neither fact.
  - `NewUberApplier.spec` builds `smAt` (and so `stAt`) from `optsOk ∗ optsSt` alone, so it cannot
    establish either.
  - `reachable σ` is in no triple's premise, only in the laws.
- Fix:
  - add `∀ k r, s k = some r → r.lease = 0 ∨ lt r.lease ≠ none` to `lessorSt` (true of every
    reachable state; the boot and `applySnapshot` callers discharge it);
  - add to `optsSt` the deleter facts: `ls.rd ≠ nil`, and `□ ∀ n ls P…, rdOk …` built from 3e's
    `mvccDeleter_rdOk` or 2d's closure.
- The rdOk half is recorded as 2d's to supply (`integration-I5.md:310`), but 3a's slots give it no
  place. The `leasesLive` half is not recorded.

**F3. The hook contracts for lessor and auth writes have no source in 3a's statements.**
- What needs a hook:
  - `lessor.Grant.spec` and `lessor.Checkpoint.spec` take `beHook ls.be Pk f ∗ Pre ∗ beHookRun ls.be Pk f Pre Q ∗ (Q ={⊤}=∗ Pk ∗ Post)`;
  - every 3d `AdminTriple` (and `HasRole`, `RoleList`) takes `Auth.authHook γa Pre Q`.
- The sketches (`applierV3backend__LeaseGrant.lean:7`, `__AuthEnable.lean:10`, and so on) say these
  come "from `R`". But:
  - `R` is universally quantified in every backend triple;
  - `lessorOk` and `authOk` are transparent and mention no hook (`Api.lean:658,675`);
  - `optsOk` (`Api.lean:735`) carries `R` only through `kvOk`, `snapSrvOk` and `ciOk`;
  - nothing ties `ls.be` to the backend whose hook `kvOk` covers.

  So the backend's `LeaseGrant`, `LeaseCheckpoint` and all twelve admin methods cannot close for an
  arbitrary `R`.
- Recorded as 2d's/4a's to supply (`integration-I5.md:118,285,309`), but 3a has no slot for it.
- Fix: a provisional slot in `optsOk`, e.g. `hooksOk o R`: under `R`, the lessor's `beHook`/`beHookRun`
  for `o.Lessor`'s backend and `Auth.authHook` for `o.AuthStore`, each given back with `R`.

**F4. `opStep_step`/`irrStep_step` conclude all of `Step`, refusal disjunct included, so no client
can rule out a refusal. Snippet `apply/ReqApplyWrite` fails.**
- `Step` (`Model.lean:1296`) admits `σ' = σ ∧ res = .err e` for any `EtcdErr.refusal` error
  (`requestTooLarge`, `tooManyRequests`, ...) at every state.
- `opStep` is opaque. Its other laws (`opStep_fun`, `_total`, `_noOldRev`, `_read`, `_ttl`) do not pin
  a put's answer.
- So `ReqApplyWrite` (auth off, no alarm, a valid put, a live lease) cannot prove its
  `panic("write: a valid put refused")` unreachable: `opStep` may answer `.err .requestTooLarge`.
- Fix: state `opStep_step` with the operation's own step, `kvStep ∨ leaseStep ∨ authStep ∨
  clusterStep` (W0's `Step` without its refusal disjunct). This is true of the backend:
  - its errors are mvcc's, the lessor's and the auth store's, all inside those relations;
  - the backend applier makes no refusal of its own.

  `irrStep_step` then follows, and so does a client's "not refused". For a put at auth off,
  `kvStep` pins `res` given `p.check`.

**F5 (minor). `aiAt`'s stated realization is too weak for a header-less request.**
- `Api.lean:110-111` and `authApplierV3__Apply.lean:6` give the mutex invariant as
  `∃ ai, aa.authInfo ↦ ai`.
- With `ir.hdr = none` (which `irrDecodes` admits), Go keeps the field as it is
  (`S/etcdserver/apply/auth.go:46-51`), while the spec passes `aiAt aa ir.user ir.revW = aiAt aa "" 0`
  to `applyFunc`.
- Fix: realize the invariant as `aa.authInfo ↦ ("", 0)`. It holds because every path resets the
  field before unlocking (`auth.go:54-55,60-61`). Alternatively, have `IrrOp.ok`/`Irr` require a
  header.

## Proof plans (every spec file)

### 3a apply (72 specs, 35 laws)

**The chain, the model.**
- `uberApplier.Apply`: `smAt_unfold` gives `uberChain p (chainLayers σ) ∗ stAt b σ`.
  - Then `v.Apply(r, v3, a.dispatch)`. The corrupt and capped appliers embed and promote `Apply`
    down to `authApplierV3.Apply`.
  - The mutex gives `aiAt` (F5); `needAdminPermission.spec`; 3d's `IsAdminPermitted` at the writer's
    exact state (`authCur_at`, `authAt_le`) answers `adminErr σ.auth ir.user`.
  - On a refusal: `&Result{Err}`, which is `irrStep`'s first case.
  - Otherwise: `quotaApplierV3`'s promoted `Apply`, then `applierV3backend.Apply.spec` (calls `af`),
    then `dispatch.spec`.
  - The post's `ar = null` clause holds: `dispatch` returns `nil` past the membership switch without
    `v3` (`uber_applier.go:126-128`).
  - This closes given F1, F2, F3 and F5.
- `dispatch`:
  - The membership switch: the backend's `ClusterVersionSet` (`semver.MustParse`: `clusterVerOk`;
    `ForceSnapshot` under `snapSrvOk R`), `ClusterMemberAttrSet` (`memberUpd`'s AU:
    `UpdateAttributes` panics on an unknown member), `DowngradeInfoSet`, and the test request.
  - Then each kind's chain method, through the layer specs, giving `layersStep` at `chainLayers σ`.
  - Alarms go through `uberApplier.Alarm.spec`, which calls `restoreAlarms`, giving
    `uberChain p (chainLayers σ')`.
  - The `default` panic is excluded by `irrDecodes` ("exactly one field").
  - The deferred warnings need `msgOpt ar.Resp`. That has to come from 2c's `irrReply` through
    `replyAt_result`. **Uncertain**: I did not find the depth fact there.
- Layer methods (`applierV3Corrupt.*` ×7, `applierV3Capped.{Put,Txn,LeaseGrant}`,
  `authApplierV3.{Put,Range,DeleteRange,Txn,LeaseRevoke,UserGet,RoleGet}`,
  `quotaApplierV3.{Put,Txn,LeaseGrant}`): one line each, against Go.
  - corrupt: return `ErrCorrupt` (`corrupt.go`); `corruptRefused` matches the seven overrides exactly.
  - capped: `Put`, `LeaseGrant` give `ErrNoSpace`. `Txn` uses `a.q.Cost(r) > 0`: a zero
    `BackendQuota` struct, and `Cost` reads no field (`S/storage/quota.go:136-173`). It is positive
    iff a branch has a put (`costPut ≥ 256`), which is `cappedRefused`.
  - auth: `checkPutAuth`/`IsRangePermitted`/`IsDeleteRangePermitted`/`CheckTxnAuth` through
    `permReads_writer` (`chkExact`, `checkErr`), then the base.
    - The orders match `authErr`: a standalone delete is checked write then read; a delete inside a
      txn read then write (`auth.go:104-112,165-173`).
    - `UserGet`/`RoleGet`: `IsAdminPermitted` and `HasRole` (`auth.go:222-242`).
  - quota: `Available`, then the base. `ErrNoSpace` after a success is `resMatch`'s third disjunct.
- Backend methods, one line each:
  - `Put`, `DeleteRange`, `Range` (`withTotalCount` true), `Txn`: 3b's specs with `context.TODO()`.
    `Put` and `Txn` need F2 (and `Txn` F1).
  - `Compaction`: 3e's `Compact`, then `KV.Range` at the current revision, which cannot fail
    (`rev ≥ compactMainRev`), so `rr.Rev` is safe (`backend.go:66-81`).
  - `LeaseGrant`: `lessor.Grant` with the id nonzero (`reqAdmitted`), `grantTTL`, `l.TTL()` (needs
    F3).
  - `LeaseRevoke`: `lessor.Revoke` (needs F2).
  - `LeaseCheckpoint`: `Checkpoint` per entry, always `nil` (needs F3). The model answers `noAns`
    while Go returns a non-`nil` `LeaseCheckpointResponse`. **Uncertain** whether 2c's
    `applyResult` accepts a non-`nil` `Resp` for `.noop`.
  - `Alarm`: the alarm store; `Activate` of a raised alarm returns the existing member, still
    `[al]`; an unknown action is `nil, nil`, which is `noAns`.
  - `AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`, `UserChangePassword`, `UserGrantRole`,
    `UserRevokeRole`, `RoleAdd`, `RoleDelete`, `RoleGrantPermission`, `RoleRevokePermission`: 3d's
    `AdminTriple` with `nextOk` (`authReached`, `recordsFit`) and `authHook` (F3); `newHeader`.
  - `UserGet`, `UserList`, `RoleGet`, `RoleList`, `AuthStatus`: 3d's readers at the writer's state.
  - `Authenticate`: `ConsistentIndex()` under `ciOk R`, `authnIdx`, 3d's `Authenticate` with `tokFrom`
    (`authSt`).
  - `newHeader`: `statusOk`, `isCluster`, `kvOk`'s `Rev`.
- Constructors and helpers: `NewUberApplier`, `newApplierV3`, `newApplierV3Backend`,
  `newAuthApplierV3`, `newQuotaApplierV3` (`NewBackendQuota` with `beReadable`), `newApplierV3Capped`,
  `newApplierV3Corrupt`, `restoreAlarms`, `uberApplier.Alarm`, `needAdminPermission`, `noSideEffect`.
  All are allocation or pure dispatch on the message's fields (3h's `irrMsgAt`). They close, except
  that `NewUberApplier` cannot build the `stAt` that F2 needs.
- `Apply` (`apply.go`):
  - `MustUnmarshalMessage` (`irrDecodes`); the id via `hasId`.
  - `w.IsRegistered` (2c's `list.IsRegistered.spec` with `waitWasReg ∨ waitNever`); the wrapper's
    `sk`.
  - The interface call through the caller's method triple (`isUber_apply`), or `nil` with `P`. Closes.
- Permission helpers: `CheckTxnAuth`, `checkTxnPermission`, `checkTxnReqsPermission`, `checkPutAuth`,
  `checkLeasePuts`, `checkLeasePutsKeys`.
  - Each check goes through `permReads` (an internal bundle of triples; its realization is the
    per-check triples) and gives `checksOut C`.
  - `checkLeasePutsKeys`'s `leaseObj` comes from `Lookup`'s `lessorAt` and `lessorAt_obj`.
  - Recursion through nested transactions needs the split laws `endsDecoded rt → opsDecoded`
    (branches) and nested `endsDecoded`. Those are requested and do not exist yet
    (`apply/Api.lean` `opsDecoded` docstring; `integration-I5.md:88`), so the recursive step does not
    close today. A recorded W0/3h gap.

**The model laws (pure).** Every case of `irrStep_step` is checked against Go:
- **Admin refusals.** `adminErr` vs W0's `adminErr who`: `u = ""` with a nonzero revision gives
  `ErrUserEmpty`, where W0 says `userNotFound`. But `userEmpty` is a refusal, so it is still a `Step`.
- **Per-check refusals:**
  - `preErr`'s `userEmpty`/`authOldRevision` are refusals;
  - `permissionDenied` corresponds to `¬ permits ∨ invertedDeny`, using `reachable` (no user `""`,
    no key on a dead lease);
  - `leaseErr`'s administrator shortcut is the same as `isRoot`.
- **Operations:**
  - put: `invalid`, `permits`, `check`, `record`;
  - range: `v = σ.kv` is `IsView` of itself;
  - txn: `TxnRun`'s first error is `checkTxn`'s in order, because each check reads only `s0`; the
    revision is `runRev`;
  - compaction: `rev ≠ 0` (`reqAdmitted`); W0's `compacted = 0` vs Go's `compactMainRev = -1` agree
    for `rev ≠ 0`; the admin clause holds at `j = 0` because `authTables[0]` is the initial,
    auth-off state of every reachable `σ`;
  - grant: `id' = id`, `ttl' = max ttl minTTL`, within `(0, MaxLeaseTTL]` by `mc.ok`;
  - revoke: `commit []` is the identity when the lease has no keys, as mvcc's empty `End` is;
  - the admin methods: `storeNext` vs `authStep`, case by case against `S/auth/store.go:270-860`.

The derived laws (`irrStep_fun`, `applyStep_fun`, `applyStep_total`, `irrStep_read`, `_quiet`,
`_noV3`, `_oldRev`, `_alarm`, `_env`, `_ttl`, `applyStep_ttl_same`, `applyStep_reach`) follow from
`irrStep`'s definition and the `opStep_*` laws.
- None is vacuous.
- `opStep_*` are plausible of the backend's computation.
- With `lo := 0`, W0's admin and permission clauses are trivially met through `authTables[0]` (auth
  off). So `irrStep_step` constrains reads and compactions less than a caller's `lo` would. That is
  W0's choice, not a defect of 3a.

The resource laws (`persistent`, `smAt_timeless`, `smAt_excl`, `smAt_unfold`, `smAt_optsSt`,
`smAt_alarms`, `uberOpts_persistent`, `aiAt_excl`, `reqMsgAt_endsDecoded`, `replyAt_result`,
`permReads_writer`, `permReads_reader`, `isUber_apply`) are plausible from the stated realizations.
But `permReads_writer`'s `chkExact` needs `stAt`'s auth view to be the writer's (it is: `authSt`), and
`isUber_apply` inherits F1.

### 3b txn (47 specs, 12 laws)

- `Range`: `EnsureTrace`; `Read` (3e) fires the update; `executeRange` (`viewErr`/`viewStore` at
  `.read σ`); `End`. `targetOk` excludes `sortRangeResults`' `lg.Panic` (`range.go:158`). Closes.
- `Count`: `Range` count-only (no context error). Closes.
- `executeRange`: mvcc's `Range`, then `filterRangeResults`, `sortRangeResults` (`goSort`) and
  `asembleRangeResponse`; this is `rangeOut`. The sort's `Less` subtractions cannot overflow because
  all values are below `2^63` (`kvFits`).
- `Put`: `checkLease` (`Lookup` at the writer, with a reader token from `lessorState_reader`), then
  `Write`, `checkAndGetPrevKV`, `put` (premises from `checkLease` and `leasesLive`), and `End` (3e's
  two steps). Closes against 3e/3c as stated.
- `DeleteRange` / `deleteRange`: `mkGteRange`; the optional `PrevKv` range (a context error is
  possible); `DeleteRange` (`delsLs`). Closes.
- `Txn`: `IsTxnReadonly`, `Read`, `compareToPath`, `checkTxn`; then, for a write, `End` + `Write`, or
  `NewReadOnlyTxnWrite`; then `txn`. The ignore-put premise of `executeTxn` comes from `opsSafe`
  across the branch's deletes. Closes, given `txnSafe`; the defect is 3a's (F1).
- `txn`, `executeTxn`, `checkTxn`, `compareToPath`, `applyCompares`, `applyCompare`, `compareKV`,
  `compareInt64`, `newTxnResp`, `checkPut`, `checkLease`, `checkRange`, `checkAndGetPrevKV`,
  `getPrevKV`, `put`:
  - each mirrors its Go function (`txn.go:81-336`, `put.go`, `range.go:186-196`);
  - the response tree's path offsets match `respSkel`/`txnPathOf`;
  - `applyCompare`'s `rv.Range` cannot fail at the current revision.
- `filterRangeResults`, `pruneKVs`, `sortRangeResults`, `asembleRangeResponse`, `rangeLimit`,
  `mkGteRange`, `isNil`, the `kvSort*` methods, `IsDefaultOrdering`, `HasRevisionFilters`,
  `IsTxnReadonly`, `IsTxnSerializable`: one-line pure or array specs. They close.
- `Warn*`, `warnOfExpensiveGenericRequest`, `ApplySecObserve`, `RangeSecObserve`: logging, over
  `stringerOk` (provisional, 3h) and `msgOpt`. They close.
- Laws: `goSort_sorted` (needs a functional model of pdqsort: a Perennial change, recorded),
  `rangeAll_eq`, `rangeOut_answers`, `run_txnRun`, `runEvs_readonly`, `attached_evsLs` are
  plausible. The batch records three as not provable from callees as they stand: `ctxErr_not_errIs`,
  `errIs_agree`/`errIs_ne_nil` at `.keyNotFound`, and `rrOwn`'s `kvFits` (`txn/Api.lean:73-80`).
  These are open gaps owed by 3e and `etcdserver/errors`.

### 3c lease (44 specs incl. `leasehttp`, 21 laws)

Checked against `S/lease/lessor.go`:
- `Grant` (`:281`): `id = 0` gives `ErrLeaseNotFound`; `ttl > Max` gives `ErrLeaseTTLTooLarge`;
  `ErrLeaseExists`; the minimum TTL raise; `persistTo` under the hook. Closes, with the hook from the
  caller.
- `Revoke` (`:326`, quoted above): absent gives `ErrLeaseNotFound` with `rd` not called; the `rd()`
  transaction, sorted `Keys`, a `DeleteRange` per key; then `delete` and `UnsafeDeleteLease` inside
  the deleter's transaction (`beTxHeld`); `End` under `le.mu`. Closes from `rdOk`.
- `Lookup`, `Leases`, `unsafeLeases`, `GetLease`, `Attach`, `Detach`, `Checkpoint`,
  `shouldPersistCheckpoints`, `greaterOrEqual`, `Promote`, `Demote`, `SetRangeDeleter`,
  `SetCheckpointer`, `Recover`, `initAndRecover`, `ExpiredLeasesC`, `Stop`, `isPrimary`,
  `clearScheduledLeasesCheckpoints`, `clearLeaseExpiredNotifier`, `scheduleCheckpointIfNeeded`,
  `NewLessor`, `NewLease`, the `Lease` methods (`TTL`, `Keys`, `Remaining`, `Demoted`, `refresh`,
  `forever`, `getRemainingTTL`, `persistTo`), `LeaseQueue`'s and `leasesByExpiry`'s heap methods,
  `LeaseExpiredNotifier`, `newLeaseExpiredNotifier`:
  - each is a lock-protected step of `LessorState`, or a heap or array method;
  - the time-based parts are unmodelled, as the header says.
  - I checked `Grant`, `Revoke`, `Renew`, `Lookup` and `Checkpoint` line by line, and skimmed the
    rest; **uncertain** on the heap-index arithmetic of `LeaseQueue.Push`/`Swap`.
- `Renew` is assumed (names only). Its three outcomes match `lessor.go:396-456` (the checkpointer
  through `ckptOk`: `nil` or `ErrNotPrimary`).
- `leasehttp.RenewHTTP` is assumed; it returns for any input (no `nil` dereference on its path).
- Laws: plausible from the realization (a `mono_list` history, ghost var). `lessorAt_minTTL` holds
  because only `grant` and `loaded` set TTLs. `leaseObj_id`'s `int64` bounds come from the `ID`
  field's type.

### 3d auth (75 specs, 52 laws) and bcrypt (2)

- The `AdminTriple` methods (`UserAdd`, `UserDelete`, `UserChangePassword`, `UserGrantRole`,
  `UserRevokeRole`, `RoleAdd`, `RoleDelete`, `RoleGrantPermission`, `RoleRevokePermission`,
  `AuthEnable`, `AuthDisable`): `storeNext` matches each Go method (`S/auth/store.go:270-860`) case by
  case.
  - Root-only checks with auth on.
  - `UserChangePassword` keeps a password-less user.
  - `RoleGrantPermission`'s `ErrPermissionNotGiven`/`ErrInvalidAuthMgmt` come before the role lookup;
    W0 allows them at any state.
  - `RoleAdd` does not refresh the permission cache, which is harmless: the new role has no
    permission.
  - `storeNext_adm` is plausible. Its admStep is non-vacuous at reachable states: with auth on, root
    holds the root role, because nothing can remove it while on.
- Readers: `isOpPermitted` and the `Is*Permitted` methods give `checkPost` (`store.go:862-913`).
  - The order matches: flag, revision zero, revision stale, user at the backend, root, cache.
  - A missing user is reported as `checkDenied` with `jc := jx`.
- `IsAdminPermitted` gives `adminPost`. `HasRole`, `IsAuthEnabled`, `Revision`, `AuthInfoFromCtx`
  (`ctxInMD`'s "every key has a value" excludes `ts[0]` on an empty list), `AuthInfoFromTLS`,
  `WithRoot`, `Authenticate` (`tokFrom` n→idx), `CheckPassword` (`CompareHashAndPassword`), `Recover`,
  `NewAuthStore` (`normRev`), `Close`, `BcryptCost`, `GenTokenPrefix`, `selectPassword`,
  `commitRevision`, `setRevision`, `refreshRangePermCache`, `lockedReadTx`, `setupMetricsReporter`,
  `authInfoFromToken`: they close against the code, over the provisional `authBackendAt`,
  `authReqAt` and `authHook`.
- Range-permission helpers (`checkKeyInterval`, `checkKeyPoint`, `isRangeOpPermitted`,
  `getMergedPerms`, `isValidPermissionRange`, `isOpenEnded`): mirror `range_perm_cache.go`.
  `isValidPermissionRange` corresponds to `validPerm`. The unknown permission type's `lg.Panic` is
  excluded because `PermType` has three values.
- Token providers (`tokenSimple.*`, `tokenNop.*`, `simpleTokenTTLKeeper.*`, `newTokenProvider*`,
  `NewTokenProvider`, `decomposeOpts`, `hasRootRole`, `redactToken`, `permSlice.*`):
  `assignSimpleTokenToUser`'s duplicate panic is excluded by `tokFrom`. Close.
- bcrypt:
  - `GenerateFromPassword` (over 72 bytes refused; cost clamped or refused; `crypto/rand` never
    fails);
  - `CompareHashAndPassword` (`nil ↔ pwMatch`, by definition).

  Both are true of v0.57.0.

## Snippets (56)

| package | count | result |
|---|---|---|
| apply | 8 | 6 close; **`ReqApplyWrite` fails (F4)**; `ReqCorrupt` closes once its `Assumes` adds "a valid range" (`reqAdmitted` needs `key ≠ [] ∧ validSort`) |
| txn | 18 | all close (examples: `ReqApplyTxnSkip` via `execOp`'s skipped range at `h.rev+1` after the put; `ReqRangeStreamPages` via `pushdownLimit = 3` and the successor key `last ++ "\x00"`; `ReqRangeSortedKeysOnly` via `fastKeysOnly`, then filter, then `goSort_sorted` descending) |
| lease | 14 | all close; `ReqGrantHook`'s `Specs:` line cites `Mvcc.hookRun`, now `Lease.beHookRun` (stale name) |
| auth | 16 | all close (`ReqWriterCheck`: the writer's views all at `i` by `authAt_le`; `ReqAdminSteps`: the error disjuncts of `roleGrantPermission` are excluded because `storeNext` bumps the revision) |

Other apply snippets:
- `ReqApplyReplay`: `isUber_apply`'s `v3 = false → … → ar = null`.
- `ReqNoSpaceCapped`: activation, then `chainLayers` gains `capped`, then `.noSpace` (assuming no
  CORRUPT alarm).
- `ReqStaleRevision`: `putChecks`' first `.op`, then `preErr`, then `authOldRevision`.
- `ReqCheckTxnAuth`: `checkPost`'s four errors.
- `ReqNewUber`: `isUber_apply`'s `ua = ok ui`, so it is non-`nil`.

## Counts

- Specs checked: 240.
  - 72 (3a) + 47 (3b) + 44 (3c) + 75 (3d) + 2 (bcrypt).
  - Closing as stated: 3a 72 − 19 (`Put`, `Txn`, `LeaseGrant`, `LeaseCheckpoint`, `LeaseRevoke`, the
    12 admin methods, `NewUberApplier`, `authApplierV3.Apply`) = 53. The rest close.
  - The nested-txn recursion of the `check*` helpers waits on the requested split laws.
- Laws checked: 120 (35 + 12 + 21 + 52). Plausible: all but 3b's three self-declared open ones.
  None vacuous.
- Snippets checked: 56. 54 close; `ReqCorrupt` closes once one assumption is added; `ReqApplyWrite` fails (F4).

## Go-code bugs

None new. F1 is `issues/etcd-txn-delete-then-ignore-put.md`, already recorded; the spec admits what
the fork's gRPC check excludes.
