# R-A9 (apply 3a, txn 3b, lease 3c incl. leasehttp, auth 3d, bcrypt): re-review after the repairs

Reviewer: an independent re-review agent, 2026-11-09, at `974e05095b`. I worked read-only and wrote
only this file. I formed the verdicts below from the specs and the Go code (`.lake/src/server/...`,
x/crypto v0.57.0 in the module cache). Only after that did I read `repair-apply-txn.md`,
`repair-lease-auth.md` and `open-questions.md` §C, to check whether a finding was already recorded.

## Verdicts

| batch | verdict | why |
|---|---|---|
| 3a apply | **PASS WITH OPEN DECISIONS** (3.12 `invRefused`; C17, C18) | All five provability findings and C-F6 are resolved in the text. The admin methods' hook sketch closes only once N1 (3d) is fixed: that changes the sketch, not 3a's statements. N2 is a gap in 2d's law that introduces `kvDelOk`, not in 3a. |
| 3b txn | **PASS** | No first-tier finding before. The three laws it owed now close against 3e's `rangeCtxErr` and `kvsFit`, and against 2c's sentinels. `stringerAt` replaces `stringerOk` and is given back. |
| 3c lease (+ `leasehttp`) | **PASS WITH OPEN DECISIONS** (C20, C23, C24 `leasePeerURL`) | C-F2, C-F3 and C-F9 are resolved. `TimeToLiveHTTP` is new and true of `http.go:224-282` under its recorded deployment premise. |
| 3d auth | **FAIL** | C-F1, C-F4 (two of its three parts), C-F5, C-F7 and C-F8 are resolved. **N1**: the new `authHook_intro`, together with `hookOut` and `Recover`, makes the eleven `AdminTriple` specs impossible to prove. `rootTokOk` (§6 F2) is still an open decision. |
| bcrypt | **PASS** | `ErrPasswordTooLong` is named, and `init` gives the shapes. True of v0.57.0 (`bcrypt.go:84-101`). |

## The original first-tier findings

| finding | status | evidence at HEAD |
|---|---|---|
| P-F1 `Txn` panics under `op.ok` (delete, then an ignore-put) | **resolved** | `txnAdmitted` has `Txn.txnSafe t` (`apply/Api.lean`, `txnAdmitted`). Its source is 2c's new `txnChecked_admitted.spec` (`ApiReq.lean:205`), with `txnChecked_safe` (`:200`). `txnSafe` = `opsSafe` of both branches (`txn/Api.lean:439-451`), which excludes an ignore-put after a covering delete (`put.go:55`). |
| P-F2 no source for `leasesLive`, `ls.rd ≠ nil`, `rdOk` | **resolved** in 3a (the source law is weak: N2) | `lessorSt` now carries `Txn.leasesLive s ls ∧ ls.be = be ∧ ls.rd ≠ func.nil` and `kvDelOk kv γl be ls.rd`. `kvDelOk` is persistent, and its realization is `mvccDeleter rd γ ∗ mvccLessorIs ∗ □(kbHeld ∗-∗ beTxHeld)`, which are exactly the premises of `Mvcc.mvccDeleter_rdOk.spec` (`mvcc/Api.lean:801-812`). `leasesLive` is kept: Put/Txn check the lease, and Revoke deletes the lease's keys through the attachment clause. |
| P-F3 no source for the lessor's and auth's hook contracts | **resolved for the lessor; the auth half is resolved but N1 appears** | `hooksOk be R` is in `optsOk`. Lessor half: `beHook` (persistent), `□ beHookRun be Pk f R Q` and `□ (Q ={⊤}=∗ Pk ∗ R)`, which fit `lessor.Grant.spec`'s `Pre := R`, `Post := R`. Auth half: a `□` producer of `authBeHook` at any wrapper of `be`. `authSt` holds `authBeCur γa (iface abe)` and `abe ↦□ authBackend.mk be lg`. |
| P-F4 `opStep_step` concluded all of `Step` (refusals included) | **resolved** (recorded as C17) | `opStep_step` now concludes `ownStep` = `kvStep ∨ leaseStep ∨ authStep ∨ clusterStep` at `lo = 0`. That implies `Step`, so `irrStep_step` still follows. I checked it against the backend's errors: grant at id `0` is excluded by `reqAdmitted`; TTL too large, exists, not-found, compacted and future-revision are each inside their step; compaction's admin clause holds at `authTables[0]`. |
| P-F5 `aiAt` too weak for a request without a header | **resolved** | The mutex invariant is `aa.authInfo ↦ ("", 0)`. It is true: `newAuthApplierV3` builds the zero value, and both exits reset the field (`auth.go:52-61`). |
| C-F1 a read denial is not at one auth state | **resolved** (in W0 and 3d) | W0's `State.deniedSince` takes three views `jf jx jc ≥ lo` (`Model.lean:908-913`), which is 3d's `checkDenied`. Recorded as `nonissues/etcd-auth-read-denied-across-views.md`. Snippet `auth/ReqDenied` added. |
| C-F2 `ckptOk` cannot be met by the server's closure | **resolved** (C20) | `ckptOk` is now at `context.Background()` with `threadTok` in and out. That matches `lessor.go:437,679`, which pass `Background()`, and `server.go:395-403`. `Renew` takes and returns the caller's token, and `EtcdServer.LeaseRenew` holds one. `NewLessor` lends the run loop a token, which `Stop` returns. |
| C-F3 `clusterOk` has no introduction | **resolved** (C23) | `clusterOk` is now transparent: `□ {{True}} cl.Version() {{v = null ∨ ∃ sv, v ↦□ sv}}`. 2e's `RaftCluster.Version.spec` meets it, with `Semver.verAt` = `∃ x, v ↦□ x ∗ …` and `clusterVerInv` persistent. `noCluster` meets it from its body. |
| C-F4 `authBackendAt`, `authHook`, `authnCtx` have no introduction | **resolved for `authBackendAt` and `authnCtx`; `authHook` is resolved but unsound (N1)** | `Backend.authBackendAt_intro` (`backend/AuthBackend.lean:82`). `authnCtx` is transparent, over `Context.ctxValueIs` (`auth/Api.lean:438-448`). `authHook_intro` plus 4a's `authBeHook_intro` (`AuthBackend.lean:102`). |
| C-F5 3d's context predicates are not grpc's | **resolved** | `ctxInMD`, `ctxCertUser` and `ctxPeerCN` are now `abbrev`s of `Grpc.*`. `ctxToken` has `tokKeysOk`. |
| C-F6 `NewUberApplier` has no slots for the hooks and the deleter | **resolved in 3a** (see N1 and N2) | `hooksOk` and `lessorSt`, as above. `NewServer.lean:108` and `applySnapshot.lean:56` cite their sources. |
| C-F7 `waiterOk` is false before `start` | **resolved** (C21) | `waiterOk iw R` is gated on `R`. `tokenProviderAt … R`, `authGate γa R`, and `info`/`isValidSimpleToken`/`AuthInfoFromCtx` take `□ R`. True: the simple provider calls the waiter only from `info` (`simple_token.go:240`). |
| C-F8 bcrypt's error is unconstrained | **resolved** | The disjunct is now `72 < |pw|` with `errIs ErrPasswordTooLong err`. The length test is first (`bcrypt.go:96`). `init.spec` gives the three `errors.newVar` values, distinct. Snippet `auth/ReqLongPassword` added. |
| C-F9 `RenewHTTP` says nothing of its error | **resolved** | The post is `nil`, or `Lease.errIs ErrLeaseNotFound err` (exactly `http.go:205-206`), or `errIsNot err t` (no other path returns or wraps the sentinel: `http.go:171-218`). Snippet `lease/ReqRenewForward` added. |
| open decision: `WithRoot`'s `rootTokOk` | **still open** (open-questions §6 F2) | unchanged |
| P: snippet `ReqCorrupt` needed a valid range; `ReqGrantHook` cited a stale name | **resolved** | `alarm.go:34-35`; `lease/lessor.go:281`. |

Totals: 14 original first-tier findings (P-F1–F5, C-F1–F9). All 14 are resolved in the text. One
fix (`authHook`, the shared part of P-F3, C-F4 and C-F6) brings a new defect, N1. One recorded open
decision (`rootTokOk`) is still pending.

## New findings

### N1 (first tier, 3d): a stale `authHook` survives `Recover`, so the admin triples cannot be proved

- **Where:**
  - `auth/Api.lean`: `authHook_intro.spec` (`:582`), `hookOut` (`:667`), `AdminTriple` (`:677-685`);
  - `auth/authStore__Recover.lean`;
  - 3a's admin sketches (`applierV3backend__UserAdd.lean:15-18` and the other ten).
- **What fails.** `authHook_intro` is `authBeCur γa be ∗ authBeHook be Pre Q ⊢ authBeCur γa be ∗
  authHook γa Pre Q`, and it gives `authBeCur` back whole.
  - So a holder can mint an `authHook` for the current backend `be0` and keep it. `hookOut`'s
    unused branch even hands it back (`Pre ∗ authHook γa Pre Q`).
  - It can then call `Recover`, which moves `authBeCur γa be0` to `authBeCur γa be` and takes no
    outstanding hooks.
  - It can then pass the stale `authHook` to an admin method.
- **Why no realization works.** The method locks the current backend `be` and runs `be`'s hook
  (`authBatchTx.Lock` is `LockInsideApply`). But the stale hook only says what `be0`'s hook does
  (`Backend.hookRun` at `be0`'s names and lock invariant `Pk`). So the promised `Q` (`hookOut`) has
  no source. The ways out all fail:
  - The stated realization ("`∃ be,` that half at `be` (a fraction) `∗ authBeHook`", `Api.lean:99-102`)
    contradicts `authHook_intro`, which keeps the writer's half whole, together with
    `authBeCur_excl`.
  - Any ghost tie that would stop a stale hook from being used must also stop `Recover` from moving
    the backend, and `Recover`'s spec does not take the hooks back.
  - I found no assignment of `authHook` that makes `authHook_intro`, `authBeCur_excl`, `Recover.spec`
    and the eleven `AdminTriple` specs all provable.
- **Who it affects:**
  - 3d's eleven admin methods (`UserAdd` … `AuthDisable`);
  - 3a's backend admin appliers, whose sketches go through `authHook_intro`.

  Today's applier never reuses a hook, so this is about what the statements admit, not about a
  real execution.
- **Suggested fix** (smallest):
  - drop `authHook` and `authHook_intro`;
  - make `AdminTriple` take `authBeCur γa be ∗ authBeHook be Pre Q` and give back `authBeCur γa be ∗
    (Q ∨ Pre ∗ authBeHook be Pre Q)` (redefine `hookOut` that way). 3a already holds `authBeCur` in
    `authSt`, and `hooksOk` supplies `authBeHook` per call.
  - Alternatively, keep `authHook` but make it hold `authBeCur` itself: `authHook_intro` consumes
    `authBeCur`, and `hookOut` returns it on both branches.

  Either way C22's design (backend as exclusive writer state) stays.

### N2 (first tier for the caller chain; 2d's law, outside this area): `srvStores_kv` gives `kvDelOk` at an unconstrained backend and deleter

- **Where:** `etcdserver/ApiApply.lean:654-659`. It reads `∃ (kv be : GoInterface) (γl) (rd : GoFunc), … ∗
  Apply.kvDelOk kv γl be rd ∗ …`.
- **What fails.** 3a's `lessorSt` needs `kvDelOk o.KV' γl o.Backend' ls.rd`: the server's backend
  `s.be`, and the lessor's actual deleter `ls.rd` from its `lessorState`. `kvDelOk` is opaque and has
  no law relating it to anything else. So the `be` and `rd` the law gives cannot be identified with
  `ls.be` and `ls.rd`. As a result, `NewServer` and `applySnapshot`, whose sketches cite
  `srvStores_kv` (`NewServer.lean:108`, `EtcdServer__applySnapshot.lean:56`), cannot establish
  `optsSt`.
- **Suggested fix:**
  - state `srvStores_kv` with `be` the server's backend field and `rd` the lessor's: for example,
    take `Lease.lessorState γl n ls` (or a `srvLessor`-held fact) and conclude `kvDelOk kv γl ls.be
    ls.rd`, with `ls.be = s.be`;
  - or move the ties into the conclusion as pure equalities.
- **Also in the docstrings.** `kvDelOk`'s and `srvStores_kv`'s docstrings say the deleter after a
  snapshot comes from "applySnapshot's new store". In fact it is the server's closure `func() {
  return s.kv.Write(TODO) }` (`server.go:1087`), not `NewStore`'s (`kvstore.go:117`). The closure
  meets 3e's transparent `mvccDeleter` through `KV.Write`'s spec, so this is a wording fix. I did not
  re-check A7's area further; this is for A7's re-reviewer to confirm.

### Second tier

- **S1 (3a/2d, provisional).** 3d's `authnCtx` requires `(46#8) ∉ p` and `0 < idx < 2^64`
  (`auth/Api.lean:448`). The applier's only source is `authnIdx`, and neither the docstring of
  `authnIdx` (`apply/Api.lean`, "for every `name`, `tok`") nor 2d's `applyLent_opts` states either
  fact. `IrrOp.ok` says nothing of `.authenticate`'s prefix either. Fix: add to `authnIdx`'s meaning
  that the prefix has no `.` (it is the proposer's `GenTokenPrefix`, letters only) and that `idx` is a
  nonzero `uint64`.
- **S2 (3a snippet).** `apply/ReqApplyWrite` panics "a valid put refused" on any error. But W0's
  `kvStep` put answers `keyNotFound` for an ignore-value or ignore-lease put of an absent key
  (`PutReq.check`, `Model.lean:686-689`). "Valid" (`PutReq.invalid = none`) does not exclude that.
  Add to `Assumes:`: "no ignore flag, or the key present".
- **S3 (3c, completeness note).** The lease HTTP handler (`leasehttp/http.go:91`) is the other user
  of `Renew`, and `Renew` now needs a `threadTok`. The handler is out of scope today (no `NewHandler`
  spec; `RenewHTTP.lean`'s header), but whoever specifies it must give `net/http`'s handler goroutine
  a token.
- **S4 (snippets).** `lease/ReqPromoteCheckpointer` (`Renew`) and `auth/ReqBoot` (`AuthInfoFromCtx`)
  now need a thread token. Their `Assumes:` lines do not say so: wording only.

## Regressions check (the 70 changed spec files and 7 changed snippet files)

- **3a.** Every statement that changed is listed below, and the rest are docstring-only.
  - `lessorSt`, `authSt`, `optsOk`, `optsSt`;
  - `txnAdmitted`;
  - `ownStep`, `opStep_step`;
  - `clusterVerOk`, now transparent over 2e's `verFits` and `Semver.parse`;
  - `endsDecoded`/`opsDecoded`, now 3h's share-holding predicates, given back by
    `CheckTxnAuth`/`checkTxnPermission`/`checkTxnReqsPermission`; `□` at the apply via
    `reqMsgAt_endsDecoded`;
  - `chkExact`/`replyAt_result` over `srvErr`;
  - new `irrMsgAt_msg`, `replyAt_msgOpt`.

  `optsOk` stays persistent: `hooksOk` is persistent, and so is `clusterVerInv` (an `inv`).
  `ClusterVersionSet`/`DowngradeInfoSet` now close against 2e's `RaftCluster.{Version,SetVersion,
  SetDowngradeInfo}` with `beVer` and `clusterVerInv`. Nothing false or vacuous found, apart from N1
  (through 3d) and N2 (through 2d).
- **3b.** The `Warn*` statements now take `EtcdServerPb.stringerAt` and give it back. `ctxErr` is
  realized over 3e's `rangeCtxErr` (`ctxErr_of_range` new). Closes.
- **3c.**
  - Changed: `ckptOk`, `clusterOk`, `NewLessor`/`Renew`/`Stop` (thread token), `init` (`newVar`), new
    `TimeToLiveHTTP`, `RenewHTTP`'s post, `errIsNot`.
  - All are true of `lessor.go:60-63,437,679` and `http.go:171-282`. `Stop` returning the loop's
    token is sound: the loop runs `defer close(doneC)` and `Stop` waits on `doneC`.
  - `TimeToLiveHTTP`'s premise `leasePeerURL` is a recorded deployment premise (C24), with its issues
    filed (`issues/etcd-leasehttp-timetolive-nil-{response,header}-panic.md`).
- **3d.**
  - Changed: sentinels as `errIs`/`init`; `R` gates (`waiterOk`, `tokenProviderAt`, `authGate`,
    `simpleAt`, `tp_*`); `authnCtx` transparent; `authBeCur`/`authBeHook`/`authHook_intro`;
    `Recover` moving the backend; `WithRoot`'s `ctxValueAt`.
  - New laws: `authStoreAt_lb` and `authReach_of_reach` (pure in W0: a `Step` moves `σ.auth` only by
    `authStep` of a permitted admin request; plausible).
  - All are plausible from their realizations, except N1.
- **bcrypt.** True of v0.57.0.

## Snippets

| package | changed or added | result |
|---|---|---|
| apply (8) | `ReqNewUber` (Assumes), `ReqApplyWrite` (Specs), `ReqCorrupt` (Assumes) | `ReqApplyWrite` now closes through `opStep_step`'s `ownStep`, except for the S2 assumption gap. The others close. |
| txn (18) | none | close (unchanged specs, or changes covered above) |
| lease (14+1) | `ReqGrantHook`, `ReqNewLessor`, `ReqPromoteCheckpointer` (checkpointer at `Background()`, forks a goroutine with the lent token), `ReqRenewForward` (new) | close (S4 wording) |
| auth (16+2) | `ReqLongPassword` (new), `ReqDenied` (new: `checkDenied`'s `af.enabled ∧ ¬ ax.isRoot` with `authStoreAt_lb`), `ReqBoot` (gated waiter, `AuthInfoFromCtx` after `started`), `ReqTokenUser` (Specs) | close. `ReqAdminSteps`/`ReqUserAddThenCheck` rest on the `AdminTriple`s, which are subject to N1 (the snippets need no change). |

Coverage of the user patterns the completeness report found unserved:
- read denial: `ReqDenied`;
- checkpointer through `raftRequest`: `ReqPromoteCheckpointer`'s goroutine;
- `NewLessor` with a cluster: `ReqNewLessor`;
- bcrypt over 72 bytes: `ReqLongPassword`;
- follower renewal: `ReqRenewForward`;
- gated waiter: `ReqBoot`.

All are now covered.

## Counts

- Spec files re-checked: 70 changed (apply 28, txn 7, lease 9 incl. 3 in `leasehttp`, auth 23, bcrypt 2)
  plus the cited callee and caller laws (ApiReq, ApiApply, AuthBackend, mvcc's deleter, membership's
  `Version`, semver's `verAt`).
- Snippet files: 7 changed, 6 snippets new or substantively changed. All close under their stated
  assumptions, apart from the S2 and S4 wording.
- Original first-tier findings: 14, all resolved. New first-tier findings: N1 (3d), N2 (2d's law,
  affecting 3a's callers). Second tier: 4.
- Go bugs: none new. P-F1's panic is `issues/etcd-txn-delete-then-ignore-put.md`. C-F1's anomaly is
  `nonissues/etcd-auth-read-denied-across-views.md`.
