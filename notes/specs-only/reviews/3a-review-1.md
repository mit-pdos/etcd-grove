# Batch 3a (apply), review round 1: provability and completeness

Reviewer: one agent for both kinds, 2026-11-09, at `ada75e2e1d` (3a's draft is `ce20d0f6d7`; 2d's
round-1 repairs `ace7137300`, 3d's draft `74a953bc71` and 3e's `ada75e2e1d` came after it). Go:
`.lake/src/server/etcdserver/apply/*.go` (`a4d2bb17`). Read-only; snippets `go vet` clean.

## What is good

- **`irrStep`'s order is Go's.** I checked it against `uber_applier.go:135-275`, `auth.go:43-63` and
  `backend.go`, and found it right:
  - The administrator check comes first and runs in both modes (`auth.go:52-58`, before `dispatch`).
  - Then the membership switch (`uber_applier.go:158-178`), then `!shouldApplyV3 → nil` (`:179-181`).
  - Alarms go through every layer to the backend (`Alarm` is overridden only by the backend), then
    `restoreAlarms` runs on ACTIVATE or DEACTIVATE (`:267-275`).
  - The corrupt layer is outermost, then capped (`restoreAlarms`, `:123-133`).
- **The classifiers are exact:**
  - `needAdmin`: all 13 cases of `auth.go:244-275`.
  - `noSideEffect`: `apply.go:51-53`.
  - `corruptRefused`: `corrupt.go`'s 7 methods.
  - `cappedRefused`: `capped.go`. `Cost(r) > 0 ↔ hasPutL`, nested transactions included
    (`storage/quota.go:136-173`). The capped applier's zero-valued `q` is safe because `Cost` reads
    no field.
- **The auth checks follow Go's order.** I checked each against Go:
  - `preErr`/`opErr` match `store.go:862-901`, and `adminErr` matches `store.go:915-936`.
  - Put: the key, then the lease's keys, then `prevKv` (`auth.go:73-94`).
  - Delete: write, then read (`:103-115`). A transaction's delete: read, then write (`:160-175`).
  - `leaseErr`: `Lookup` nil, or the administrator shortcut (`:198-220`).
  - UserGet and RoleGet (`:222-242`). The `σ.auth.users [] = none` premise is what makes
    `HasRole("")` false.
- **`alarmStep` is Go's.** `Activate` of an already-raised alarm returns the stored member, so the
  answer is `[⟨mid,k⟩]` either way (`alarms.go:62-73`). DEACTIVATE of an unknown type gives an empty
  answer. Another action gives `nil, nil` (`backend.go:132-133`) → `noAns`.
- **`resMatch`'s three allowed differences are real, and I found no fourth:**
  - The alarm map's iteration order.
  - `SkipRangeExecution` (`apply.go:43`).
  - The quota's `ErrNoSpace` after a write it applied (`quota.go:412-437`). Note that a write
    transaction whose read-only branch ran also gets it, since `Cost` is the maximum over both
    branches; `quotaWrite` covers that case.

  Headers, the trace and `Physc` are not modelled, as they should not be.
- **The rest of the model:**
  - Per-member TTLs: `irrStep_ttl` holds because the gates read only whether a lease exists.
  - `irrStep_env`: `V3alarm.raise` is `EnvStep.alarm` or no change. A publication for a removed
    member is a no-op `map`.
  - The `v3 = false` semantics, including the non-nil `&Result{Err}` for an administrator refusal
    (`auth.go:53-57`).
- **The batch's discipline is right:** one spec per function in every mode, the old 25 premises
  gone, and the old `backendUnderQuota` premise turned into a disclosed margin with a nonissue.

## First tier

**F1. `Apply.spec` cannot call `IsRegistered`, and it dropped the waiter fact (provability and
completeness; `Apply.lean:169-185`).**
- 2c's `list.IsRegistered.spec` at HEAD (unchanged since `a098c18d14`, before this draft) takes
  `waitWasReg γw id ∨ waitNever γw id` and gives `⌜b = false⌝ -∗ waitDone γw id`.
- `Apply.spec`'s pre has only `Wait.listAt l γw Pw ∗ threadTok`, so the call at `apply.go:40` cannot
  be made.
- The margin ("2c's `IsRegistered` gives nothing today", `Apply.lean:136-139`) is stale.
- The approved shape (`examples/apply-uber-contract.md`) carried the waiter fact (`G ot id`) in both
  branches; this post dropped it.
- Who is affected: 2d's `applyEntryNormal`.
  - On the `ar = nil` path (`server.go:2001`) it must justify not triggering the waiter.
  - For a skipped transaction's result it must justify that nobody owes a value.
- Fix:
  - Pre: `waitWasReg γw ir.reqId ∨ waitNever γw ir.reqId` (2d gets it from its cluster invariant).
  - Post: `(∃ sk, Q sk ar ∗ (⌜sk = false⌝ ∨ waitDone γw ir.reqId)) ∨ (⌜ar = null ∧
    noSideEffect⌝ ∗ waitDone γw ir.reqId ∗ P)`.

**F2. `irrStep_step`'s `hdrOk` premise is false of real requests, and `Irr.who` is not 2c's or 3d's
principal (`Api.lean:232,236,811-814`).**
- How such a header arises:
  - With auth on, client-certificate auth on and no token, the header is the TLS identity
    (`v3_server.go:1206-1215`, `1078-1079`).
  - `AuthInfoFromTLS` (`store.go:1040-1043`) takes `Username = CommonName`, which may be `""` (a
    certificate with SANs only), and `Revision = as.Revision() ≥ 1`.
  - So `user = ""` with `rev ≠ 0`, and `hdrOk` fails.
- For such a put:
  - Go answers `ErrPermissionDenied` (`store.go:885-889`: no user `""`).
  - `Step none` would require `permErr none = ErrUserEmpty`.
- 3d's principal for this request is `some cn` (`auth/Api.lean:309`, `AuthInfoFromTLS`), and so is
  2c's `srvStep … tls` (`ApiReq.lean:133-135`). 3a's `Irr.who` gives `none`.
- Who is affected: 2c and 2d. No law covers such an entry, so the history cannot move.
- Fix: drop `hdrOk`, and define `Irr.who := if ir.user = [] ∧ ir.authRev = 0 then none else some
  ir.user`. I checked every case against Go with this definition: KV, lease revoke,
  administrator, UserGet `""`, RoleGet. Each agrees, given W0's "no user `""`":
  - `user ""`, `rev ≠ 0` → `permissionDenied`, which is `permErr (some "")`.
  - `user ≠ ""`, `rev = 0` → `ErrUserEmpty`, a refusal.

**F3. `irrStep_step` (and the obligation `opStep_step`) are false at unreachable states that the
premises admit (`Api.lean:342-347` vs W0's `State.permits`, `Model.lean:817-827`).**
- Lease 0: `putChecks` always contains `.lease p.lease`, but W0's `RequestOp.leases` drops lease 0.
  - If `σ.leases 0 ≠ none`, every key without a lease is "attached" to 0.
  - With auth on and a non-admin user, Go-the-model refuses with `permissionDenied` where W0
    `permits`.
- A key whose record names a dead lease:
  - `leaseErr` passes (`Lookup` nil), while W0's `permits` requires the key covered.
  - So W0 answers `permErr` where the model answers `ErrLeaseNotFound`.
- Both states are unreachable, but the law quantifies over every `σ` with only
  `σ.auth.users [] = none`. As stated it cannot be proved, and nor can 3b/3c's `opStep_step`.
- Fix: add the reachable-state facts as premises (`σ.leases 0 = none`; `σ.attached id k → σ.leases
  id ≠ none`), or one premise `Reach (State.init ms) σ`. Ask W0 for the `etcdLb` laws that give
  them, as was done for "no user `""`".

**F4. 2d's round-1b requests are unanswered
(`req/go_etcd_io_etcd_server_v3_etcdserver_apply.md`, "from 2d (round 1b)").** The request
postdates the draft.
- **Same configuration, TTL-variant states, equal answers.** `irrStep_ttl` gives only `respTtlEq`,
  so the proposer's waiter cannot be shown to get the answer the commit fixed. The law is true:
  the granted TTL is `max(ttl, mc.minLeaseTTL)` and reads no stored TTL.
  - Fix: add `irrStep_ttl_same` / `applyStep_ttl_same` (`ttlEq σ₁' σ₂' ∧ r₁ = r₂`).
  - Fix: strengthen `opStep_ttl` to `mc₁ = mc₂ → r₁ = r₂`.
- **`applyStep_reach`.** It is not derivable from the laws:
  - Alarm GET and DEACTIVATE have no law mapping them to `Step who .alarmList` /
    `.alarmDisarm` (`irrStep_step` covers only `.req`).
  - The hashed user changes need W0's credential model (W0 item 2).
  - Fix: state `applyStep_reach` (for `IrrOp.ok` entries at reachable states) and the alarm law.

**F5. No law gets the stores back out of `smAt` (`Api.lean:573`, `NewUberApplier.lean`).**
- 2d's `applySnapshot` recovers the stores and then builds a new applier (`server.go:1178`):
  - the lessor (`server.go:1087`);
  - mvcc (`:1094`);
  - the alarm store (`:1118`);
  - the auth store (`:1127`);
  - the membership (`:1151`).
- 2d's `applyEntryNormal` reads `s.alarmStore.Get(NOSPACE)` while the thread holds `smAt`
  (`server.go:2006`).
- Only the internal `smAt_unfold` exists, and it gives the opaque `stAt`.
- Fix:
  - `NewUberApplier` also returns a persistent `uberOpts ua opts`, with the law `uberOpts ua opts ∗
    smAt ua σ ⊣⊢ uberOpts ua opts ∗ optsSt opts σ`.
  - Or `smAt` gives the alarm store's reader half through a law (the open alarm-view question).

**F6. `CheckTxnAuth`'s post does not serve 2c's linearizable read-only `Txn`
(`CheckTxnAuth.lean`, `v3_server.go:355`, `doSerialize` `:1053`).**
- What W0's `kvStep .txn` needs:
  - for success, `σ.permits` at the answer's state, or `authOffSince lo`;
  - for a denial, `¬permits` at the answer, or `deniedSince lo`.
- What the post gives:
  - for success, each pair permitted at *some* auth state anywhere in the history: no lower bound
    `lo`, and no single state;
  - for an error, its kind only, with no witness state for `permissionDenied`, which is not a
    refusal.
- 2c's `EtcdServer.Txn` sketch assumes "the permission … at the auth store's state".
- The code does give more:
  - `isOpPermitted` passes only at `a.rev ≤ rev`, and `doSerialize` re-checks `rev =` the final
    revision.
  - The checks run after the read-index wait, so at states at or after the call's `lo`.
- Fix: take `authRead` with a lower bound (3d's `authLb`, as 3d's `checkPost`/`adminPost` do) and
  state:
  - each check at a recorded state `≥ lo` with `a.rev ≤ rev`;
  - a `permissionDenied` with the state where it failed.

  The snippet `ReqCheckTxnAuth` should panic on what 2c needs, not only on the error's kind.

**F7. Most of the snippets are unprovable from the specs.**
- *`kv.Rev()`* is read in `ReqApplyWrite`, `ReqApplyReplay`, `ReqApplyNoResult`,
  `ReqNoSpaceCapped` and `ReqStaleRevision`. `smAt` is opaque, and no law reaches the KV's state
  (see F5). Real callers never do this; check the answer's header revision instead.
- *`ReqApplyWrite`*: its `ar.Err != nil → panic` rests on "the backend is under its quota", which
  nothing expresses. `resMatch` (c) allows `ErrNoSpace`. Handle it as 2c does: outcome 3.
- *`ReqApplyReplay`*: `ar != nil → panic`, but `resultAt` admits a non-null result for `v3 =
  false` (`ApiResult.lean:64-66`).
  - Either tighten `resultAt` (`¬v3 ∧ ¬isMembership ∧ admin passed → ar = null`), or drop the
    panic. 2d returns before reading `ar` at `server.go:1998`.
- *`ReqNoSpaceCapped`*: the activation's `AlarmResponse` contents cannot be read, because `irrReply`
  of `.alarmActivate` is `True` (`ApiReq.lean:378-385`, via `opBody`). Ask 2c for an alarm reply, or
  drop the check.
- *`ReqCorrupt`*: `ar == nil → panic`, but `Apply.spec` relates nothing to registration. A registered
  waiter may also have given up (`Trigger(id, nil)`, `v3_server.go:1117,1129`), so the nil branch is
  real. Restate it as `ar != nil && !errors.Is(ErrCorrupt) → panic`.
- *`ReqStaleRevision`*: its "Assumes" omits "no CORRUPT/NOSPACE alarm". Under NOSPACE the put is
  `ErrNoSpace` before the auth layer.
- Provable: `ReqNewUber` (`isUber_apply`'s `ua = ok ui`) and `ReqCheckTxnAuth` (as written).

**F8. Some helper specs are unsound (template copy errors).**
- `authApplierV3.UserGet.spec` and `RoleGet.spec` give back `aiAt aa u rev`. On a refusal Go sets
  `aa.authInfo` to `""`/`0` (`auth.go:225-226`, `236-237`).
  - Fix: `∃ u' rv', aiAt aa u' rv'`, as `dispatch`'s post already has.
- `checkLeasePutsKeys.spec`: the lease object `l` is not tied to `id` (no `leaseObj l id`
  premise), so the post's `Check.lease id` is about an arbitrary lease.
  - Fix: take 3c's lease-object predicate for `l` and `id`.

**F9. `resMatch` (c) is sound only once W0 accepts item 1, and 2c and 2d still contradict it.**
- At HEAD `noSpace` is a definite refusal (`Model.lean:330-332`, not `indefinite`).
- So 2c's waiter, given `ErrNoSpace` for a write that took effect, would return a refusal that W0
  reads as "nothing changed".
- 2d's `applyEntryNormal` sketch says "the refusal `.err .noSpace` is a `Step` with no change, fixed
  at the entry's commit". That is false for the quota's case.
- This is decision 2 of `batch-3a.md`. It blocks 2c and 2d until W0 or the user settles it. Keep the
  nonissue's `blocks-proof: no` only if W0 adopts item 1.

## Second tier

- **S1. Alarm GET.**
  - `opBody (.alarm .get _ at')` is `.req .alarmList` for every `at'`, but the answer is
    `getOf σ.alarms at'`, filtered by type. W0's `alarmList` is every alarm (`Model.lean`,
    `clusterStep`).
  - A client can send a typed GET through `Maintenance.Alarm` (`maintenance.go:258-268,366-377`
    → `v3_server.go:805`).
  - Fix: restrict `opBody` to `at' = 0` (else `.noop`, or a typed request of W0's).
- **S2. Unneeded premise.** `IrrOp.ok` excludes ACTIVATE of an unknown alarm type.
  - An administrator can propose one (`maintenance.go:372-377`).
  - Go stores it without panicking (`alarms.go:62-73`).
  - Such an entry has no `applyStep_total`. This is W0's `AlarmKind` limitation; record it (W0 or
    a nonissue) rather than leave a silent premise.
- **S3. Laws not provable from the listed ones.**
  - `irrStep_oldRev` and the `.req` cases needed by `ReqApplyNoResult` need `opStep` facts off
    `op.ok`/`hdrOk`.
  - Add `opStep_noOldRev` (the backend never answers `ErrAuthOldRevision`).
  - Add `opStep_read` (a `noSideEffect` operation changes nothing), and an `irrStep_read`. 2d's nil
    path then needs no `hdrOk` or `opStep_step`.
- **S4. Who establishes `IrrOp.ok` for a committed entry.**
  - `authRecordFits op` is opaque and required of every `.req`, including puts; there is no law
    for non-auth operations.
  - `clusterVerOk` is unowned.
  - There is no bridge from 2c's `IrrBody.wf` (and `txnChecked`) to `reqAdmitted`/`IrrOp.ok`.
  - Fix: state the bridge and the trivial `authRecordFits` cases, and name what 2d's `histPropose`
    `D` must carry: `irrDecodes ∧ hasId ∧ ok`.
- **S5. 1:1 replacement is incomplete.**
  - 2e still declares the provisional, *shared* `ApplyCfg`/`applyCfgIs`
    (`ApiBoot.lean:17,192-199`, `NewServer.lean:52`).
  - 3a and 2d settled on per-member `Apply.MemberCfg` with `srvCfg`.
  - 2e must produce `srvCfg s mc` with `mc.ok`. `mc.ok`'s upper bound (`minLeaseTTL ≤
    MaxLeaseTTL`, and no overflow in `server.go`'s `minTTL`) is a configuration fact 2e has to
    supply.
- **S6. Realization of `aiAt`.** The mutex invariant `∃ ai, aa.authInfo ↦ ai` (`Api.lean:110-111`)
  loses the reset value. A header-less entry (`auth.go:46-51`) needs `("", 0)` there.
- **S7. Lent `R` (uncertain).**
  - `uberApplier.Alarm`, `applierV3backend.ClusterMemberAttrSet` and `DowngradeInfoSet` take no
    `R`, but they write the backend:
    - `schema/alarm.go:52-56` (`LockInsideApply`/`Unlock`);
    - `MustSaveMemberToBackend` (`cluster.go:474`);
    - `MustSaveDowngradeToBackend`.
  - By the header, `R` is what the post-lock hook needs. Thread `R` through these three or say why
    they need none. This depends on 2e's/4a's hook specs.
  - Also, `R` is fixed at construction while the hook moves the consistent index to each applying
    index. Check with 2d that a fixed `R` carries what `applyEntryNormal` needs ("ci moved to k or
    unchanged").
- **S8. Requests that came after the draft.**
  - 3d's item 2: `admNext` threaded to the administration methods.
  - 3d's item 4: `authnCtx`/`tokFrom` threaded from entry to entry for `Authenticate`.
  - The backend specs have no slot for either.
- **S9. Field count.** `irrDecodes` says "one of the known fields set". It should say exactly one:
  `needAdminPermission`, `noSideEffect` and `dispatch` test the fields in different orders.
- **S10. Locality.** The internal vocabulary (`beAt`, `stAt`, `applierAt`, `uberAt`, `uberChain`,
  `aiAt`, `wrapperAt`, `replyAt`, `smAt_unfold`) sits in the client-facing `Api.lean`. Move it to an
  `Internal` module the package's specs import.

## Users and patterns (completeness)

Outside the batch, `go.etcd.io/etcd/server/v3/etcdserver/apply` is used only by the server package.
I found no other user in the examples or in Kubernetes.

| Pattern | Call site | Covered? |
|---|---|---|
| Apply a committed entry | `server.go:1995` | `ReqApplyWrite`/`Replay`/`NoResult` (see F7) |
| The nil-skip path and `Trigger` | `server.go:2001-2008` | Needs F1's `waitDone` |
| `ErrNoSpace` → propose the alarm, then trigger | `server.go:2006-2027` | Needs F5 for `alarmStore.Get`, and F9 |
| Rebuild the applier after a snapshot | `server.go:1178-1197` | Needs F5 |
| Build the applier at boot | 2e's `NewServer` | Needs S5 |
| Read the result on the request path (`Err`, the `Resp` kind, `Trace` mutated, `<-Physc`, then `ForceCommit`) | `v3_server.go:392-418,1015-1031,1126` | Through 2c's `applyResult` (fine) |
| A compaction's `Physc` | `v3_server.go:402` | No snippet: add one |
| `CheckTxnAuth` | `v3_server.go:355` | F6 |

## Targets ranked by need of revision

1. `Api.lean`: F2, F3, F4, F5 (laws), S1-S4, S9, S10.
2. `Apply.lean`: F1.
3. `CheckTxnAuth.lean`: F6.
4. The snippets `examples/specreq/apply/*.go`: F7.
5. `authApplierV3__UserGet.lean`, `authApplierV3__RoleGet.lean`, `checkLeasePutsKeys.lean`: F8.
6. `ApiResult.lean`:
   - `resultAt` for `v3 = false` (F7);
   - `opBody` for a typed GET (S1);
   - `resMatch` (c), pending W0 (F9).
7. `uberApplier__Alarm.lean`, `applierV3backend__{ClusterMemberAttrSet,DowngradeInfoSet}.lean`: S7.
8. `NewUberApplier.lean` and `uberApplier__Apply.lean`: F5's law.

The other generated specs I spot-checked look right:
- the capped `Txn`;
- the corrupt `Range`;
- the quota `Put`;
- the backend's `LeaseGrant`, `Compaction`, `newHeader`, `Authenticate` and `Alarm`;
- `checkLeasePuts`, `checkPutAuth`, `checkTxnReqsPermission`, `dispatch`, `restoreAlarms`;
- the auth applier's `DeleteRange`.

## Bugs in the Go code

None. The empty-CN behaviour (F2) is consistent in Go (`ErrPermissionDenied`); it is a mismatch in
the spec. The quota's `ErrNoSpace` after a write is already recorded
(`nonissues/etcd-apply-quota-nospace-after-write.md`).

## Verdict

Not done; round 2 needed. The model of one apply is faithful to the code. What fails is the laws and
specs that connect it to its callers and to W0:
- a principal definition that misclassifies one real request kind (F2);
- missing reachable-state premises (F3);
- 2d's and 2c's needs: TTL-exact answers, `Reach`, the stores out of `smAt`, the waiter fact,
  `CheckTxnAuth`'s states (F1, F4, F5, F6);
- two unsound templated helpers (F8);
- snippets that test facts the API does not expose (F7).

The `ErrNoSpace` question (F9) goes to the user or W0.
