# RR (grpc boundary, auth, apply): targeted recheck of R-A6's and R-A9's new first-tier findings

Reviewer: fresh and independent; read-only except for this file. Date: 2026-11-09. Base: `4a6a9b6b6e`.
The fixes are uncommitted in the worktree, so I judged the working tree as it is now.

Targets:
- **R-A6:** N1 (`FromOutgoingContext` with a `nil` map), N2 (`RangeStream`'s precondition), N3
  (`isPermitted` racing `AuthEnable`).
- **R-A9:** N1 (a stale `authHook` survives `Recover`), N2 (`srvStores_kv` not tied to the lessor).

I also checked the files those fixes changed for regressions:
- `git diff 4a6a9b6b6e` over `SpecPlan/Spec/google_golang_org`, `api/v3`, `v3rpc`, `auth`, `apply`, `ApiApply`,
  `ApiReq`, 2c's `EtcdServer__{Range,RangeStream,Txn}`;
- the snippets in `grpc`, `apply`, `auth`.

I wrote every verdict below before reading the "Re-review" sections of `repair-{grpc-v3rpc,
lease-auth,apply-txn,server-core,client-core}.md`. I read them afterwards only to check that none of
the new findings is recorded there. None is.

`etc/lean-check.py` elaborates `FromOutgoingContext`, `MD__Copy`, `MD__Get`, `v3rpc/Api`,
`auth/authStore__UserAdd` and `ApiApply` with no errors.

## Verdicts

| Batch | Verdict |
|---|---|
| **2a** (v3rpc, grpc, metadata, proto boundaries) | **FAIL**. R-A6 N1's spec is fixed but its snippet does not close (**RR1**). N3 is provable but the widened denial is vacuous (**RR2**). N2 is resolved, but its fix breaks 2c/3a's read-only `Txn` (**RR3**, counted under 3a). |
| **3d** (auth) | **PASS WITH OPEN DECISIONS**: `rootTokOk` (open-questions §6 F2), unchanged. R-A9 N1 is resolved. Second tier: stale `authHook` wording in two snippets; `authBeCur`'s realization says `as.be` is read under `beMu`, but the writer reads it without the lock (`store.go:433`). |
| **3a** (apply) | **FAIL**. R-A9 N1 and N2 are resolved, but two regressions reach 3a's specs: **RR3** (`CheckTxnAuth`'s `endsDecoded` share is lost on the request path) and **RR4** (`dispatch`'s `stringerAt_irr` now needs a depth bound that nothing supplies). |

## The targeted findings

| Finding | Status now | Evidence |
|---|---|---|
| R-A6 N1: `mdAt` of the `nil` map ⊢ `False` | **Resolved, but the repaired snippet introduces a new problem (RR1)** | See "R-A6 N1" below. |
| R-A6 N2: `RangeStream` needs `own 1` plus an `endsDecoded` share | **Resolved, but the fix introduced a new problem (RR3)** | See "R-A6 N2" below. |
| R-A6 N3: `isPermitted` racing `AuthEnable` | **Resolved (provable), but the new clause is vacuous (RR2)** | See "R-A6 N3" below. |
| R-A9 N1: stale `authHook` after `Recover` | **Resolved** | See "R-A9 N1" below. |
| R-A9 N2: `srvStores_kv` gives `kvDelOk` at an unconstrained backend and deleter | **Resolved** | See "R-A9 N2" below. |

### R-A6 N1

- `mdAtN isNil m dq md` (`grpc/Api.lean:290-295`) puts the `nil` case outside `mdAt`: it is
  `⌜m = null ∧ md = []⌝`.
- `FromOutgoingContext.spec` (`:44-49`) now gives `mdAtN (!ok) m (own 1) md ∗ ⌜ok → m ≠ null⌝`.
- I tried again to derive `False`:
  - The `ok = false` case is now pure. It asks `md = []`, which is true: no `rawMD` is attached
    (`metadata.go:325-328`), and `outMD_ctxOk`/`outMD_agree` make `md` the context's unique one,
    which is `[]` there.
  - The `ok = true` case is `mdAt` of a fresh `make` (`:330-349`).
  - `MD.Copy` and `MD.Get` of a `nil` map (`metadata.go:170-184`) match the new `b = true` cases.
- The Go callers' `ok = false` branches (`client/ctx.go:29,42`, `lease.go:390`, `watch.go:1103`) are
  no longer vacuous.
- The snippet the repair rewrote no longer closes (**RR1**).

### R-A6 N2

- `EtcdServer.RangeStream.spec` drops `endsDecoded`. It takes only `rangeReqOwn r (own 1) rm`.
- 3h's `rangeReqOwn_msgAt` now carries `endsOk c`, and W0's `rangeReqOwn_unfold` carries
  `es = nil ∨ ebs ≠ []` (`Wire.lean:371-374`).
- `kvServer.RangeStream` meets the precondition: `msgAt (own 1) c` with `norm c = c`, then
  `endsOk_canon`, then `rangeReqOwn_msgAt` right to left.
- `rangeStream` never writes `RangeEnd`, so `∃ rm', rangeReqOwn r (own 1) rm'` in the post still
  holds.
- But the same change dropped `endsDecoded` from `EtcdServer.Txn`. That breaks its read-only path
  (**RR3**).
- Stale wording (second tier):
  - `kvServer__RangeStream.lean:20-21` still says the proof splits off an `endsDecoded`;
  - `v3rpc/Api.lean:712-714` says `Range`/`RangeStream`/`Txn` take `endsDecoded`.

### R-A6 N3

- `V3rpc.adminDenied` is now W0's `State.adminDenied` (`Model.lean:862-870`). It checks a principal
  `who'` with `who' = who ∨ ∃ jo ao, σ.authTables[jo]? = some ao ∧ ao.enabled = false`.
- Both schedules from R-A6 are now admitted:
  - (a) `who' = none`, `userEmpty`;
  - (b) `who'` the certificate's user.
- So `isPermitted.spec` and `kvServer.Compact` can be proved. The behavior is recorded in
  `nonissues/etcd-admin-check-authenable-race.md`.
- The new disjunct is always true, though (**RR2**).

### R-A9 N1

- `authHook` and `authHook_intro` are gone.
- `hookOut be Pre Q := Q ∨ (Pre ∗ authBeHook be Pre Q)` (`auth/Api.lean:652`).
- `AdminTriple` (`:663-672`), `AuthEnable`, `AuthDisable` and `HasRole` take `authBeCur γa be ∗ Pre ∗
  authBeHook be Pre Q` and give `authBeCur γa be` back.
- A hook of an old backend cannot be used: `Recover` moves `authBeCur` to the new backend, and
  `authBeCur_excl` rules out a second copy.
- 3a closes:
  - `authSt` holds `authBeCur γa (iface abe)` and `abe ↦□ authBackend.mk be lg`;
  - `hooksOk`'s auth half (`apply/Api.lean:816-820`) yields `□ authBeHook (iface abe) R Q` and
    `□ (Q ={⊤}=∗ R)`;
  - so `hookOut abe R Q` gives `R` back.
- No remaining use of `authHook` in any statement. It survives only in comments: `examples/specreq/auth/check.go:74` and
  `admin.go:22,62` (second tier).
- Realization note (second tier): `UserAdd` and the other writer methods read `as.be` without `beMu`
  (`store.go:433`). So `authBeCur` must hold a share of the field `as.be` itself, not only the ghost
  half. The docstring (`auth/Api.lean:100-102`) says the method "reads `as.be` under `beMu`". That is
  false of the code, but realizable.

### R-A9 N2

- `srvStores_kv` (`ApiApply.lean:668-676`) now gives:
  - `s.kv ↦□ kv` and `s.lessor ↦□ le`;
  - the new internal `srvCurBe s be`;
  - `Apply.lessorSt le kv be σ.leases σ.kv.store`, which holds `kvDelOk kv γl be ls.rd` with
    `ls.be = be` and `ls.rd ≠ nil`.
- This is exactly `optsSt`'s conjunct `lessorSt o.Lessor' o.KV' o.Backend' …`
  (`apply/Api.lean:842`), once `o.Backend'` is `s.be`.
- `NewUberApplier` reads `s.be` without `bemu` (`server.go:1193`). The tie of `o.Backend'` to `be`
  therefore rests on `srvCurBe`'s realization: the apply thread's half of `s.be ↦`. `srvCurBe` is
  2d's internal predicate, and `NewUberApplier` is 2d's own function, so that is acceptable.
- Second tier:
  - `srvCurBe` should say that it holds the field's half (`s.be ↦{1/2} be`);
  - `EtcdServer__NewUberApplier.lean`'s sketch says "`bemu`'s read lock for `s.be`", but the code
    takes no lock there;
  - `kvDelOk`'s docstring (`apply/Api.lean:705-706`) still says the deleter comes from
    "`applySnapshot`'s new store". It is the server's closure (`server.go:1087`).

## New first-tier findings

### RR1. Snippet `grpc/metadata-out` (`ReqMetadataOut`) does not close (2a)

**Evidence.**
- The repair added `if ok || md != nil { panic(...) }` (`examples/specreq/grpc/grpc.go:80-83`).
- Its Assumes line is "ctx carries no outgoing metadata", which is W0's `ctxNoMeta`. Through
  `outMD_noMeta` that gives only `outMD ctx []`.
- `FromOutgoingContext.spec` does not relate `ok` to `ctxNoMeta`. With `md = []` it admits `ok = true`,
  `m ≠ null` (`mdAtN false`).
- That case is real: a context carrying an attached empty `MD` (`NewOutgoingContext(ctx, MD{})`)
  returns `(make(MD,0), true)` (`metadata.go:330-349`). So `outMD ctx []` cannot tell the two cases
  apart.
- The `panic` is therefore reachable in the proof, and the snippet's own new check fails. The rest of
  the snippet closes.

**Who is affected.** The snippet. The Go callers only branch on `ok`.

**Fix** (either):
- A gated row in `FromOutgoingContext.spec` ("one spec, a gated row"): `∀ (b : Bool)`, the premise
  `if b then Context.ctxNoMeta ctx else True`, the post `⌜b = true → ok = false⌝`. This is true: the
  `Value` lookup is `nil`, so the type assertion fails (`metadata.go:326`).
- Or drop the check from the snippet. That leaves the `nil` path unexercised.

### RR2. The widened `State.adminDenied` is vacuous in its `who'` (2a / W0; principle "No vacuous guarantee")

**Evidence.**
- `State.init` has `auth.enabled = false` (`Model.lean:322-325`).
- `authHist` is only ever appended to (`:1148`, `:1176`).
- So whenever `adminDenied` can hold at all (some table with `enabled = true`), `authTables[0]` is an
  auth-off table. The disjunct `∃ jo ao, σ.authTables[jo]? = some ao ∧ ao.enabled = false` is then
  always true, and `who'` is free.
- Concretely: once auth has ever been enabled, the model lets *any* `Compact` be denied with:
  - `userNotFound`, for some `u'` absent from the table;
  - `userEmpty`, for `who' = none`;
  - `permissionDenied`, if some non-root user exists.

  That includes a root with a valid token, with no `--client-cert-auth`, at any later time.
- The code can only deny such a call as:
  - the token's user (`who`);
  - no user, when the flag is read off at the member (`v3rpc/auth.go:182-189`, `store.go:1072`);
  - the certificate's user, only under `--client-cert-auth` (`v3_server.go:1206-1215`).
- `client-core`'s re-review note ("or anything") shows the widening was deliberate. Its triviality
  under table 0 is not noted anywhere.

**Who is affected.**
- W0's compact step (`Model.lean:1049`) and every client of it. A root compactor (Kubernetes) can no
  longer learn that its compaction was not refused for an arbitrary other user.
- `kvServer.Compact`'s Margin now claims the model "admits exactly those readings". It admits far
  more.

**Fix.**
- Restrict `who'` to `who`, or `none`, or the certificate's principal. For example, give
  `State.adminDenied` a `tls : Principal` argument:
  ```
  (who' = who ∨ ((who' = none ∨ who' = tls) ∧ ∃ jo ao, jo < jf ∧ σ.authTables[jo]? = some ao ∧ ao.enabled = false))
  ```
  Thread `tls` through as `srvStep` already does for writes. 2a's `isPermitted` has `tls` in scope.
- If W0 is not to know the certificate principal, at least use `who' = who ∨ who' = none`, and
  record the `--client-cert-auth` case as an open user decision.
- Bounding `jo` alone does not help: a lagging member can apply the old `AuthEnable` at any time, so
  table 0 qualifies.

### RR3. `EtcdServer.Txn`'s read-only path cannot give back `txnReqOwn r dq t` (regression of R-A6 N2's fix; 2c's spec, 3a's `CheckTxnAuth`)

**Evidence.**
- The fix removed `endsDecoded r` from `EtcdServer.Txn.spec`'s pre (`EtcdServer__Txn.lean:56-62`).
- Its frame given back is still `txnReqOwn r dq t` at the *same* `dq` (`:62`).
- The read-only path calls `apply2.CheckTxnAuth(s.authStore, ai, s.lessor, r)` as `doSerialize`'s
  `chk` (`v3_server.go:353-355`). `CheckTxnAuth.spec` (`apply/CheckTxnAuth.lean:70-82`) still takes
  and returns `endsDecoded rt` beside `txnReqOwn rt dq' t`. So do `checkTxnPermission` and
  `checkTxnReqsPermission` (open-questions C19).
- `Txn` must now produce `endsDecoded r` by splitting its own `txnReqOwn r dq t` with `msgAt_split`.
  `endsDecoded` is `∃ dq'' c, msgAt … dq'' c ∗ ⌜endsOk c⌝` (`etcdserverpb/Api.lean:514-515`). The
  `endsDecoded` that comes back hides its fraction, so the split-off share cannot be rejoined, and
  `txnReqOwn r dq t` cannot be rebuilt.
- Before the fix, `Txn` received a separate `endsDecoded` and could drop it. That was C19's design:
  "the share is lost with it, which only the handler's `reqBack` notices".

**Who is affected.**
- `EtcdServer.Txn.spec` (read-only), hence `kvServer.Txn`.
- The snippets `ReqTxnReadOnly` and `etcdserverreq/kv.go`.

**Fix.**
- Since every W0 request predicate now carries `endsOk` (NF1), drop `endsDecoded`/`opsDecoded` from
  `CheckTxnAuth`, `checkTxnPermission` and `checkTxnReqsPermission`. The end facts come from
  `txnReqOwn`'s unfolds (`compareOwn_unfold`/`requestOpOwn` carry `es = nil ∨ ebs ≠ []`). Then
  retire C19 and `reqMsgAt_endsDecoded`.
- Or index `endsDecoded` by its fraction (`endsDecoded t p dq`), so the caller can rejoin the share.

### RR4. The new depth premise of `stringerAt_msg`/`stringerAt_irr`/`NewLoggableTxnRequest` has no source for a transaction or an internal request (regression of R-A6's second-tier fix; 3h, reaching 3b and 3a)

**Evidence.**
- `NewLoggableTxnRequest.spec` and `stringerAt_irr` now require `⌜Proto.depth c < Proto.depthMax⌝`
  (`etcdserverpb/NewLoggableTxnRequest.lean:48`, `Stringer.lean:53,58,68`).
- **`txn.WarnOfExpensiveReadOnlyTxnRequest`** (3b) calls `pb.NewLoggableTxnRequest(r)`
  (`txn/util.go:59`). Its pre holds only `txnReqOwn rt dqr t` (`WarnOfExpensiveReadOnlyTxnRequest.lean:45`).
  - 3h's `holds_depth` excludes transactions (`etcdserverpb/Api.lean:283`).
  - No law relates a `TxnRequest` content's depth to `txnMsgDepth t`.
  - `EtcdServer.Txn` bounds the depth only for writes (`isRead = false → …`).
  - So the call no longer closes.
- **`uberApplier.dispatch`** (3a) logs `&pb.InternalRaftStringer{Request: r}` (`uber_applier.go:99,101`)
  through `stringerAt_irr`. Its source, `irrMsgAt_msg` (`apply/Api.lean:971-973`), gives
  `∃ c, msgAt … discard c` with no depth. `Proto.Unmarshal.spec`'s success case does not state
  `depth c < depthMax` either (`proto/Unmarshal.lean:53-54`), although protobuf-go errors past
  `RecursionLimit`.
- The R-A6 claim that "callers hold it" is true of the running code, but false of the specs as
  stated.

**Who is affected.**
- `WarnOfExpensiveReadOnlyTxnRequest`, hence `EtcdServer.Txn`'s read-only path.
- `uberApplier.dispatch`, hence `Apply` and every apply snippet that goes through it (`ReqApplyWrite`, …).

**Fix** (either):
- Supply the bound everywhere it is needed:
  - add `depth c < depthMax` to `Unmarshal.spec`'s success case and to `irrMsgAt_msg`;
  - add a 3h law `reqHolds c (.txn t) → Proto.depth c ≤ txnMsgDepth t`;
  - give `EtcdServer.Txn` (and `WarnOfExpensiveReadOnlyTxnRequest`) `txnMsgDepth t + 1 ≤ 10000`
    unconditionally. `kvServer.Txn` has it from decoding.
- Or revert the depth premise on the stringer laws, keeping the old Margin.

## Second-tier findings (new or still open)

- Stale wording that names removed constructs:
  - `kvServer__RangeStream.lean:20-21` and `v3rpc/Api.lean:712-714` (`endsDecoded` taken by 2c);
  - `examples/specreq/auth/{check.go:74,admin.go:22,62}` (`authHook`);
  - `apply/Api.lean:705-706` (`kvDelOk`'s "`applySnapshot`'s new store");
  - `EtcdServer__NewUberApplier.lean` ("`bemu`'s read lock").
- `authBeCur`'s realization (`auth/Api.lean:100-102`): the writer reads `as.be` without `beMu`.
  Realize the predicate with a share of the field.
- `srvCurBe`'s docstring should name the field share (`s.be ↦{1/2} be`), which `NewUberApplier` needs.

## Counts

- Targeted findings: 5.
  - Resolved: R-A9 N1 and N2.
  - Resolved but with a new first-tier problem: R-A6 N1 (RR1), N2 (RR3) and N3 (RR2).
- New first-tier findings: 4 (RR1–RR4). Second tier: 3 items.
- Go bugs: none new. `nonissues/etcd-admin-check-authenable-race.md` covers N3's race. Its "Proof"
  section inherits RR2's overstatement ("any certificate user").
