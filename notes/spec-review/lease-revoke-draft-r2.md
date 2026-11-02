# Review, round 2: the lease-revoke Draft in code

Reviewer: independent spec review, 2026-10-31. Worktree `/shared/etcd-grove-leaserevoke`, branch
`lease-revoke` at `5879096ea3` with uncommitted changes: the Draft
(`apply/LeaseRevokeDraft.lean`, `apply/LeaseRevokeProbe.lean`, both untracked), the restated
`Spec/go_etcd_io/etcd/server/v3/lease/lessor__Revoke.lean` and its proof, and the new vocabulary in
`storage/mvcc/LeaseItems.lean`. `apply/` means `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/`.
Round 1's findings are in `notes/spec-review/lease-revoke-draft.md`. The plan's R1–R8 are in
`notes/lease-revoke-plan.md`, last section.

The Draft, the probes, the restated spec, its proof and `LeaseItems.lean` all check with no error
(`etc/lean-check.py -a`; the Revoke proof was already checked at this content, "unchanged").

## Summary

**No blocker.** Both round-1 blockers are fixed in the code:
- R1: `lessor.Revoke.spec` is stated at `mvcc.leaseDels`, and its proof goes through.
- R2: `rdAt` quantifies over every name set, and the probe `kvWriter_open` shows that the names
  `kvWriter` hides can be used.

I walked `deriveRevokeStmt` resource by resource. It is provable from `lease.lessor.Revoke.spec`
with the premises it names, given four small laws that are not written yet (F4). `chainRevokeStmt`
is provable from the layers once their LeaseRevoke specs are restated. As written in code, though,
it reads two definitions that have not been replaced yet (F2).

Findings by severity:

| # | Severity | Target | In short |
|---|---|---|---|
| F1 | major | `rdAt` | Nothing produces it today. `mvcc.New`/`newWatchableStore` give `rdIs` at their own names only, so the docstring's "the server's build has it" is false. Its producer must be restated (sound; L3c). |
| F2 | moderate | `chainRevokeStmt` | In code it is read with today's `authMayReject` and `backendStep`, so R5 and the exact certificate are not in the statement as written. |
| F3 | moderate | `revokeOutcomeIsR`, `revokeClause` | R7 is only partly done: no header. The not-found error is weakened to `≠ nil`/`applyErrIs`, though `Revoke.spec` gives `ErrLeaseNotFound`. |
| F4 | moderate | `deriveRevokeStmt` | Laws it needs: `kvWriter_open` belongs to txn (it unfolds txn's and mvcc's definitions); a size law; `stateAfter_length_le`; a "the deletion clears the lease" law. |
| F5 | minor | `rdAt` | Lives in `apply`, not in the lessor's or mvcc's API (D4-3 only half done); no intro law. |
| F6 | minor | `deriveRevokeStmt` | The lens is a bk-only lens, not `roLens`. That is the right choice, but the docstring calls it "`roLens`'s form". The `RW`/`RO` asymmetry is not stated. |
| F7 | minor | `revokeClause` | Size: `commitLog log (leaseDels (stateAfter log) id)` is written out four times. The not-found branch could state `leaseDels … = []`. |
| F8 | minor | `LeaseItems.lean` | `eq_of_lt_sorted_mem` is a fact about lists and `GoStringLt` (Perennial's). The laws need `hs`, with no `stateAfter` form. |
| F9 | minor | `lessor__Revoke.lean` | One phrase of the docstring is stale; one line is too long. |
| F10 | minor | `authMayRejectR` | The `needAdminPermission` disjunct admits, with auth off, a rejection the method never makes. This looseness was there before; noted for L3c. |

Ranking by need of revision: **`rdAt` > `chainRevokeStmt`/`revokeOutcomeIsR` > `revokeClause` >
`deriveRevokeStmt` > `LeaseItems` vocabulary > `revokePreR`/`revokeRes`/`revokeResAfter` >
`revokeStep`/`authMayRejectR` > `lessor.Revoke.spec`**.

## Round 1's findings, checked in the code

| Round 1 | Fix | In the code at HEAD? |
|---|---|---|
| D3-1 (blocker) | R1 | **Yes.** `lessor__Revoke.lean:55`: the premise is `□ certOkNext γw.st log (leaseDels (stateAfter log) id)`. `:66-69`: the post is at `commitLog log (leaseDels …)`, with no `∃ ks`. The proof's `hD` (`Proof/.../lease/lessor__Revoke.lean:197-201`) identifies the sorted `ks'` by `leaseDelKeys_eq`. The decision entry is at the end of `notes/decisions.md`. Only the server's `Link.lean:2746` uses the spec, so the restatement breaks no caller. |
| D3-2/D4-2 (blocker) | R2 | **Yes.** `rdAt` (`LeaseRevokeDraft.lean:69-71`) has `□ ∀ ws γw, isWatchableStore ws s γw -∗ rdIs rd ws s γw`, without round 1's `⌜γw.st = γ⌝`. That is weaker to supply and enough, because `kvWriter_open` gives `γw.st = γ`. `kvWriter_open` (`LeaseRevokeProbe.lean:40-82`) is proved. But see F1 on the producer. |
| D2-1 (major) | R3 | **Yes.** `revokePreR` (`:122`) takes `putOk log` and no `rqOk`; `rqOk .leaseRevoke = False` stays (`Chain.lean:266`). |
| D5-1 (major) | R4 | **Yes, through `chainStep`.** `chainRevokeStmt` uses `chainStep revokeStep (alarmChain …)`. There `cappedRejects .leaseRevoke = false` (`Chain.lean:143-145`) and `.quota` passes through (`:187`), so no `noSpace` outcome remains. Go agrees: `corrupt.go:53-55` rejects with `ErrCorrupt`; capped and quota do not override the method. |
| D5-2 (major) | R5 | **Defined, not wired in.** `authMayRejectR` (`:53-56`) is right, but `chainStep`'s auth case still reads `authMayReject` (`Chain.lean:182`). F2. |
| D4-1/D3-3 (major) | R6 | **Yes.** `revokeClause`'s not-found branch has `err ≠ nil` (`:93`). `revokeResAfter` (`:113-114`) is `E.RO (if err = nil then restRevoke id rs else rs)`. Every rejected outcome's error is non-nil: `errVarIs` is `err = ok e` (`txn/Write.lean:182`), and `rejErrIs .auth` has `err ≠ nil` (`Chain.lean:739`). So the `if` gives `rs` there, as Go leaves the bucket. |
| D5-3 | R7 | **Partly.** `revokeOutcomeIsR (.applied _ _)` (`:130`) is `⌜resp ≠ null⌝ ∗ applyErrIs err`. It says nothing of the header the plan names ("its header at the revision after"). F3. |
| D1-2/D5-4 | R8 | **Yes.** `leaseDels_mem` and `leaseDelKeys_mem` (`LeaseItems.lean`) are as asked, at a sorted state. |
| D1-1 | — | Deferred: `revokeChanges_eq` is not in the Draft. That is right, since it is L3c's lemma. Note that `KVModelDefs.revokeChanges` (`KVModelDefs.lean:282`) then duplicates `leaseDels` without the `0` guard. At L3c, replace it by `leaseDels` rather than prove the two equal ("drop what existed only for what it changed"). |
| D3-4 | — | The lens is not `roLens`, and rightly so (F6). The docstring needs a fix. |
| D4-3 | — | Half done: one name, but in `apply` (F5). |
| D4-4 | — | **Yes**, in `revokeClause`'s docstring (`:80-81`). |

---

## 1. `LeaseRevokeDraft.lean`

### `revokeStep`, `authMayRejectR`

**Good.**
- `revokeStep` is exact, and it is `backendStep`'s old case with the existential over `pend`
  replaced by a function of the state, as T2 did for put, delete and txn.
- When the lease is not live, the outcome is `applied log false`: `leaseDels` is `[]` because
  `leasesKnown` gives `lease = 0 ∨ ∈ L`. Go returns before any write (`lessor.go:326-333`).
- `authMayRejectR` matches Go:
  - `checkLeasePutsKeys` returns at `IsAdminPermitted(ai) == nil` (`apply/auth.go:208-212`);
  - `IsAdminPermitted` returns `nil` when auth is disabled (`auth/store.go:915-917`);
  - `checkLeasePuts.spec` already states `on.isOn = false → err = nil`
    (`Spec/.../apply/checkLeasePuts.lean:39`).

So the auth layer's no-rejection with auth off is provable from what is there.

**F10 (minor, `authMayRejectR`).** The disjunct `needAdminPermission rq = true` admits an auth
rejection of a revocation with auth off. `authApplierV3.LeaseRevoke` never makes it: the admin
check is in `Apply`, not in the method, and with auth off it passes anyway. The disjunct is false
only for an `IRRModel` that has both `leaseRevoke` and an admin field set.
- This looseness predates the stage (it is in `authMayReject`).
- L3c's deterministic model (`chainLog (.auth _ c) = chainLog c`) must exclude such a request, or
  the disjunct goes.
- *Change (optional):* for a revocation, `authMayRejectR on rq` with
  `dispatchKind rq = .leaseRevoke` reduces to `on = true`. State it as a lemma
  (`authMayRejectR_revoke`) that the auth layer's proof and L3c use. Or restrict the
  `needAdminPermission` disjunct to `dispatchKind rq ∉ {put, range, deleteRange, txn, leaseRevoke}`.

### `rdAt`

**Good.**
- One name for the pair (`rdOwn`, `rdIs`).
- Quantified over the store's name sets, which is how `txn.kv_Write` treats `Write`.
- Not persistent, as `rdOwn` is not; returned by every path.
- `rd ≠ nil` comes through `rdIs`, which rules out Go's `le.rd == nil` early return
  (`lessor.go:338-340`). That return would close `revokec` with no deletion, contradicting the live
  branch.
- This is only sound because the clause also takes `kvWriter` under `γ.watchQ`: with no watchable
  store over `s`, `rdAt` would hold of any `rd`, `nil` included. That is fine, because
  `deriveRevokeStmt` takes `γ.watchQ = true` and `kvWriter`'s `wlogOwn` then provides a store.
  Say so in the docstring.

**F1 (major; a premise with no producer, and a false docstring claim).** The docstring says "the
server's build has it (`mvcc.newWatchableStore`)". It does not:
- `mvcc.New`'s post (`Spec/.../mvcc/New.lean:55`), `newWatchableStore`'s
  (`Spec/.../mvcc/newWatchableStore.lean:58`) and the server's `Results.lean:943`/`BuildLemmas.lean:116`
  all give `∃ rd, rdOwn γl rd ∗ rdIs rd s st γ` at the build's own `γ`.
- `rdAt` needs `rdIs` at every `γw` with `isWatchableStore ws s γw`.
- Getting from one to the other needs either a names agreement, which round 1's D3-2 found no
  lemma for and which I believe is not provable from `isWatchableStore`, or a restatement of the
  producer.

The restatement is true of Go:
- the closure is `func() lease.TxnDelete { return s.Write(traceutil.TODO()) }`
  (`watchable_store.go:107`);
- `mvcc.watchableStore.Write.spec` is `∀ γ`, taking `isWatchableStore s st γ`;
- `ws' = s` follows from `isWatchableStore ws' st γ'` (`txn.watchableStore_unique`'s argument,
  `txn/KVWrite.lean:134`, would move to mvcc).

So `newWatchableStore` and `New` can return `rdAt`'s quantified form, as a strengthening of proved
posts with no axiom.

This is not a blocker for the stage, because F2 (a) makes `rdAt` a premise of the chain. But
`chain_revoke` is unusable until its producer exists, and the plan's L3c ripple does not list it.

*Change:*
- In mvcc, define the persistent half: `mvcc.rdIsAt rd st := □ ∀ ws γw, isWatchableStore ws st γw -∗ rdIs rd ws st γw`.
- Restate `newWatchableStore.spec`/`New.spec` (and `BuildLemmas`/`Results.lean:943`) to return
  `∃ rd, lease.rdOwn γl rd ∗ mvcc.rdIsAt rd st`.
- Define `rdAt γl s := ∃ rd, rdOwn γl rd ∗ rdIsAt rd s`.
- Fix the docstring: "`newWatchableStore` will return it (L3c: today it returns `rdIs` at its own
  names)".
- List the restatement in the plan's L3c ripple, with `Recover`'s fix (F2 of the plan).

**F5 (minor; vocabulary).** `rdAt` is `apply.rdAt` (`LeaseRevokeDraft.lean:69`), built of
`lease.rdOwn` and `mvcc.rdIs`. Its producers (`mvcc.New`, the server's build, later
`lessor.Recover`/`SetRangeDeleter`) are in other packages, which would have to unfold an `apply`
definition to make it ("a client does not unfold another package's definitions"). Round 1's D4-3
put it in the lessor's API.

*Change:* move it to `lease` (beside `rdOwn`, `InvLessor.lean:607`) or to mvcc (with `rdIsAt`,
F1). Export the intro law `rdOwn γl rd ∗ mvcc.rdIsAt rd s ⊢ rdAt γl s` and the elimination at a
watchable store (what `deriveRevokeStmt` uses).

### `revokeClause`

**Good.**
- No `⌜False⌝`, and it is true of Go:
  - **not live**: `ErrLeaseNotFound`, nothing written, `Pre`, `storeWT` and `RO rs` back;
  - **live**: the write transaction opened even with no key, so `Post`, and `storeWT` spent; the
    keys deleted at one revision; `L.filter (· != id)` (`delete(le.leaseMap, l.ID)`); the record
    deleted in the same backend transaction (`UnsafeDeleteLease`, `lessor.go:352-356`), so
    `RO (restRevoke id rs)`; `err = nil`.
- `RO` follows `isCluster`'s pattern, so the clause names no backend.
- Every premise is needed:
  - `putOk` by `rdIs`/`Write`;
  - `storeReader`, `storeWT`, `csContract` by `Write`;
  - `leaseOwn`, `leaseRevokers` by `Revoke`;
  - `leasesKnown` to give it back at `L.filter` and to make the not-found log `log`;
  - the one certificate by the commit.

**F3, the clause's part (moderate; the post says less than the code).** The not-found branch says
`err ≠ nil`. `lessor.Revoke.spec` gives `∃ e, globalAddr ErrLeaseNotFound ↦□ ok e ∗ err = ok e`
(`lessor__Revoke.lean:60-61`), which is `txn.errVarIs lease.ErrLeaseNotFound err`. L3c/L4 maps the
error to gRPC (`togRPCError`: `ErrLeaseNotFound` → `ErrGRPCLeaseNotFound`), and then has to know
which error it is. *Change:* `⌜id ∉ L⌝ ∗ txn.errVarIs lease.ErrLeaseNotFound err ∗ …`. It implies
`≠ nil`; keep the top-level `applyErrIs err`.

**F7 (minor; size and caller burden).**
- `mvcc.commitLog log (mvcc.leaseDels (mvcc.stateAfter log) id)` appears four times in the clause
  (`:90`, `:97`, `:99`, `:102`), and again in `Revoke.spec`. *Change:* name it in mvcc,
  `mvcc.revokeLog log id`, with its `proj`/unfold law; or use `let log' := …` in the post.
- The not-found branch returns `kvWriter … log`. The backend then has to prove
  `commitLog log (leaseDels …) = log` itself (from `leasesKnown`, `leaseDels_none`) to give
  `kvOwn E (oc.logAfter log)`. The derivation proves it anyway. *Change:* add
  `⌜mvcc.leaseDels (mvcc.stateAfter log) id = []⌝` to the not-found branch.

### `revokeRes`, `revokeResAfter`, `revokePreR`

**Good.**
- `revokeRes` is the footprint beside `mPre`: the range deleter and the rest at `rs`.
- `revokeResAfter` is deterministic (R6) and gives the range deleter back.
- `revokePreR` is `putPre`'s shape with `putOk`, and has no `rqOk` (R3).
- Taking `E.RO rs`, the whole rest model, is an aggregate. It is the indexed one `isCluster` and
  `dispatch.spec` already take, whose effect is a named function (`restRevoke`, `revoke_bk` and
  `restRevoke_mem` both `rfl`, `RestLease.lean:53-59`). A new bucket does not change the text.
  Accepted, as in round 1.
- The margin (not live versus live with no key) is stated in `revokeResAfter`'s docstring.

No finding.

### `revokeOutcomeIsR`

**F3, the answer's part (moderate; R7 partly done, the margin unstated).** The applied case is
`⌜resp ≠ null⌝ ∗ applyErrIs err`.
- Go: `&pb.LeaseRevokeResponse{Header: a.newHeader()}` (`apply/backend.go:94-97`), whatever the
  error; `newHeader` reads `KV.Rev()` after the deletion (`backend.go:306-313`).
- The v3rpc handler L4 will reach (`LeaseServer__LeaseRevoke.lean`) consumes a header owned at a
  revision (`leaseHdrAns`: `h`, `rv`, the writable fields `Hw`, `0 < rv`), then calls `header.fill`.
- The docstring says "its header: `newHeader`'s, not nil", but the statement has neither the header
  nor that it is non-nil. `newHeader.spec` gives only `h ≠ null`
  (`Spec/.../applierV3backend__newHeader.lean:31-35`), so the header's revision is not available
  without strengthening that spec.
- Separately, `applyErrIs err` loses which error came back (see the clause's part).

*Change:*
- Applied case: `⌜resp ≠ null⌝ ∗ applyErrIs err ∗ (⌜err = GoInterface.nil⌝ ∨ txn.errVarIs lease.ErrLeaseNotFound err)`.
  The error is free from the clause.
- Either add the header as `putAnswerIs` does (`appliedHdr log' (structFieldRef LeaseRevokeResponse "Header" resp)`,
  which needs `newHeader.spec` to give `respHdrOwn` and the revision), or state in the docstring
  that the header is the margin, left to L4, and why (`newHeader.spec`). Then fix the docstring to
  what the statement says.

### `chainRevokeStmt`

**Good.**
- `chain_put`'s shape (`apply/Results.lean:213-224`): outcome, answer, `kvOwn` at `oc.logAfter log`,
  `chainRes`, `Post ∨ Pre`, `revokeResAfter`, and the class under `authPassed oc`.
- The lease class is at the item map before the call. That is right: `checkLeasePuts` runs before
  the backend (`auth.go:191-195`).
- With `leaseDels_mem`, a client gets "every deleted key was writable by the principal" without
  unfolding. That is the stage's goal.
- **Provable from the layers.** Each layer's step is available:
  - `corrupt`: `nil, ErrCorrupt`; `revokeRes` back at `err ≠ nil`.
  - `capped`/`quota`: promoted methods (`newApplierV3Capped.lean:156`, `newQuotaApplierV3.lean:158`),
    which pass the call on.
  - `auth`: `checkLeasePuts.spec` with `kvOwn_lend`'s `lessorUser` and `RD`
    (`Chain.lean:448`). On rejection, `rejErrIs .auth`. On `err = nil`, `leaseKeysClass` at
    `leaseItemsOf (stateAfter log)`, that is `reqLeaseClass .leaseRevoke` (`AuthClass.lean:552`).
    With auth off, `err = nil`.
  - `backend`: the clause (below), `certPre_backend_applied` + `certOkNext_of_commitLog`
    (`Chain.lean:905-930`), and `newHeader` for `resp ≠ null`.
  - The chain's step: `chainClass_alarm` (`Chain.lean:578ff`), `chainLeaseClass_alarm` (`:692`),
    and a `chainStep_alarm_revoke` as `Results.lean:106-170`.
- What it needs: `applierTriples`' LeaseRevoke row (`Chain.lean:1277-1282`) restated at
  `revokePreR`/`revokeResAfter`/`revokeOutcomeIsR`, and the three methods' specs restated (D6).

**F2 (moderate; the statement in code is not the intended one).**
- `chainRevokeStmt`'s outcome is `chainStep revokeStep (alarmChain …)`. `chainStep`'s auth case
  reads `authMayReject` (`Chain.lean:182`), not `authMayRejectR`. So, as written, the statement
  admits an auth rejection with auth off: R5 is not in it.
- Its precondition's `certPre` is `chainStep backendStep` (`Chain.lean:859-861`) with today's
  `backendStep` (`∃ pend`, `:226`). As written, it therefore asks the certificate of every log of
  deletions: D3-1's unsuppliable premise, again.
- Both resolve at Prove ("the definitions replace their counterparts", the file's header). But a
  reviewer, the tester and the user cannot check the Draft's statement as the one that will be
  proved. A `Prop` that reads definitions about to change is not frozen.

*Change, either:*
- (a) In the Draft, define `backendStepR` (`backendStep` with the case replaced), `chainStepR`
  (`chainStep` over `authMayRejectR`), and `certPreR`, and state `chainRevokeStmt` and `revokePreR`
  with them.
- (b) Add the Draft-level lemma that the final reading of each is the one meant, for example
  `chainStep revokeStep (alarmChain false ns cr) rq log oc → oc ≠ .rejected .auth` with
  `authMayRejectR`. Say in the header which statements read definitions still to be replaced.

(a) is more honest and cheap.

### `deriveRevokeStmt`

**Good.**
- The premises are what the server can supply: `γ.watchQ`, the two package inits, `lessorInv`,
  `hookOk`, and a lens on `RO`. Every premise is persistent, as the `□` clause needs.
- It takes `lease.lessor.Revoke.spec` only.

**Provable, resource by resource.** I traced each against the definitions.

- **`storeRb`/`lessorBeOn` through `RO`.**
  - The lens at `rs` gives `d`, `γ.kb = some d`, `storeRb γ rs.bk`, `lessorBeOn lp d.be` and the
    wand.
  - `Revoke.spec` takes `γw.st.kb = some d` (`γw.st = γ` from `kvWriter_open`) and `r := rs.bk`.
  - Not live: `storeRb γ r` back, and the wand at `rs.bk` gives `RO {rs with bk := rs.bk}`, which
    is `RO rs` by structure eta.
  - Live: `storeRb γ (rbDel r leaseName (u64Le id).reverse)`, which is `(restRevoke id rs).bk`
    (`revoke_bk`, `rfl`), and `.mem` is unchanged (`restRevoke_mem`, `rfl`). So the wand gives
    `RO (restRevoke id rs)`.
  - `lessorBeOn` comes back in both branches (`lessor__Revoke.lean:58`).
  - It is sound: `le.b` is the store's backend (`lessorBeOn lp d.be` at `γ.kb`'s `d`), so the
    record's delete goes to the bucket `RO` tracks.
- **`watchWriter` through `kvWriter_open`.**
  - Opening at `X ws γw := rdIs rd ws s γw` (persistent, `InvWatchStore.lean:1856`) gives `ws`,
    `γw` with `γw.st = γ`, `soleLog log`, `rdIs rd ws s γw`, `watchWriter γw log`, `writerFrag γ`,
    and the closing wand at any `log'` with `soleLog log'`.
  - Closing: `soleLog (commitLog log _)` is `txn.soleLog_commit` (`SoleWriter.lean:66`); the
    certificate comes from `watchWriter`'s own `idxCert` (the probe's `Hc'`).
- **`hookIs` from `hookOk` plus `writerFrag`.**
  - `hookIs γ P f` is `hookOk γ P f ∗ writerFrag γ` (`InvStore.lean:1031`, `hookIs_split`).
  - `Revoke.spec` returns `hookIs` in both branches (`lessor__Revoke.lean:58`). Splitting it gives
    `writerFrag γ` back for `kvWriter`.
- **`rdOwn`/`rdIs` through `rdAt`.**
  - `rdAt γ.leases s` gives `rd`, `rdOwn γ.leases rd`, and the `□ ∀` instantiated by
    `kvWriter_open`.
  - `Revoke.spec` takes `γw.st.leases = γl`, which holds since `γl = γ.leases`. It returns
    `rdOwn γl rd`, which with the `□` part refolds `rdAt` (it is persistent).
- **`log.length + 4 ≤ 2^63`** is `putOk`.
- **`(stateAfter log).length ≤ 2^62`.** It follows from `soleWriter_small'`
  (`SoleWriter.lean:100`: `logCh log < 2^48`) and a `stateAfter_length_le : (stateAfter log).length ≤ logCh log`.
  - That lemma is not written. It is true: `applyChange` adds at most one entry per change, since
    `putKv` inserts or replaces and `.del` filters (`Model.lean:108-121`).
  - `kvWriter_open` drops the sole writer's facts, so the bound must be taken before opening, which
    means unfolding `kvWriter` again (F4).
- **`leasesKnown` after the deletion.** It is pure:
  - every `v` in `stateAfter (commitLog log (leaseDels (stateAfter log) id))` is a `v` of
    `stateAfter log` whose key is not deleted (`txn.stateAfter_commitLog`, `.del` filters);
  - if `v.lease = id ≠ 0`, its key is in `leaseDelKeys`, so it was deleted;
  - hence `lease ≠ id`, and `leaseOk L` becomes `leaseOk (L.filter (· != id))`;
  - for `id = 0`, `leaseDels = []` and `0` is always `leaseOk`.
  It needs no sortedness, but the law is not written (F4).
- **The error.**
  - Not live: `errVarIs ErrLeaseNotFound` gives `err ≠ nil` (`ok e`) and `lessorErrIs`
    (`InvLessor.lean:591`), hence `applyErrIs` by `lessorErrIs_applyErrIs`
    (`LessorDerive.lean:41`; `isPkgInit` lease is a premise).
  - Live: `err = nil`, `applyErrIs_nil`.
- **The certificate** is passed through unchanged (the same `leaseDels` term).

**F4 (moderate; laws the derivation and its neighbours need, not yet written).** All are small and
none is in doubt, but each is a missing law of its owning package:
- `kvWriter_open` unfolds `txn.kvWriter`, `txn.soleWriter`, `mvcc.watchWriter`, `mvcc.wBudget`,
  `txn.soleBudget` (`LeaseRevokeProbe.lean:48-77`) from `apply`. *Change:* move it to txn
  (`txn/KVWrite.lean`, beside `wlogOwn_watch`), and add `⌜logCh log < 2 ^ 48⌝` (or the state bound
  directly) to its result, so that the derivation needs no second unfold.
- `mvcc.stateAfter_length_le` (`mvcc/LogLemmas.lean`, D2's) and the corollary
  `(stateAfter log).length ≤ 2^62` under `logCh log < 2^48`.
- `mvcc.leaseDels_clears : v ∈ stateAfter (commitLog log (leaseDels (stateAfter log) id)) → id ≠ 0 → v.lease ≠ id`
  (in `LeaseItems.lean`). The derivation and L3c's model both need it.
- (optional) `txn.leasesKnown_revoke` built on it, so that apply does not unfold `leasesKnown`.

**F6 (minor; the lens's docstring).** The lens is
`□ ∀ rs, RO rs -∗ ∃ d, ⌜γ.kb = some d⌝ ∗ storeRb γ rs.bk ∗ lessorBeOn lp d.be ∗ (∀ bk, … -∗ RO {rs with bk})`.
That is *not* `roLens` (`InvRest.lean:395`): `roLens`'s wand is `∀ r', X r' -∗ RO r'`, which would
let the members change for free unless `X` also owned `clusterMem`, as the cluster's lens does
(`SnapApplyOptsLemmas.lean:84-97`). The draft's bk-only form is weaker to supply, and the server
can supply it: lend `rbOwn` and `srvObjsOn`'s `lessorBeOn`, keep `clusterMem` in the wand. So round
1's D3-4 suggestion was wrong, and the draft is right not to follow it.

*Change:*
- Say in the docstring that this is a bk-only lens, unlike `roLens`, and why.
- Give it a name (`roBkLens RO X`) if L3c's grant will take the same one.
- Also state the asymmetry round 1 asked for: `Grant`/`Checkpoint` write the bucket through `RW`
  and `Revoke` through `RO`, deliberately, until grants are admitted.

---

## 2. `lessor.Revoke.spec` (restated)

**Good.**
- **True of Go.** Each key is `txn.DeleteRange([]byte(key), nil)` in sorted order
  (`lessor.go:342-349`), and `leaseDels` is the state's filter in key order. `leaseDelKeys_eq` (no
  duplicates and `GoStringLe`-sorted, hence strict) identifies the two, and the proof does so
  (`hD`).
- **Stronger for every caller.** The premise is one certificate instead of a `∀`, and the post is
  determined (no `∃ ks`).
- No axiom moves, and the only use is the linking file (`etcdserver/Link.lean:2746`).
- The not-found case needs a certificate the caller always has: `certOkNext γ log []` is trivially
  true, and in general it comes from `certPre` for the outcome.
- No internals added: `leaseDels` is mvcc vocabulary over the state.

**F9 (minor; the docstring).**
- `:30-31`: "and the certificates of a commit of deletions" should now be "the certificate of its
  deletions' commit".
- `:37` is over-long. The history clause ("until then some sorted `ks` …") belongs in
  `decisions.md`, which has it.

---

## 3. `LeaseItems.lean`: `leaseDelKeys`, `leaseDels` and their laws

**Good.**
- The `0` guard is needed: `kvLease` maps lease `0` to no item, and without the guard every key
  without a lease would be deleted.
- `leaseDelKeys_mem`/`leaseDels_mem` give exactly the client's law (R8).
- `leaseDels_isDel` and `leaseDelKeys_sorted` are what the proofs use.
- `findKey_iff_sorted` and `sorted_key_unique` are general and correct.

**F8 (minor).**
- `eq_of_lt_sorted_mem` (two strictly `GoStringLt`-sorted lists with the same members are equal)
  is a fact about lists and Perennial's `GoStringLt`. By CLAUDE.md ("There is no `Proof/Lib/`"),
  it belongs in Perennial, generalised to any strict order. *Change:* keep it here for now, and
  record it in `notes/perennial-changes.md`.
- `sorted_key_unique` and `findKey_iff_sorted` are about the state model and fit
  `mvcc/LogLemmas.lean` (beside `stateAfter_sorted`) better than the lease file.
- Every law takes `hs : s.Pairwise etcdKvLess`, and every client applies it at `stateAfter log`.
  *Change:* add `leaseDels_mem_stateAfter` (with `stateAfter_sorted` supplied), so that the
  client's glue is one line.
- Add `leaseDels_clears` (F4) and `leaseDels_none` (now a probe) as laws here.

---

## Bugs in the Go code

None new. Go's behaviours the clause relies on, or rules out, are already filed:
- `le.rd == nil` with a double revoke: `nonissues/etcd-lessor-revoke-twice-no-deleter.md`;
- `le.rd` read outside the lock: `nonissues/etcd-lessor-revoke-rd-unlocked.md`.

The false statement of this repository's `lessor.Recover` axiom (the plan's F2) is in
`notes/audit.md`, correctly in `notes/` rather than `issues/`.

## Ranking by need of revision

1. **`rdAt`**: F1 (no producer; the docstring claim is false; L3c must restate
   `New`/`newWatchableStore`) and F5 (move it to lease or mvcc, with laws).
2. **`chainRevokeStmt` / `revokeOutcomeIsR`**: F2 (read with definitions still to be replaced) and
   F3 (the header and the not-found error).
3. **`revokeClause`**: F3's `errVarIs ErrLeaseNotFound` and F7 (a name for the log; `leaseDels = []`
   when not live).
4. **`deriveRevokeStmt`**: provable. F4 (four laws, `kvWriter_open` moved to txn) and F6 (the lens's
   docstring and the `RW`/`RO` asymmetry).
5. **The `LeaseItems` vocabulary**: F8.
6. **`revokePreR`, `revokeRes`, `revokeResAfter`**: no finding.
7. **`revokeStep`, `authMayRejectR`**: F10 (optional).
8. **`lessor.Revoke.spec`**: F9 (docstring only).
