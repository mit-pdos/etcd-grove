# Batch 3b, review round 1 (provability and completeness)

Reviewer: independent of the author. Under review: `HEAD` = `9ca5a40087` (3b's files last changed
in `ce20d0f6d7`; round 1, so no finding is stale). Read: `notes/specs-only/{README,review-brief,
batch-3b,batch-3e}.md`, the spec skill's `PRINCIPLES.md`, all of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/` (Api and the 47 specs), `examples/specreq/txn/`,
W0's `Spec/go_etcd_io/etcd/api/v3/{Model,Wire}.lean`, **3e's written API**
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/{Model,Api}.lean`), 3c's `lease/Api.lean` (the
`LessorState` record and steps), 3a's `apply/{Api,applierV3backend__Txn}.lean`, 2c's `ApiReq.lean`
(`txnChecked`), the `req/` sections from and to 3b, and the Go code (etcd `a4d2bb17`:
`server/etcdserver/txn/*.go`, `storage/mvcc/{kvstore_txn,index,kvstore}.go`,
`etcdserver/v3_server.go`, `etcdserver/apply/*.go`, `api/v3rpc/key.go`, `pkg/traceutil/trace.go`,
`client/v3/op.go`, `proxy/grpcproxy/adapter/kv_client_adapter.go`). No build was run.

## Verdict

The semantic core is good: `rangeOut` follows `executeRange` step by step (pushed-down limit
before the filters and the sort, the sort-none quirk, count truncated at the pushed-down limit
without `withTotalCount`, lease `0` on the fast keys-only path, `More` from the response's own cut);
`run`/`execOps` follow `checkTxn`/`executeTxn` (nested verdicts at the read view, ranges at
`beginRev` or `beginRev+1`, prevKV from the in-transaction store, the skip path's header revision);
`txnSafe` is a sound state-free sufficient condition, and the write `Txn`'s pin is a premise the
apply thread can establish (it is mvcc's only writer: compaction, revocation and restore all run on
it; the background compaction does not change the history). The ctx-never-done premise of a
writing `Txn` is exactly what keeps `txn.go:91`'s `lg.Panic` unreachable.

**Not done.** Five first-tier findings: (F1) the specs are unsound against W0's request predicates
as they stand at `HEAD` for a non-`nil` empty `RangeEnd`, and the requested fix rests on a false
claim; (F2) the fast keys-only path with a sort cannot be proved against the opaque `goSort`;
(F3) `checkRange`/`checkTxn` are false at a write transaction; (F4) the write specs' single update
cannot be fed to 3e's written two-step `End` (and the other slots differ from 3e's API in
statement-changing ways: state type, reader tokens, trace ownership, writer resources); (F5)
`errIs` has no law tying it to the Go sentinels, so two snippets and the callers' error mapping are
unprovable. No Go bug found (nothing to add to `issues/`).

## First tier

### F1. A non-`nil` empty `RangeEnd`: the range specs are unsound at `HEAD`, and the requested premise is the one the old proof rejected

*Principle*: sound, true of the code at every input the pre admits; every premise has a source
the caller sees.

*Evidence.* mvcc reads a `nil` end as the key alone and a non-`nil` empty end as unbounded
(`storage/mvcc/index.go:116`, `:99`: `len(endi.key) > 0`). `mkGteRange` passes any end other than
`"\x00"` through (`txn/delete.go:63-68`). W0's `KeyRange.mem` reads `rangeEnd = []` as the key
alone (`Model.lean:103-106`), and W0's unfold laws relate the request's end slice to its content
only (`Wire.lean:275`, `:310`, `:342`: `es ↦*□ r.rangeEnd`), so a non-`nil` empty slice satisfies
`rangeReqOwn` with `rangeEnd = []`. Then `Range.spec` answers the one key while Go answers
`[key, +∞)`; likewise `DeleteRange.spec` (deletes every key from `key` on), and `Txn.spec` through
`applyCompare`, `executeRange`, `deleteRange` and `txnSafe` (`opDelRanges` reads the delete as a
point, so a delete-then-ignore-put on a later key is admitted and panics, `put.go:55`).
3b's fix is a request to W0 (`req/go_etcd_io_etcd_api_v3.md`, "from 3b": `rangeEnd = [] → es =
slice.nil`), not adopted at `HEAD`. Its justification "a client builds none other" is false:
`clientv3.WithRange("")` sets `op.end = []byte("")` (`client/v3/op.go:440`, non-`nil`), and an
embedded server's `v3client` passes the struct unmarshalled to the server
(`grpcproxy/adapter/kv_client_adapter.go:33-34` → `EtcdServer.Range` → `txn.Range`). The old proof
considered exactly this premise and rejected it ("it would sit on every KV spec"), reading a
non-`nil` empty end as open (`specs-ref/notes/decisions.md:16676-16685`, "The range end as the check
sees it"). 3e's API already models the distinction (`Mvcc.MRange.endNil`, `mrange`).
`Count.spec` alone states its own premise (`⌜e = [] → rend = slice.nil⌝`), so the batch is also
inconsistent with itself.

*Callers affected*: 2c (`EtcdServer.Range`/`Txn` over in-process requests), and any client spec
that builds a range with `WithRange`.

*Restatement.* Do not ask for the premise. Either (a) W0's unfold laws map the slice to the model
as mvcc reads it (a `nil` end ↦ `[]`; a non-`nil` empty one ↦ `[0#8]`, which `KeyRange.mem` already
reads as "from the key on", and which `mkGteRange` would produce from it anyway), so every request
predicate's `rangeEnd` is mvcc's reading and no spec needs a premise; or (b) 3b states its answers
over 3e's `MRange` of the slice actually passed. (a) is local to W0 and keeps 3b's text. Then drop
`Count.spec`'s premise. (The auth store's point reading of the same slice differs; the old
decision's `authEndOf` handled it; that is 3d's.)

### F2. The fast keys-only path with a sort is unprovable against the opaque `goSort`

*Principle*: sketches plausible (every step from a callee's post); a spec is true of the code.

*Evidence.* On the fast keys-only path (`KeysOnly ∧ SortTarget ≠ VALUE`) mvcc's key-values have no
value and lease `0` (`kvstore_txn.go:96-104`; 3e: `keysOnlyM`, value `[]`), and
`sortRangeResults` sorts *those* (`range.go:131-152`); `asembleRangeResponse` then clears values
(`range.go:166-168`). `rangeOut` (`Api.lean`, `rangeOut`) sets only `lease := 0` before the sort,
so `executeRange.spec` must show `(goSort t d L).map eraseValue = goSort t d (L.map eraseValue)`.
`goSort` is opaque with only `goSort_sorted` (a sorted permutation), so this does not follow
(equal-key elements may be placed differently by an arbitrary sorted-permutation function). Real
input: `etcdctl get --prefix --keys-only --sort-by=MODIFY`. The same holds for `rrOwn`
(`KeyValueM.ofKV kv` cannot describe a `keysOnlyM` record with a non-empty `kv.value`).

*Callers affected*: `Range.spec`, `Txn.spec` (a nested keys-only sorted range), 2c's registry and
3a's determinism.

*Restatement.* In `rangeOut`, the fast path maps `fun kv => { kv with lease := 0, value := [] }` (the
answer is unchanged: `assemble` clears values whenever `keysOnly`, and `rangeOut_answers` stays
true since keys are unique). Optionally add the general law for Perennial's functional sort
(`goSort t d (l.map f) = (goSort t d l).map f` for an `f` preserving `targetLt t` both ways), which
the functional `sort.Sort` spec should give anyway (`notes/perennial-changes.md`, 2026-11-09).

### F3. `checkRange.spec` and `checkTxn.spec` are false at a write transaction

*Principle*: sound at every input the pre admits (an internal spec too).

*Evidence.* `store.Write` builds `storeTxnCommon{s, tx, 0, 0, trace}` (`kvstore_txn.go:179`), so a
write transaction's `FirstRev()` is `0` (3e's `Txn.FirstRev.contract`). `checkRange`
(`range.go:174-184`) then never reports `ErrCompacted` for a positive revision below the compaction.
`checkRange.spec` and `checkTxn.spec` quantify over any `k : TxKind` and claim `rm.txnRevErr h`,
which says `compacted`. Go's own callers pass only the read transaction (`txn.go:54`), so `Txn` is
unaffected (3e's warning that "3b's checks meet" this is moot for `Txn`, but not for these two
statements).

*Restatement.* Take `k = .read` (or `.read`/`.roWrite`) in `checkRange.spec` and `checkTxn.spec`
(with 3e's names, `mvccTxn rv γ tr (.read σ)`).

### F4. The provisional mvcc slots do not match 3e's written API, and the write specs cannot be proved from it

*Principle*: sketches plausible against the callee specs when they exist (review brief,
Provability 3); the user's decision on reader tokens (3e's report, 2026-11-07).

*Evidence* (3e's `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, present at `HEAD`):

1. **Commit in two steps.** `Txn.End.contract` (`Api.lean:487-505`) and `KV.Put.contract` take a
   *nested* update: notify (`mvccState γ (σ.notify pend)`), then the bump (`σ'.commitPending`).
   3b's `Put`/`DeleteRange`/`Txn` take one update `<{ mvccState γ h }> <{ mvccState γ (next h) }>`
   and their sketches say `End` "fires the caller's update". One atomic update cannot serve both
   steps: after the first, the state is `σ.notify pend`, which is neither the update's
   precondition (an abort must restore the same state) nor its postcondition. (3e's report says
   "the caller passes its one through both": I do not see how; with `pend = []` both steps are
   no-ops and peeks suffice, but not otherwise.)
2. **The state** is `MvccState = {kv, pending}`, not `KVHist`; a read may begin while a revision
   is pending and reads `σ.kv` (`mvccTxn_state`'s comment).
3. **Reader tokens**: `Read`, `Write`, `Range`, `Rev` take `mvccReaders γ 1` (the user's decision of
   2026-11-07); 3b's specs take `threadTok`.
4. **The trace** is exclusive (`traceOwn trace`, `⌜trace ≠ null⌝`) in `Read`/`Write`/`Txn.Range`;
   3b's is persistent (`traceAt`). `EnsureTrace` returns the *caller's* trace when its context has
   one (`trace.go:102-111`; `EtcdServer.Range` and `Txn` set one first, `v3_server.go:118`, `:341`),
   so with exclusive traces `Range`/`Txn` need the caller's trace ownership in their pre, which
   nothing in 3b's statements provides. (A persistent `traceAt` whose methods "never panic" is
   itself doubtful: `Trace.Step` appends without a lock, `trace.go:145-149`; uncertain how Goose's
   model treats such a race. 4b's call.)
5. **Writer resources**: `mvccWriter γ` is 3e's `mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗
   hookRun Pk f Pre Q ∗ (Q ={⊤}=∗ Pk ∗ Post)`; `mvccKV` is `isMvcc` (which contains
   `Lease.isLessor`), `mvccLessor` is `mvccLessorIs`; `mvccTxn tx γ k h evs` is
   `mvccTxn t γ trace (k : MTxn)`.

Items 2, 3 and 5 are renamings with work; items 1 and 4 change what 3b's statements say to their
callers (3a's `applierV3backend.*`, 2c's `EtcdServer.Range/Txn`), so they belong in this round,
not at integration.

*Restatement.* State the write specs with 3e's shape: the caller's update nested as `KV.Put`'s is
(notify at `σ₀` with `σ₀.pending = []`, then the bump), over `MvccState`, with the pin `σ = σ₀`
for a writing `Txn`; the check-failure paths fire both steps as no-ops. Reads over `∃∃ σ,
mvccState γ σ` with the answer at `σ.kv`. `mvccReaders γ 1` for `threadTok`. Agree with 4b on
the trace (if exclusive, `Range`/`Count`/`Txn`/`Put`/`DeleteRange` take the context's trace,
`traceAt`-of-ctx or `traceOwn`, and give it back). To keep the storage contract out of txn's
client-facing statements, a transparent bundle `txnWriter γ Post` (3b's) for the backend share,
hook and `Pre`, unfolding to 3e's.

### F5. `errIs` cannot be eliminated: the error snippets and the callers' error mapping are unprovable

*Principle*: a predicate a client would have to unfold is a missing law; snippets provable.

*Evidence.* `errIs err e` is opaque with laws `persistent`, `ne_nil`, `agree`, `ctxErr_not_errIs`
only (`Api.lean`). Nothing says `err` is the value of mvcc's `ErrCompacted`, lease's
`ErrLeaseNotFound`, ... So `errors.Is(err, srverrors.ErrKeyNotFound)` in `ReqApplyPutIgnoreValue`
and `errors.Is(err, lease.ErrLeaseNotFound)` in `ReqApplyPutLeaseCheck` cannot be evaluated: both
snippets are unprovable. The same holds for 2c's `togRPCError` (maps by identity with the
sentinels) and for 3a's results, which the batch defers to "integration laws". 3e already states
its errors this way (`rangeResOwn`: `globalAddr ErrCompacted ↦□ err`).

*Restatement.* Make `errIs` transparent:
`errIs err e := match e with | .compacted => globalAddr mvcc.ErrCompacted ↦□ err | .futureRev => …
| .leaseNotFound => globalAddr lease.ErrLeaseNotFound ↦□ err | .keyNotFound => globalAddr
errors.ErrKeyNotFound ↦□ err | _ => False` (with the owners' `init` laws giving distinct non-`nil`
values), or keep it opaque with an intro/elim law of that form. `errIs_agree`/`ne_nil` then follow.

## Second tier

- **S1. Snippets cite laws 3b's vocabulary does not give.** `ReqRangePinnedRev` needs "every record
  of `storeAt rev` has `modRev ≤ rev`", `ReqApplyTxnCAS` "a present key's `modRev ≠ 0`": both are
  facts of a reachable history (3e's `mvccState_reachable`, `MvccReachable`/`EvsWf`), absent from
  3b's provisional item 7. Cite 3e's law in the snippets' `Specs:` lines (provable with it).
- **S2. Uncovered patterns** (completeness). (a) A sorted / keys-only / filtered range whose order
  the caller relies on (2c's registry and 3a's `kvStep` rely on `rangeOut_answers`; no snippet
  exercises it, which is why F2 went unnoticed): e.g. `SortTarget: MOD, SortOrder: DESCEND,
  KeysOnly: true` and a panic on an increasing pair or a non-zero lease. (b) A `Txn` whose check fails
  (a range below the compaction, or a put on a dead lease) writing nothing and returning the
  sentinel (3a's error results). (c) `DeleteRange` with `PrevKv` (3a's `apply`, the client's
  `WithPrevKV`). (d) The uber applier's `WarnOfExpensiveRequest`/`WarnOfFailedRequest` with
  `&pb.InternalRaftStringer{...}` and `ar.Resp` (`uber_applier.go:98-101`): its `msgOpt` depth premise
  is a real precondition, worth one "the pre can be met" snippet.
- **S3. The lessor post is weaker than mvcc's and names 3c's fields.** `sameLeases` mentions
  `bkt`, `be`, `rd` of `Lease.LessorState`, and `∃ ls', sameLeases ls ls' ∧ attached …` leaves the
  item sets of dead lease objects (`ls'.keys o` for an `o` no live lease names) unconstrained, where
  3e gives the exact state (`putLs`, `delsLs`). Either give the exact state (a pure function of the
  events: `evsLs ls evs`, the fold of 3e's steps) or state this as the margin. 3a's
  `lessorSt` only needs `attached`, so the margin is probably harmless; say so.
- **S4. `DeleteRange.spec`'s `Lease.isLessor leL γl c`**: `leL`, `c` occur only in the pre (the code
  gets the lessor through the store). With 3e, `isMvcc` contains it: drop the conjunct.
- **S5. `txnSafe` is stricter than the code needs** (both branches, nested ones, any delete that
  *may* cover the key, a known sort target even on untaken ranges). Justified (state-free, so the
  gRPC check can give it; the path-exact form stays internal in `executeTxn.spec`), but the
  docstring calls it what the code needs "at every state": say "a state-free sufficient condition"
  and name the exact one as the margin.
- **S6. The pin's composition** (for 3a/2d, not a 3b defect). The pin `h = h0` needs the apply thread
  to hold an authority over the store's state while 2c's reads fire their updates over the same
  `mvccState` concurrently. 3a's draft holds `kvSt kv h` exclusively (`apply/Api.lean:595`), which
  would leave 2c's readers no update to fire. Note it in the batch's open questions.
- **S7. `run_txnRun`/`rangeAll`** are fine (every `KVHist`'s stores have finite support, so
  `rangeAll` is the real list), but `rangeAll`'s docstring "`[]` if none exists, which no store of a
  reached history is" undersells it: no store of *any* `KVHist` is. Minor.
- **S8. The warnings' `err`**: `zap.Error(err)` reaches `err.Error()`; the specs take any `err`. True
  if W0's zap spec makes `Error` safe for any error value; uncertain, W0's.

## Per target

### `Api.lean` (vocabulary)

Good: transparent, code-faithful models (`rangeLimitZ`, `sortOut`, `assemble`, `rangeOut`,
`execOps`, `opPath`); the laws `rangeOut_answers`, `run_txnRun` connect the functions to W0's
relations at exactly the validity W0 needs; `txnSafe`'s three clauses each match a panic
(`txn.go:143` nil response for an empty op, `range.go:145`, `put.go:55`), and checkIntervals with
the fork's fix (`api/v3rpc/key.go:236-311`: this level's and nested deletes against every put)
does give the third. Findings: F1 (requested premise), F2 (`rangeOut`), F4 (slots), F5 (`errIs`),
S3, S5, S7.

### `Txn.lean`

Good: one spec for both modes (the pin a case split on the input, not a disjunction of specs); the
error branch's `resp = null ∧ tr = null` (`txn.go:57`); the read-only context error with the partly
filled response (`roTxnResp`, `txn.go:93`, `v3_server.go:359`); `runRev` = `Rev()+1` iff changes
(`txn.go:96-99`). Findings: F4 (single update vs two-step `End`; reader token; trace), F1 (through
the operations). Callers: 3a's `applierV3backend.Txn` (needs F4 settled), 2c's read-only path
(serves it once F4.2-4 are done).

### `Put.lean`, `DeleteRange.lean`

Good: the lease check before the write transaction (`put.go:35-39`) handled as a no-change firing
at the writer's lessor state; `putAns`/`putHist` exactly `PutReq.check` then `record`; prevKV and
the ignore flags right; `DeleteRange`'s context error only with `PrevKv` and before any delete
(`delete.go:44-55`), the update given back. Findings: F4.1 (the given-back update needs `End`'s
steps as no-op peeks; fine for `pend = []`, but the success path needs the nested form), F4.3, S4,
S3, F1 (`DeleteRange`).

### `Range.lean`, `Count.lean`, `executeRange.lean`, `sortRangeResults.lean`, `rrOwn`

Good: the three outcomes as in `rangeKeys` (`kvstore_txn.go:73-151`), the context error only where
mvcc checks it (`Count`: none, `CountRevisions` checks none), header `h.rev`, count semantics
including `min all L` (`index.go:123-136`). Findings: F2, F1, F4.2-4.

### `checkRange.lean`, `checkTxn.lean`

F3. Otherwise mirror the code (first error, the path's sliding window counted).

### `put.lean`, `deleteRange.lean`, `executeTxn.lean`, `txn.lean`, `newTxnResp.lean`, compares

Good: the ignore-key presence carried as a premise and kept across the branch by `opsSafe`; the
lease to attach live (checked, or the previous record's by `attached`); nested verdicts at the read
view (`compareToPath` on `txnRead`); `compareKV` matches `Compare.holdsOf` including unknown targets
and results and a mismatched `TargetUnion`. Only F4 (the slots) applies.

### Helpers and warnings (`IsTxnReadonly`, `IsTxnSerializable`, `IsDefaultOrdering`, `HasRevisionFilters`, `Warn*`, `*SecObserve`, `isNil`, `kvSort*`)

Good: W0's `readonly`/`serializable` match `GetRequestRange` (a nested transaction is a write); the
`Less` specs are the signed order without overflow for values in `[0, 2^63)` (`kvFits`); the
warnings take the response's content and depth (`msgOpt`) rather than "any response", which 3a asked
for and which would be false (`proto.Size` recurses per level). S2(d), S8.

### Snippets (`examples/specreq/txn/`)

Proof sketches: `ReqRangeLimitCount`, `ReqCountOnly`, `ReqRangeStreamPages` (the caller keeps a
monotone record of the history in its invariant so that `Count` at `rev` reads the same
`storeAt rev`; an error after a later compaction is returned), `ReqTxnReadOnly`,
`ReqApplyPutThenRange`, `ReqApplyDeleteRange`, `ReqApplyTxnSkip`, `ReqReadonlyKinds`,
`ReqSortHelpers` are provable from the specs (given W0's context law for `TODO()` and, at `HEAD`,
F1's resolution for the ranges built from `end`). `ReqRangePinnedRev`, `ReqApplyTxnCAS`: provable
with 3e's reachability law (S1). `ReqApplyPutIgnoreValue`, `ReqApplyPutLeaseCheck`: unprovable (F5).
Coverage gaps: S2.

## Ranking by need of revision

1. `Api.lean` (F1's request, F2, F4's slots, F5; S3, S5).
2. `Txn.lean` (F4: the update's shape, reader token, trace).
3. `Put.lean`, `DeleteRange.lean` (F4; S4).
4. `Range.lean`, `executeRange.lean`, `Count.lean` (F2, F1, F4).
5. `checkRange.lean`, `checkTxn.lean` (F3, a one-line fix).
6. The snippets (F5 follows the vocabulary fix; S1, S2).
7. The other internal specs and the helpers/warnings (follow the renames; otherwise fine).
