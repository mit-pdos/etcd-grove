# Re-review A1 (client KV, batch W0) after the repairs

Reviewer: independent, read-only. HEAD `974e05095b`. Baseline for regressions: `1aa6fc1337`.
Area: `SpecPlan/Spec/go_etcd_io/etcd/client/v3/` (KV, Op, Txn, Cmp, retry, ctx; the shared `Api.lean`'s KV part),
`SpecPlan/Spec/go_etcd_io/etcd/api/v3/{Model,State,Wire}.lean`, `SpecPlan/Spec/go_uber_org/zap/`, `SpecPlan/Spec/context/`,
`SpecPlan/Spec/fmt/`; snippets `examples/specreq/clientv3kv/` (there is no `examples/specreq/context/`).
I wrote my verdict on each finding before reading `repair-*.md`. Afterwards I read only
`repair-client-core.md` §8, `repair-grpc-v3rpc.md` P-F7 and `open-questions.md` C3/1.5/A14, to check
the disagreements below.

## Verdict

**Batch W0 (A1-client-kv): FAIL.**

Every original first-tier finding is resolved, or is recorded as an open decision (completeness F4:
`open-questions.md` 1.5). But the F5 repair's scope premise (`emptyEnd = false`, `e ≠ []`) never
reaches the formal chain: W0's request predicates and the `RemoteKV` contract forget it. Three new
first-tier findings follow:

- **NF1.** The `RemoteKV` contract cannot be realized: grpc's `unaryArgs` now needs `endsOk`, and no
  W0 request predicate carries it.
- **NF2.** `cloneCompare`, `FromCompare` and `Cmp.Clone` are false, or cannot be proved, at a non-`nil`
  empty `Compare.RangeEnd`.
- **NF3.** The new `Context.Value.spec` contradicts the old law `ctxOk_of_isContext`.

NF1 and NF2 have one common fix.

## Original first-tier findings

| Report | Finding | Status | Evidence at HEAD |
|---|---|---|---|
| prov. | F1 `GetStreamToGetResponse`: no `ErrCompacted` disjunct | **Resolved** | `GetStreamToGetResponse.lean:51` adds `⌜err = errVal .compacted⌝`; `streamAt_recv` (`Api.lean:1168`) has the same. |
| prov. | F2 `callErr_errorsNew` vs `callErr_eof` | **Resolved** | `Api.lean:1223-1226` concludes `Canceled ↦□ err ∨ io.EOF ↦□ err`. The consumers are updated: `concurrency/Api.lean:684` and `recipes/Api.lean:449` keep their sentinels distinct from both. |
| prov. | F3 `io.EOF` not excluded from the wire stream's errors | **Resolved** | `wireStreamAt_recv`'s error branch carries `∃ eof, io.EOF ↦□ eof ∗ ⌜err ≠ eof⌝` (`Api.lean:1191`). New law `errorsIs_callErr_eof` (`:1259`). Every error disjunct gives `callErr err _` (`indefCall` unfolds to `∃ k, callErr`, `:611`). Plausible: grpc's status `Is` matches only `*status.Error`; `EtcdError` and context errors neither unwrap nor define `Is`. |
| prov. | F4 `Op.WithRangeBytes` false at `nil` | **Resolved** | `Op__WithRangeBytes.lean:42`: `if b = slice.nil then none else some k`. This matches `op.go:169` and `opAt_unfold`. |
| prov. | F5 non-`nil` empty end: client model vs dialed member | **Resolved in the statements, recorded as open decision C3** | The scope premise is in `KV.{Get,Delete,Do,GetStream}Triple`, `Txn.{Then,Else}Triple` (`Api.lean:720,735,769,789,827,838`) and `Cmp.WithRange` (`e ≠ []`); the nonissue is filed. **The premise is never carried to the gRPC layer**, so the repair does not close: see NF1 and NF2. |
| prov. | F6 no law persisting a built request | **Resolved** | `protoRest_persist.spec` (`Wire.lean:360`). With the unfold laws it persists `compareOwn`, `requestOpOwn` and `txnReqOwn`. The sketches cite it (`Value`, `OpTxn`, `Cmp.GetCompare`, `txn.If`, `txn.Commit`, `kv.Do`). |
| compl. | F1 `GetStream` keeps the caller's thread token | **Resolved** | No `threadTok` in `KV.GetStreamTriple` (`Api.lean:785-799`). Perennial's `wp_fork` (`Lifting.lean:1977`) needs none, and the margin is rewritten. |
| compl. | F2 no `kvAt`/`txnAt` introduction for wrappers | **Resolved** | `kvAt_intro` (`Api.lean:1087`) and `txnAt_intro` (`:1118`). `Txn.*Triple` take `T` (default `txnAt`). Realizable as the stated existential bundles. Checked against `wrap.go`: for `S iv st := txnAt iv st ∨ ∃ x, ⌜iv = trackedTxn{x}⌝ ∗ txnAt x st`, the promoted `If` returns the inner value and `Commit` forwards. |
| compl. | F3 `ctxPrin_todo` a second triple | **Resolved** | `ctxPrin_todo.spec : ⊢ ctxPrin dflt (ok todoCtxVal) dflt` (`Api.lean:1234`). `TODO.spec` names that value (`context/Api.lean:109`). |
| compl. | F4 no `ctxPrin` for an unissued token | **Open decision** (`open-questions.md` 1.5, "still out of scope") | No `tokenUnissued` anywhere in `Spec/`. Two users stay unserved (`authkv.go`'s "bad" principal, 1c's `ReqRefusedPrincipals`). |
| compl. | F5 no `Context.Value` contract | **Resolved, but see NF3** | `Value.spec`, `ctxValueIs`, `_wp`, `_child`, `_other` (`context/Api.lean:158-199`). Sound for the lessor's `==` (`lease.go:368`): one side is `&ctx`, a comparable pointer, so the interface compare cannot panic. Sound for the server's checked assertion (`v3_server.go:1022`). |

Second-tier, for the record:
- prov. F7 is resolved: `compactOptAt_rev`, `Api.lean:999`.
- prov. F8 is resolved: the stale "Open" notes are dropped in `retryKVClient__{Range,Txn,RangeStream}`.
- prov. F9 is resolved: `State.lean`'s header puts the bounds in the program's half.
- prov. N1–N4 are resolved: the `Api.lean` header, `errors.go`'s `lo`, the `putPanics` doc and the zap margin.
- compl. S3 is resolved.
- compl. S1 is partly resolved. `Float64`, `Time`, `Binary`, `Named`, `With` and `Sync` are added. `Logger.Core().Enabled` is still missing. The zap header says "no specced caller needs them yet", but `logUnaryRequestStats.lean` is specced and calls it (`interceptor.go:94`). Second tier.

## New first-tier findings

### NF1. The KV requests' `endsOk` has no source: W0's `RemoteKV` contract cannot be realized over grpc

- **The step that fails.** Every `RemoteKV.*Triple` is realized by `NewKVClient.spec`'s `remoteKVAt`
  (3h). That realization goes through 1c's `uiOk_call`/`AttemptTriple`, whose `unaryArgs` slot 3h
  realizes as `unaryArgs_msgAt.spec` (`etcdserverpb/Realize.lean:212-221`), and that law requires
  `endsOk c` of the request content.
- **Why there is no source.** `RemoteKV.RangeTriple` (`Api.lean:861-870`) gives the realizer only
  `rangeReqOwn req dq r`, and likewise `RangeStream`, `DeleteRange` and `Txn`. Through
  `rangeReqOwn_msgAt` (`etcdserverpb/Api.lean:332`) this is `∃ c, msgAt ∗ ⌜reqHolds c (.range r)⌝`.
  The only ways to introduce `endsOk` are:
  - `endsOk_canon`, for a decoded message: a client-built request is not known canonical;
  - `endsOk_range_intro` (`:501`), which requires `r.rangeEnd ≠ [0]`.
- **What is left uncovered.**
  - `r.rangeEnd = [0]`: every `WithFromKey`, `WithPrefix("")` and prefix-of-`0xff` range (`Wire.endOf`
    maps both `"\x00"` and a non-`nil` empty end to `[0]`).
  - Every `DeleteRange`, `Txn` and `Put` content: there is no intro law for them at all.
- **Why the scope premise does not help.** The client's `emptyEnd = false` is known inside `kv.Do`,
  but it is lost at the contract. `rangeReqOwn_unfold` (`Wire.lean:365-370`) admits
  `es ≠ nil ∧ ebs = []`. The `Wire.lean` header (lines 29-36) and `repair-client-core.md` §8 claim
  "the client keeps `endsOk` by `OpM.emptyEnd`", but no statement carries it.
- **Affects.**
  - `retryKVClient.{Range,RangeStream,DeleteRange,Txn,Put}.spec` (no proof plan closes at the
    `uiOk_call` step);
  - `NewKVClient.spec` (A6/3h);
  - through `kvHandle_kvAt`, every client KV call and every snippet.
- **Uncertain, outside A1.** `unaryArgs_msgAt` is generic in `rq`, so the lease, auth, cluster and
  maintenance stubs probably have the same gap for their contents.
- **Suggested fix (also closes NF2).** Make W0's request predicates mean "ends `nil` or non-empty":
  1. Add `⌜es = slice.nil ∨ ebs ≠ []⌝` to `rangeReqOwn_unfold`, `deleteReqOwn_unfold` and
     `compareOwn_unfold`, and hence to `requestOpOwn` and `txnReqOwn`.
  2. 3h realizes them as `∃ c, msgAt ∗ ⌜reqHolds c rq ∧ endsOk c⌝` and adds `endsOk` intro laws for
     contents with no range end (put, compact, the lease requests).
  3. Builders discharge the new conjunct from `emptyEnd = false` or `e ≠ []`; the server holds
     decoded messages (`endsOk_canon`).

  Alternative: give the `RemoteKV` triples an explicit W0-level premise. That spreads the condition
  over every caller.

### NF2. `cloneCompare.spec` / `FromCompare.spec` / `Cmp.Clone.spec` are false or unprovable at a non-`nil` empty `Compare.RangeEnd`

- **The step that fails.** `cloneCompare` (`compare.go`, via `proto.Clone`) produces `norm c`
  (`proto/Clone.lean:52`). protobuf-go's merge of a proto3 implicit-presence `bytes` field copies it
  only when its length is above 0, so a non-`nil` empty `RangeEnd` becomes `nil`. 3h's `holds_norm`
  keeps `compareHolds` only under `endsOk` (`etcdserverpb/Api.lean:310`).
- **Why the post is false.** `cloneCompare.spec` (`cloneCompare.lean`) takes
  `optOwn compareOwn p dq m` for any content and returns the copy at the **same** `m`. At
  `RangeEnd = []byte{}` (model `[0]`, "from the key on") the copy compares the key alone (model `[]`).
- **A Go program that reaches it.** `clientv3.FromCompare(&pb.Compare{Key: k, RangeEnd: []byte{},
  ...})`:
  1. `FromCompare.spec` gives `cmpAt c (some m)` with `m.rangeEnd = [0]`;
  2. `txn.If`/`Commit` then hand an update for a compare over `[k, ∞)`;
  3. the cluster evaluates `k` alone, even in-process.

  So a program that asserts the compare's outcome can panic while proved safe.
- **Why the others cannot be proved.** `cmpAt_unfold` is `⊣⊢ optOwn compareOwn`, so `cmpAt` does
  not exclude such an end either. The proofs of `Cmp.Clone`, `Compare`, `Cmp.WithRange` and
  `Cmp.WithPrefix`, and the clones in `OpTxn`/`txn.If`, then need an `endsOk` that `cmpAt` does not
  give. `cloneCompare.lean`'s second-pass note asserts "every `cmpAt` comparison has a `nil` or
  non-empty end", but nothing states it.
- **Affects.**
  - `FromCompare`'s users (the gRPC proxy);
  - formally, every `Cmp` transformer's proof, and so `ReqCASModRevision`, `ReqCreateIfAbsent`,
    `ReqTxnNested`, `ReqCompactReached` and `ReqKVWrapper`.
- **Fix.** NF1's `compareOwn_unfold` conjunct. Then `FromCompare` takes only compares whose end is
  `nil` or non-empty (a scope premise, as C3), and the clone keeps the model by `holds_norm`.

### NF3. `Context.Value.spec` (new) cannot hold for every context `ctxOk_of_isContext` (old) admits

- **The conflict.**
  - `Value.spec` (`context/Api.lean:179`) says that `ctx.Value(key)` returns, without panicking,
    for every `ctxOk ctx` and every key.
  - `ctxOk_of_isContext.spec` (`:96`) gives `ctxOk (ok c)` from Perennial's
    `isContext c s` for a context of any type.
  - `isContext` specifies `Value` only at `&cancelCtxKey` (`perennial/Proof/context/Base.lean`,
    `"#HValue"`, around line 585).
- **Why it fails.** A type meeting `isContext` whose `Value` panics at other keys satisfies the law's
  premise while `Value.spec` is false of it. No realization of `ctxOk` can meet both.
- **Affects.** Nobody uses `ctxOk_of_isContext` (grep over `Spec/` and `examples/`), so the fix is
  cheap.
- **Fix.** Either:
  - drop the law; or
  - add Perennial's value-chain fact (`CtxValue.lean`'s `ctxValue (ok c) k R`, for every
    `k` that is not a `*int`) to its premise.

## Regressions checked (changed files since `1aa6fc1337`)

- **`Api.lean`.**
  - Closes under the new laws: `emptyEnd`/`anyEmptyEnd` (mutual, structural);
    `compactOptAt_rev`; `kvAt_intro`/`txnAt_intro` (bundle realizations sound).
  - `clientConnOk_conn`: plausible from 1c.
  - `init.spec`: the three `errors.New` sentinels are distinct `*errorString`s, never `errVal`
    (`client.go:45-47`), and `LeaseResponseChSize = 16` (`lease.go:92`). That exported variable is
    made read-only, a scope restriction; nothing in scope writes it.
  - `wireStreamAt_recv` and `errorsIs_callErr_eof`: as in F3. The new `T` parameter of the `Txn`
    triples defaults to `txnAt`, so the existing users are unchanged.
- **`kv__GetStream`, `Client__GetStream`, `GetStreamToGetResponse`, `Op__WithRangeBytes`,
  `Cmp__WithRange`, `kv__Do`, `kv__Compact`, `txn__*`, `retryKVClient__*`, `NewKVFromKVClient`
  (`clientBase`).** They close against the specs as they are now, except for the `endsOk` step
  (NF1) and the clones (NF2).
- **`Model.lean`.**
  - The three-view `deniedSince` and the two-view `adminDenied` in `kvStep .compact`: the snippets
    still close. `ReqAuthRefusal`: every table from `lo` on has the same grant for `u`, so no view
    denies the in-range read. `ReqCompactReached` panics only on `ErrFutureRev`, which the admin arm
    never returns.
- **`State.lean`.**
  - The realization of the bounds (F9): fine.
  - `urlsRight_norm`: plausible, owned by A8.
- **`Wire.lean`.** `protoRest_persist`: fine. The header's "wire view" paragraph is the claim NF1
  shows is not carried.
- **`context/Api.lean`.**
  - `Value` and the `ctxValueIs` laws: NF3.
  - Second tier: `ctxValueIs_child` is false at key `&cancelCtxKey`, where a cancel context returns
    itself. Go code cannot name that key, so the law only needs a "not `*int`" premise, as
    Perennial's `notIntPtrKey`.
- **`fmt`.**
  - `printMD_inj`: plausible. A printable map's `%+v` (sorted keys, no space, `:`, `[` or `]`, no
    empty strings) parses back uniquely up to key order.
  - `Sprintf_md`: holds the map at a fraction during the call. Fine.
- **zap.**
  - The six new trusted specs are total and return a field or a logger. True of zap: `Named("")`
    and `With()` return `l`, and `Sync` may return any error.
  - The concurrent-read margin is recorded in the header.

## Snippets

- **`stream.go`.**
  - `ReqGetStream` and `ReqGetStreamCompacted` close with no thread token, given F3's law.
  - `ReqGetStreamWhole` (new) closes:
    - the success post's header comes from `streamMatches`' last chunk (`Api.lean:482`);
    - `errorsIs_errVal` rules out `ErrFutureRev` for each error form (an unpinned read is never
      `futureRev`; `errVal_inj`; `indefCall_pure`).
- **`wrap.go`.** `ReqKVWrapper` (new, the Kubernetes latency-tracker pattern) closes:
  1. `New.spec` gives `clientMut`, and `clientMut_KV` exposes the `KV` field;
  2. `kvAt_intro` with `P = kvAt v` (the seven methods, four of them promoted);
  3. `txnAt_intro` with the disjunctive `S` above;
  4. `clientMut_freeze` gives `isClient`.

  It covers completeness pattern P20.
- **`errors.go`.** `ReqAuthRefusal`'s `lo` assumption is now stated (N2).
- **The other 20 snippets** are unchanged and close as before, except that every one built on a
  `Cmp` or a gRPC call inherits NF1/NF2 at the formal level. That is the same repair, not a
  per-snippet one.
- **Patterns.**
  - P19 (stream), P20 (wrapper), P21 (`TODO`) and P23 (`ctx.Value`) are now covered.
  - P22's unissued-token half remains open (1.5).
  - P25: `Core().Enabled` is still missing (second tier).

## Counts

- Original first-tier findings: 11.
  - 9 resolved;
  - 1 resolved in the statements but recorded as open decision C3, and not closing formally (F5,
    see NF1/NF2);
  - 1 still an open decision (compl. F4, 1.5).
- New first-tier findings: 3 (NF1, NF2, NF3).
- New second-tier findings: 2 (`ctxValueIs_child` at `&cancelCtxKey`; zap `Core().Enabled` with a
  specced caller).
- Changed spec files checked in the area:
  - 31 client KV/Op/Txn/Cmp/retry files plus `Api.lean`;
  - `Model.lean`, `State.lean`, `Wire.lean`;
  - `context/Api.lean`, `fmt/Api.lean`, `fmt/Sprintf_md.lean`;
  - zap `Api.lean` and 6 new zap files.

  The watch, lease, auth and cluster files changed in the same commits were not reviewed (other
  areas).
- Snippets: 3 changed or added (`stream.go`, `errors.go`, `wrap.go`) checked in full, the other 20
  rechecked against the changed statements.

No new bug in the Go code. NF2's behaviour, where `FromCompare`/`Cmp.Clone` of a `Compare` with an
empty non-`nil` `RangeEnd` silently turns a from-key comparison into a single-key one, is protobuf's
documented treatment of proto3 implicit-presence fields. It belongs with
`nonissues/etcd-client-withrange-empty-end.md` as a further instance; I did not edit `nonissues/`.
