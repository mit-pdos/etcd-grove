# Verification round, area A1 (client KV), provability: the report

Reviewer: provability, independent of the authors. HEAD `1aa6fc1337`. The targets: W0's
`api/v3/{Model,State,Wire}.lean`, `SpecPlan/Spec/context/`, `SpecPlan/Spec/go_uber_org/zap/`, `client/v3/Api.lean`,
the KV path's specs in `client/v3/`, the snippets in `examples/specreq/clientv3kv/`, and the
linearizability story in `notes/specs-only/top.md`. Go sources: `.lake/src/{client,api,server}`.
I wrote the findings below before reading the authors' notes. I read them afterwards only to mark
which findings are recorded decisions; none of the first-tier ones is.

## Verdict

**Batch W0, area A1-client-kv: FAIL.** Six first-tier findings, all cheap to repair:

- three laws or law pairs that cannot be proved or are inconsistent: F2, F3, F6;
- one spec that is false of the code: F4;
- one spec whose post cannot be established: F1;
- one place where the client's model of a request disagrees with what reaches a member over gRPC: F5.

Most of the area closes:

- **Vocabulary.** The model, the resource laws, the wire unfold laws and the KV contract are sound
  and coherent.
- **Proof sketches.** The sketches of `kv.{Get,Put,Delete,Do,Txn}`, `txn.{If,Then,Else,Commit}`
  and the `retryKVClient.*` methods close against the callee specs as they are now, except where a
  finding below says otherwise.
- **Snippets.** All 23 snippets are provably panic-free under their stated assumptions, given the
  repairs.
- **Linearizability story.** The story in `top.md` goes through from these specs. `txnlin` uses
  no empty `WithRange` end, so F5 does not touch it.

Counts:

| What | Checked | Close at HEAD |
|---|---|---|
| Client KV-path spec files (`kv__*`, `txn__*`, `Op*`, `With*` (KV options), `Cmp*`, `Compare`, comparison targets, `CompactOp*`, `retryKVClient*`, `RetryKVClient`, `NewKV*`, `*Response__OpResponse`, `OpResponse__*`, `ContextError`, `GetStream*`, `RangeStreamResponse.Err`, promoted `Client__{Get,Put,Delete,Txn,Compact,Do,GetStream}`, prefix helpers, `mustInt64*`) | 127 | 113 |
| zap specs (trusted) | 26 | 26 (one margin note, N4) |
| `context` specs (`Err`, `ErrDone`, `Background`, `TODO`, `WithCancel`, `WithTimeout`, `WithValue`, `Done`) | 8 | 8 |
| Laws (`State.lean` 23, `Wire.lean` 22, client `Api.lean` 38, `context` 15, zap 2) | 100 | 96 (F2, F3, F6, and F5's `endOf` at a dialed client's message) |
| Snippets (`put_get.go` 4, `history.go` 3, `txn.go` 6, `errors.go` 4, `ops.go` 4, `stream.go` 2) | 23 | 23 under the repairs (`ReqGetStream` and `ReqGetStreamCompacted` rest on F3's repair; `ReqCASModRevision`, `ReqTxnNested`, `ReqCompactReached` and the other transaction snippets on F6's) |

The 14 client spec files that do not close: `GetStreamToGetResponse` (F1); `kv.GetStream` and
`Client.GetStream` (F3); `Op.WithRangeBytes` (F4); `Value`, `Version`, `CreateRevision`,
`ModRevision`, `LeaseValue`, `Compare`, `Cmp.{Clone,WithRange,WithPrefix,GetCompare}` (F6). On top
of these, `txn.Commit`'s and `kv.Do`'s transaction step need F6's law, and `kv.Compact` needs F7's.

## First-tier findings

### F1. `GetStreamToGetResponse.spec`: a path whose post cannot be established

- **Principle:** sound (the post must hold on every path).
- **Evidence:** `streamAt_recv.spec` (`client/v3/Api.lean:1069-1082`) has a terminal-error
  disjunct with **no `Q`**: `⌜v.closeErr' = errVal .compacted⌝`. The server pinned the revision at
  the first page and a compaction overtook it before a later page.
  `GetStreamToGetResponse` (`kv.go:99-108`) returns `nil, err` on that chunk.
- **Why it does not close:** the spec's error post (`GetStreamToGetResponse.lean`) is
  `(∃ σ σ' e, Q σ σ' (.err e) ∗ ⌜err = errVal e⌝) ∨ indefCall err`. Neither disjunct holds of
  `errVal .compacted` without a `Q`:
  - `indefCall_pure` gives `indefErr err`;
  - `.compacted` is definite, so `indefErr (errVal .compacted)` is false.
- **Affects:** `etcdctl get --stream`; any user of the whole answer.
- **Fix:** add the disjunct `⌜err = errVal .compacted⌝` to the error post, as `streamAt_recv` has
  it. The caller relists, as Kubernetes does.

### F2. `callErr_errorsNew.spec` contradicts rpctypes' `callErr_eof.spec`

- **Principle:** sound, nothing vacuous (a law pair no realization can meet).
- **Evidence:**
  - W0's `callErr_errorsNew` (`client/v3/Api.lean:1129`) says that a call error whose dynamic type
    is `*errors.errorString` is `context.Canceled`'s value.
  - rpctypes' `callErr_eof` (`api/v3/v3rpc/rpctypes/Api.lean:400`) says `io.EOF` is a `.other`
    call error.
  - `io.EOF` is `errors.New("EOF")`, an `*errors.errorString`.
- **Why it does not close:** together the two laws make `io.EOF`'s value `context.Canceled`'s.
  The two `errorString`s carry different messages ("EOF" and "context canceled"), so the
  persistent points-to facts of their messages give `False`. The realizer of `callErr` cannot
  satisfy both laws. The W0 law is the false one: streams' `SendMsg`/`Recv` return `io.EOF`.
- **Affects:** 1d's `Mutex.TryLock`/`Lock`/`Proclaim` and 1f's `DoubleBarrier` sketches, which
  use `callErr_errorsNew` to tell their sentinels apart.
- **Fix:** conclude `globalAddr context.Canceled ↦□ err ∨ globalAddr io.EOF ↦□ err`. The
  consumers still tell their own sentinels apart from both by message.

### F3. `kv.GetStream.spec` (and `Client.GetStream.spec`): `io.EOF` is not excluded from the wire stream's errors

- **Principle:** every premise has a source; the post must hold on every path.
- **Evidence:**
  - The goroutine (`kv.go:178-186`) treats any `err` with `errors.Is(err, io.EOF)` as the clean
    end: it returns, and the deferred `close` closes the channel.
  - `streamAt_recv`'s closed-channel case then owes `Q` and `streamMatches`.
  - `wireStreamAt_recv.spec` (`Api.lean:1087-1104`) gives `Q` only in its EOF disjunct. Its
    error disjuncts admit `indefCall err` with no exclusion of `io.EOF`. By `callErr_eof`,
    `io.EOF` *is* an indefinite (`.other`) call error.
- **Why it does not close:** the sketch's step "`io.EOF` (`errors.Is`, Perennial)" lacks a premise.
  Perennial's `errors.Is` needs the error tree of `err`, and no W0 law gives `errors.Is(err, io.EOF)`
  for a call error. `errorsIs_errVal` only covers `errVal` targets.
- **Affects:** Kubernetes' store `GetList` and watcher (`etcd3/store.go:951`,
  `etcd3/watcher.go:391`); the snippets `ReqGetStream` and `ReqGetStreamCompacted`.
- **Fix:**
  - In `wireStreamAt_recv`'s two error disjuncts, add that the error is not `io.EOF`'s value.
  - Add a law that `errors.Is(err, io.EOF)` returns `false` for such a call error (as
    `errorsIs_errVal`; 2a realizes it: the errors there are statuses, context errors and
    `EtcdError`s).

### F4. `Op.WithRangeBytes.spec` is false at a `nil` slice

- **Principle:** sound (true of the code at every input the pre admits).
- **Evidence:**
  - `Op.WithRangeBytes.lean` takes any `b` with `b ↦*□ k` and posts
    `opAt op' { o with rangeEnd := some k }`.
  - `opAt_unfold`'s `some e` case requires `op.end' ≠ slice.nil`.
  - Go sets `op.end = end` (`op.go:169`), so at `b = slice.nil` (where `slice.nil ↦*□ []` holds)
    the post is false.
- **A real caller passes `nil`:** `namespace/kv.go:146` `prefixOp` calls
  `op.WithRangeBytes(end)` with `prefixInterval`'s `pfxEnd`, which is `nil` for every single-key
  op (`namespace/util.go`).
- **Consequence:** under the spec, a namespaced single-key `Get` would be modelled as "every key
  from the key on" (`endReq (some []) = [0]`).
- **Fix:** post `rangeEnd := if b = slice.nil then none else some k`.

### F5. A non-`nil` empty range end: the client models it as `"\x00"`; a dialed member reads one key

- **Principle:** sound; a contract between packages states what the receiver gets.
- **Evidence:**
  - `OpM.endReq` (`client/v3/Api.lean:289`), `Cmp.WithRange.spec` and `Wire.endOf` read a
    non-`nil` empty end as `[0]`: every key from the key on, which is mvcc's reading
    (`index.go`).
  - `clientv3.WithRange("")` (`op.go:439`: `op.end = []byte("")`) and `Cmp.WithRange("")`
    produce exactly such an end.
  - Over gRPC, proto3 does not encode an empty `bytes` field, so the member decodes `nil`: one
    key. The `RangeEnd` field is `proto3` with implicit presence (`rpc.pb.go:532`).
- **Why it does not close:** the client's `KV.GetTriple`/`DeleteTriple`/`Txn.CommitTriple` hand
  over an update for `Step p (.range r)` with `r.rangeEnd = [0]`. Through
  `retryKVHandle_remoteKVAt` and 2a's `etcdUnary` (`reqModels m c rq`), the member's update is for
  the decoded request, whose end is `[]`. That realization is false for a dialed client. It holds
  only in-process.
- **Recorded?** The server side is recorded (A14, `nonissues/etcd-auth-empty-range-end-point-check.md`,
  `endsDecoded`). The client side is not: `batch-W0.md` chose `endReq` for the in-process adapter.
- **Fix (one of):**
  - A scope premise on the client's KV specs: no `Op` or `Cmp` range end is `some []`. This is
    `WithRange`'s documented contract: "endKey must be lexicographically greater than start key".
  - Make the client's request model depend on the transport, which costs a mode.
- Either way, extend the nonissue: `WithRange("")` reads one key remotely and from the key on
  in-process.

### F6. No law makes a freshly built request message read-only

- **Principle:** every premise has a source (a missing law).
- **Evidence:**
  - `cmpAt_unfold` is `optOwn compareOwn c.c' DFrac.discard m`.
  - Every `Cmp` constructor allocates a fresh `*pb.Compare`, whose `protoRest` comes from
    `protoRest_zero` at `own 1`: `Value`, `Version`, `CreateRevision`, `ModRevision`,
    `LeaseValue`, `Compare`, `Cmp.WithRange`, `Cmp.WithPrefix`.
  - The others get one from `cloneCompare` at `own 1`: `Cmp.Clone`, `OpTxn`'s clones.
    `Cmp.GetCompare` of a zero `Cmp` allocates one too.
  - `txn.Commit` must build `txnReqOwn r dq t` with one `dq`, over compares it holds at `discard`
    (from `GetCompare`) and `RequestOp`s and a `TxnRequest` it holds at `own 1`.
- **Why it does not close:** W0 has `replyPersist` (the five replies), `eventOwn_persist` and
  `msgOwn_discard_persistent` (persistence *at* `discard`). Nothing takes `protoRest t p (own 1)`,
  or a request message, to `discard`.
- **Affects:** every snippet that builds a comparison, and leasing, concurrency and Kubernetes'
  transactions.
- **Fix:** add `protoRest_persist.spec : ∀ t p, protoRest t p (DFrac.own 1) ⊢ |==> protoRest t p
  DFrac.discard`; with the unfold laws it persists any message. 3h realizes it through
  `Proto.msgAt`, as for `msgOwn_discard_persistent`. Alternatively, a `reqPersist` law for
  `compareOwn`, `requestOpOwn` and `txnReqOwn`.

## Second-tier findings

- **F7. `kv.Compact`: no law that compact options keep the revision.**
  - `KV.CompactTriple` states the step at `.compact (sint.Z rev) (fold gs …).physical` and takes
    `rev ≠ 0`.
  - The request carries `(fold gs {rev, false}).revision` (`OpCompact.spec`,
    `CompactOp.toRequest.spec`).
  - `compactOptAt f g` has only `compactOptAt_call`, for an arbitrary `g`. `optAt_type` has no
    analogue here.
  - Fix: a law `compactOptAt_rev : compactOptAt f g ⊢ ⌜∀ o, (g o).revision = o.revision⌝`. It is
    true: `CompactOp`'s fields are unexported, and `WithCompactPhysical` is the only option.
    Alternatively, state the step at the folded revision.
- **F8 (stale at HEAD).** The "**Open**" paragraphs in `retryKVClient__Range.lean` and
  `retryKVClient__Txn.lean` say that 2a's `etcdUnary` carries no `lo`. It does now: `etcdAU … lo`
  and `authLb γ lo` (`server/v3/etcdserver/api/v3rpc/Api.lean:320-332`). Drop the paragraph.
- **F9 (`etcdState_revFits` realization text).** `State.lean`'s header realizes `etcdState` as "a
  ghost variable's half", the bound kept by the cluster's invariant. A plain entailment cannot open
  that invariant. The realization must put `⌜σ.kv.rev + 1 < 2^63⌝` (and the size bound) into the
  half the program holds; the cluster supplies it at every commit. The same holds for
  `etcdState_sizeFits`. Say so in the header.

## Notes (no change needed, or documentation)

- **N1.** The client `Api.lean` header says "a definite error is always a linearized answer". But
  `.noSpace` and `.unhealthy` are both `refusal` and `indefinite`. `ContextError` maps them to
  `indefCall` (the `Q` is dropped), which is sound, but the sentence should name the exception.
- **N2.** `ReqAuthRefusal` (`errors.go`) cites "`State.permits` at the firing state". The model
  checks a read by `permittedSince lo`, and at `lo = 0` that admits the initial auth-off table, so
  the "outside" read could succeed. The snippet needs `authLb γ lo` at an index where auth is
  already on (from an `etcdLb` the caller holds). Say so in `Assumes`.
- **N3.** `OpM.putPanics`'s docstring says "the model of a range end does not say whether an empty
  one is `nil`". `opAt_unfold` now does say it (`some []` is non-`nil`).
- **N4.** The zap `Logger.{Debug,Info,Warn,Error}` specs take the `fields` slice with no ownership,
  and `Stringer`/`Any` keep pointers the logger dereferences later. This is true of zap only if
  nothing writes them concurrently. Every caller in scope passes fresh variadic slices. Record it
  as the trust boundary's margin.

## Proof plans (every spec file; trivial ones batched)

### Vocabulary laws

**`State.lean`.**
- `etcdState_timeless`/`_excl`/`_lb`, `etcdLb_persistent`/`_timeless`/`_reach`/`_ord`: from the
  stated realization (a ghost variable's half, the history's authoritative/fragment). Plausible.
- `etcdLb_init`: `Reach` from `State.init` over the committed log. Plausible.
- `etcdLb_keyNonEmpty`: the step cases. `PutReq.invalid` refuses an empty key; a transaction's
  success arm requires `t.valid`, which recursively requires every nested put's key non-empty;
  deletes only remove existing keys. Plausible.
- `etcdLb_leases`: grants never use id `0`; `PutReq.check` checks the lease against the live table,
  and `ignoreLease` keeps a live lease; `revoke`/`leaseExpire` delete exactly the `attachedKVs`.
  Plausible.
- `etcdLb_noEmptyUser`: `userAdd` refuses `[]`. Plausible.
- `errVal_inj`: rpctypes' descriptions are pairwise distinct (checked: no duplicate
  `"etcdserver: …"` message in `error.go`). `errVal_ty`: plausible.
- `etcdState_revFits`/`sizeFits`: see F9.
- `leaseViewLb_le`, `urlsRight_excl`, `tokenUser_agree`: plausible.
- `etcdPerm`/`etcdPeek`/`envUpd`: definitions; a commit's `etcdLb` comes from `etcdState_lb` inside
  the owner's invariant.

**`Wire.lean`.**
- Every unfold law matches the generated structs' field names and types (`rpc.pb.go`; the
  `int32` enums through `W32`; the oneofs through wrapper structs).
- `protoRest_zero`, `msgOwn_ne_null`, `replyPersist`, `msgOwn_discard_persistent`,
  `eventOwn_persist`: plausible from 3h's `Proto.msgAt`.
- `endOf` is right for decoded messages (the server) and for in-process requests; F5 is the
  dialed client's case. F6 is the missing request-side persistence.

**Client `Api.lean`.**
- `opAt_unfold`, `cmpAt_unfold`, `optAt_call`, `optAt_type` (true of every package `OpOption`:
  none writes `t`, `cmps`, `thenOps`, `elseOps`), `compactOptAt_call`, `leaseOptAt_call`.
- `isClient_*`, `clientMut_*`, `clientRest_*`: 1c's realization.
- `kvAt_methods`, `txnAt_methods`, `remoteKVAt_methods`: the bundles.
- `kvHandle_kvAt`, `retryKVHandle_remoteKVAt`: the concrete specs below, with `clientReady`.
- `streamAt_recv`: the spsc realization over the goroutine; see F3.
- `wireStreamAt_recv`: 2a; see F3.
- `ctxPrin_*`: plausible from grpc metadata. `WithRequireLeader` copies the metadata and adds
  `hasleader`, keeping the token.
- `callErr_agree`, `callErr_ctxErr`, `callErr_errVal`: plausible. `callErr_errorsNew`: F2.
- `errorsIs_errVal`: plausible for the error types 2a admits (statuses' `Is` returns false against
  an `EtcdError`; `EtcdError` is comparable, so the interface compare cannot panic).
- `indefCall_pure`: plausible. `init.spec`: `noPrefixEnd` is never written (`getPrefix` returns
  it, and `prefixInterval` copies).

**`context` (`SpecPlan/Spec/context/Api.lean`).**
- `ctxOk`/`ctxDone` are a contract bundle. `Err`/`ErrDone` are Go's documented contract.
- `WithCancel`/`WithTimeout`: Perennial's, lifted. `WithValue`: Go panics on a nil or
  non-comparable key, and the premise is `CheckComparable`.
- `ctxWithValues_done`, `ctxNoMeta_*`, `ctxDone_background`, `TODO.spec`: plausible.
- `ContextError` calls `Err()` twice; `ErrDone.spec` keeps the second call's result non-`nil`.

**zap.**
- Trusted. `Check` at a level below `DPanic` (`sint.Z lvl < 3`: Debug `-1` … Error `2`);
  `Panic` panics with the message; `Fatal` never returns.
- Field constructors: total. Info and the other logging methods: see N4.

### Client functions

**`kv.Put`, `kv.Get`, `kv.Delete`.**
1. `OpPut`/`OpGet`/`OpDelete` give `opAt op (op*M key gs)` and return `optsAt`. The premises
   `¬putPanics`, `¬prefixAndFromKey` and `¬deletePanics` match the Go `switch`es exactly
   (`op.go:257-327`).
2. `kv.Do` with `o.toReq = some (.put/.range/.deleteRange …)`; `doReply`'s case gives
   `putReply`/`getReply`/`deleteReply`.
3. `ContextError`: `errVal e` stays `errVal e` through `callErr_errVal`, for a definite `e`; an
   indefinite one becomes `indefCall`, so a `Q` with `.err .noSpace` drops to the indefinite
   disjunct.
4. The update: the caller's, passed through (the read's persistent).

Closes.

**`kv.Do`** (`kv.go:213-250`). By `op.t` (`opAt_unfold`):
- **A range.**
  - `Op.IsSortOptionValid` (returns `decide o.rangeReq.validSort`).
  - If the sort is invalid, the proof fires the persistent update itself with
    `.err .invalidSortOption`. The model's range arm admits it, with `σ' = σ`, and the mask
    `⊤ \ ↑etcdN` is available.
  - Then `ContextError(ctx, rpctypes.ErrInvalidSortOption)` (rpctypes' init law, 2a).
  - Otherwise `Op.toRangeRequest` gives `rangeReqOwn` at `own 1`, then `RemoteKV.RangeTriple` with
    `kvHandle`'s `remoteKVAt` and `callOptsOk _ false`.
- **A put or a delete.** The request is built in place: `protoRest_zero`, the fields, `op.key`'s
  read-only slice, and `endOf` of `op.end`, which equals `endReq`. Then `RemoteKV.PutTriple` or
  `DeleteRangeTriple`.
- **A transaction.** `Op.toTxnRequest` (premise from `toReq`), then `RemoteKV.TxnTriple` with
  `□?isRead`.
- **The error paths.** `OpResponse{}` (all fields null), with `ContextError` on the error.

Closes, except the transaction step's compares (F6).

**`kv.Compact`.** `OpCompact`, `CompactOp.toRequest`, `RemoteKV.CompactTriple`, `ContextError`.
F7: the request's revision and `≠ 0` premise need a law.

**`kv.Txn`.** Allocates `&txn{kv, ctx, callOpts}`. Realize `txnAt` as the existential bundle over
`TxnSt.empty`, with the fields under `txn.mu` and `ctxOk`, `ctxPrin dflt ctx p` and the `kv`'s
remote stored. Closes.

**`kv.GetStream`.**
1. `OpGet`, `Op.toRangeRequest`, `RemoteKV.RangeStreamTriple`. The premise `0 ≤ r.revision` comes
   from `0 ≤ sint.Z (opGetM …).rev`.
2. On an open error: `ContextError`. A refusal `e` becomes `errVal e`, or `indefCall` if `e` is
   indefinite. The thread token is returned.
3. On success: a channel of capacity 1 (`isSpsc`) and `wp_fork` with the thread token. The loop
   uses `wireStreamAt_recv`:
   - a chunk: send `rr`'s ownership;
   - EOF: return, and the deferred `close` carries `Q` and `streamMatches`;
   - an error: send `ContextError`'s value (`errVal .compacted` without `Q`; `errVal e` with `Q`;
     else `indefCall`), then return.

Fails at the EOF test (F3).

**`txn.If`/`Then`/`Else`.**
- Lock; the flags as premises (Go panics otherwise).
- `If`: `Cmp.Clone` then `Cmp.GetCompare` per element (`cmpsAt` gives each element read-only, and
  `Clone` takes any `dq`).
- `Then`/`Else`: `Op.isWrite` (the field, unused) and `Op.toRequestOp` (premise `toReqOps os =
  some rs`), then append.
- Unlock. Closes, given F6 for `GetCompare`'s zero case.

**`txn.Commit`.** Lock, then `&pb.TxnRequest{…}` at one `dq = discard` (F6), then
`RemoteKV.TxnTriple` with `txnAt`'s `ctxPrin dflt ctx p`, `authLb γ lo` and the update, then
`ContextError`, then unlock. A second `Commit` resends the same discarded messages. A later
`Then` appends past the slices' length, into capacity the `txn` still owns. Closes with F6.

**`retryKVClient.{Range,RangeStream,Put,DeleteRange,Txn,Compact}`.** The stub's method, through
1c's `uiOk_call`/`siOk_call` over 2a's `AttemptTriple`. Further points:
- `Range` appends `withRepeatablePolicy()`. `c.callOpts` is a 3-element literal
  (`client.go:424`, `defaultCallOpts`), so `cap = len` and `append` allocates. 1c's `callOptsOk`
  must state this; plausible.
- A read's persistent update also serves as the exclusive one (`□ P ⊢ P`), for `rep = false`.
- `lo` is carried end to end (F8: the "Open" note is stale).

Closes against the callee specs as they are now.

**`RetryKVClient`, `NewKV`, `NewKVFromKVClient`.**
- `RetryKVClient`: the stub over `clientConnOk`'s connection.
- `NewKV`: `kvHandle kv c` records `c`, so that `kvHandle_kvAt` can take `clientReady c`.
- `NewKVFromKVClient` with `c = null`: `callOptsOk slice.nil false` (1c) and
  `clientReady_null` (1c). Closes.

**`ContextError`** (`client.go`).
1. `rpctypes.Error` (2a): `.etcd e` becomes `errVal e`.
2. `errors.As` into `EtcdError`: true exactly for the `errVal`s (`errVal_ty`), so the result is
   returned.
3. Otherwise `status.FromError`; for `Canceled`/`DeadlineExceeded`, `ctx.Err()` twice (`Err.spec`,
   then `ErrDone.spec`), giving a context error (`callErr_ctxErr`, `.other`).

Closes.

**`Op` constructors and transformers.**
- `OpGet` (runs the options on `NewOp()` twice, `IsOptsWith*`; `optAt` is exclusive and given
  back), `OpDelete`, `OpPut`, `OpWatch`, `OpTxn` (the comparisons cloned, given F6), `NewOp`.
- `Op.applyOpts`, `IsOptsWithPrefix`/`FromKey`.
- `Op.toRangeRequest` (Go panics unless `t = tRange`, a premise; `toEnum32` is `int32(int)`),
  `Op.toTxnRequest`, `Op.toRequestOp` (premise `toReqOp = some r`; `Unknown Op` panics otherwise),
  `Op.isWrite`.
- `Op.WithKeyBytes`/`WithValueBytes` close; `Op.WithRangeBytes` does not (F4).

**`Op` getters** (`IsGet`, `IsPut`, `IsDelete`, `IsTxn`, `Is*` flags, `KeyBytes`, `RangeBytes`,
`ValueBytes`, `Rev`, `Limit`, `Min*`/`Max*`, `IsSortSet`, `IsSortOptionValid`, `Txn`). One field
read each, through `opAt_unfold`. Close.

**`With*` (KV options)**:
- `WithLimit`, `WithRev`, `WithSort` (writes its captured `order`, the same effect on every call:
  `withSortM`), `WithPrefix` (`getPrefix`; the shared `noPrefixEnd`, `init.spec`), `WithRange`,
  `WithFromKey`, `WithSerializable`, `WithKeysOnly`, `WithCountOnly`, `WithMin*`/`WithMax*`,
  `WithPrevKV`, `WithIgnoreValue`, `WithIgnoreLease`, `WithLease`;
- `WithFirst*`/`WithLast*` (`withTop`: a fresh slice of three);
- `GetPrefixRangeEnd`/`getPrefix`, which match `prefixEnd`.

Each returns `optAt f g` with `g` the field update. Close.

**`Cmp` and comparisons.**
- `Compare` (`compareM`'s `none` cases are exactly Go's panics: an unknown result, a non-`string`
  value for `VALUE`, a `LeaseID` outside `LEASE` (`mustInt64` rejects the named type), an unknown
  target). `mustInt64`, `mustInt64orLeaseID`.
- `Value`, `Version`, `CreateRevision`, `ModRevision`, `LeaseValue`, `Cmp.WithRange`,
  `Cmp.WithPrefix`, `Cmp.Clone`, `cloneCompare`, `FromCompare`, `Cmp.GetCompare`,
  `Cmp.ensureCompare`, `Cmp.KeyBytes`.

Close but for F6, plus F5 for `Cmp.WithRange("")`.

**`CompactOp.applyCompactOpts`, `OpCompact`, `CompactOp.toRequest`, `WithCompactPhysical`.** Close;
see F7 for their consumer.

**`OpResponse.{Get,Put,Del,Txn}`, `{Get,Put,Delete,Txn}Response.OpResponse`,
`RangeStreamResponse.Err`.** Field reads and struct literals. Close.

**`GetStreamToGetResponse`.**
- `streamAt_recv` per chunk and `RangeStreamResponse.Err`.
- `proto.Merge` (3h's boundary): the `Kvs` appended; the header, `More` and `Count` from the last
  chunk, the only one that sets them.

Fails (F1).

**Promoted `Client.{Get,Put,Delete,Txn,Compact,Do,GetStream}`.** `isClient_KV` gives the field
`c.KV ↦□ v` with `kvAt v`, then `kvAt_methods`. Close (`GetStream` through F3).

## Snippets (`examples/specreq/clientv3kv/`)

Common setting: the owner's invariant over `etcdState`, holding "owned" keys' records as clauses
checked at every firing, the keys attached to no lease. Every `Q` also carries the `etcdLb`s of
its states (`etcdState_lb`). The ordering of states comes from `etcdLb_reach`, and every int64
compare is safe by `etcdState_revFits`/`etcdLb_revFits` and `sizeFits`.

**`put_get.go`.**
- **`ReqPutThenGet`.** The put's success is the put arm: `modRev = σ.kv.rev + 1`, the header's
  revision.
  - The get's firing is at a later `σ₂` (its update exists only after the put returned).
  - Owned key, no lease: the record is the put's, the range is the single key (`endReq none =
    []`), so there is one key-value.
  - The value and `ModRevision` match, and the header `σ₂.kv.rev` is at least `R`. Closes.
- **`ReqPutRevision`.** `R₁ > prevRev`: `prevRev` is at most some earlier state's revision (a
  serializable reply's view revision is at most its state's), and that is below `R₁`. With
  `WithPrevKV`, `prev` is the owned record with value `"a"` and `modRev R₁`; `putRespOwn`'s
  `optOwn` gives a non-`nil` `PrevKv`. Closes.
- **`ReqDeleteThenGet`.** Deleted `1`; then the store has no `k`. Closes.
- **`ReqListPrefix`.** `pushdownLimit = 3`, the cut at 2, `more = (2 < |take 3 all|)`,
  `count = |all|`, so `More = (Count > len)`; key order from `rangeKVs`; the prefix from the pure
  `prefixEnd` lemma (an all-`0xff` prefix is fine). Closes.

**`history.go`.**
- **`ReqGetAtRevision`.** `storeAt R₁` keeps `"old"` (the whole history is kept). The compare
  `err == rpctypes.ErrCompacted` cannot panic: `EtcdError` is comparable. Closes.
- **`ReqCompactReached`.**
  - The transaction's revision is at least 1 (`v.rev ≥ 1`), so `rev ≠ 0`.
  - `ErrFutureRev` is impossible: revisions only grow under `Reach`, and refusals and `indefCall`
    are not `futureRev` (`indefCall_pure`).
  - After a success, `compacted ≥ rev` stays (every step keeps `compacted` or raises it), so the
    `WithRev(rev-1)` get hits the `revErr` compacted arm.
  - Closes, with F6 for the comparison.
- **`ReqRevisionsMonotone`.** By `etcdLb_ord`/`reach`. Closes.

**`txn.go`.**
- **`ReqCASModRevision`.** The model's `TxnRun`:
  - One response per operation of the branch (`Forall₂`).
  - The then-branch's put and the else-branch's range read `s0`. On a failed compare, either the
    key is present with `modRev ≠ rev` (and `W64` is injective below `2^63`), or the key is
    absent with `rev ≠ 0` (the zero key-value compares as `0`).
  - Closes, with F6.
- **`ReqCreateIfAbsent`.** A failed `CreateRevision = 0` means the key is present with
  `createRev ≠ 0`. `createRev ≤ v.rev` is the header (no writes); that is a pure provenance lemma
  from `etcdLb_init`. Closes, with F6.
- **`ReqTxnReadsOwnWrites`.** No comparisons, so it succeeds. The range reads `st.1` after the
  put, and `modRev = v.rev + 1`, the header. Closes.
- **`ReqTxnNestedRangeHeaders`.** Read-only and linearizable: `□` update. With no writes the
  nested ranges' revision is `h.rev = v.rev`, the header. `ofResp .range` gives a non-`nil`
  header. Closes.
- **`ReqTxnNested`.** The nested comparison is evaluated at `s0` (as etcd's `compareToPath` does,
  upfront), where `k` holds `"a"`, so it succeeds. A `nil` else slice is `opsAt nil []`.
  Closes, with F6.
- **`ReqTxnReadonlySerializable`.** Read-only and serializable (vacuously), so `□`. No
  operations, so no responses; `v.rev ≥ 1` from `IsView`. Closes, with F6.

**`errors.go`.**
- **`ReqPutErrors`.** A put's `Step` errors are the put arm's and refusals: never `compacted` or
  `futureRev` (the lease, auth and cluster steps are `False` for `.put`). `errorsIs_errVal`
  decides each `errors.Is`. Closes.
- **`ReqGetErrors`.** `rev` is at most the current revision, so no `futureRev`; refusals are never
  `futureRev`. Closes.
- **`ReqAuthRefusal`.** Closes given N2's `lo`. With auth on since `lo` and `u`'s roles fixed,
  neither `permits` nor `permittedSince lo` holds outside `[pfx, end)`. `end` is non-empty and
  not `"\x00"`, so F5 is avoided.
- **`ReqCtxErrors`.** `WithCancel` and `cancelOk`. A current read has no `revErr`, and refusals
  and `indefCall` are not `compacted`. Closes.

**`ops.go`.**
- **`ReqOpGetters`.** The getters at `opGetM`. `OpTxn(nil, …)` gives zero clones. Closes.
- **`ReqDo`.** `doReply`'s per-kind null fields. The empty `OpTxn` is valid, read-only and
  serializable; success has `ok = true`. Closes.
- **`ReqSerializableGet`.** `IsView`: `v.rev ≥ 1`. `modRev ≤ v.rev` and `createRev ≤ modRev` are
  provenance lemmas of `Reach`. Closes.
- **`ReqGetOptions`.** Count-only gives no key-values; keys-only gives empty values;
  `WithFirstCreate` (non-default ordering, `pushdown = 0`, cut at 1) gives at most one. Closes.

**`stream.go`.**
- **`ReqGetStream`.** An error chunk's `Err()` is non-`nil`, so the snippet returns before the
  nil check. Chunk headers are `none` except the last's. At the end, `streamMatches` at the default
  ordering gives `flatten = a.kvs` with `count = |all| = |a.kvs|` (no limit). Key order and range:
  `to` is a proper end. `hdr = v.rev ≥ rev`, by success's `revErr = none`. Closes given F3.
- **`ReqGetStreamCompacted`.** An unpinned read (revision `0`) is never `futureRev`.
  `errorsIs_errVal` on the three terminal-error forms. Closes given F3.

## The linearizability story (`top.md`)

It goes through from these specs:

- **One resource.** Every KV call takes the update over `etcdState` the program owns.
- **Writes and reads.** Writes are exclusive and fire at most once. Reads are persistent and fire
  only from registration on, inside the call, with the returned `Q` the firing at the member's
  state. `txnlin`'s read-revision prophecy picks which firing appends to `linLog`.
- **Errors.** A definite error is a no-op step: every error arm of `kvStep` and the refusal arm
  have `σ' = σ`. An indefinite one leaves the update to the program's invariant, which
  `p.ResolveBool(!out.Err)` informs.
- **The environment.** Its steps reach only through `envUpd`. `txnlin` reads only current
  revisions, never grants a lease, and its `WithRange("l")` end is proper, so F5 does not arise.

The two scope points named in `top.md` (stale compare-only transactions, keys-only lease `0`) are
in the model, as stated. The Kubernetes and concurrency paragraphs rest on `etcdLb` facts that are
pure consequences of `Reach`, which the snippets above exercise. F1 and F3 touch the Kubernetes
streamed list; F6 touches its compare-and-swap.

## Go code

No new bug in the Go code. F5's behaviour, where `WithRange("")` reads one key over the network
and every key from the key on in-process, belongs in
`nonissues/etcd-auth-empty-range-end-point-check.md` or a sibling nonissue (the API's
documentation requires a greater end key). I did not edit `nonissues/`: this round is read-only.
