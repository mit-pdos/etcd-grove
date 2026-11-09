# Verification, A1-client-kv, completeness (batch W0)

Reviewer: completeness kind, independent. Commit under review: `1aa6fc1337` (HEAD of `specs-only`).
Area: `Spec/go_etcd_io/etcd/api/v3/{Model,State,Wire}.lean`, `Spec/context/Api.lean`,
`Spec/go_uber_org/zap/`, and the client's KV path in `Spec/go_etcd_io/etcd/client/v3/` (`Api.lean`,
`kv__*`, `Client__{Get,Put,Delete,Txn,Do,Compact,GetStream}`, `txn__*`, `Op*`, `With*`, `Cmp*`,
`Compare`, the comparison targets, `CompactOp*`, `retryKVClient__*`, `RetryKVClient`, `NewKV*`, the
responses, `GetStreamToGetResponse`, `RangeStreamResponse.Err`, `ContextError`, `WithRequireLeader`,
`withVersion`); snippets `examples/specreq/clientv3kv/`.

I wrote the findings below before I read `batch-W0.md`, `open-questions.md`, `integration-*.md` and
`reviews/`. I read them afterwards only to mark which findings are already recorded.

## Verdict

**Batch W0 (A1-client-kv): FAIL.** Four first-tier findings are not recorded anywhere (F1, F2, F3,
F5). F4 is a recorded open decision (`open-questions.md` 1.5, "Now: out of scope"). Everything else
closes: 20 of the 25 usage patterns, and the sampled callers' sketches except those listed below.

## First tier

### F1. `GetStream` takes a thread token and never gives it back, not even on a drained stream

- **Spec.** `KV.GetStreamTriple` (`client/v3/Api.lean:747-760`) takes `threadTok` in its
  precondition. Its success branch (`err = nil ∗ streamAt ch … [] false`) holds no token.
  `streamAt_recv.spec` (`Api.lean:1067-1083`) does not return one in any outcome either: not for a
  chunk, not for the terminal error, not for the channel closed after the last chunk. Yet
  `kv__GetStream.lean:22` says "The thread token comes back only for a drained stream". The law
  contradicts it: every successful stream costs the caller a token for good.
- **Go and Perennial.** On success, `kv.go:176` forks the goroutine. Perennial's `wp_fork_tok`
  (`.lake/packages/perennial/Perennial/GooseLang/Lifting.lean:1964`) hands the forking thread a fresh
  `threadTok`, and the forked thread must end holding one. So `GetStream` can give the goroutine the
  caller's token and return the fresh one, or need none at all. The token loss is unneeded weakness,
  and the premise may be unneeded too.
- **Users not served.**
  - Kubernetes' `store.go:951` (`streamChunks`, once per LIST) and `watcher.go:391`
    (`syncStreamRecursive`, once per watch). A request goroutine holds only its own token, which it
    needs again at its exit, so it cannot call `GetStream` at all. A long-running store runs out of
    tokens.
  - The snippet `ReqGetStream` (`stream.go`) assumes "the caller has a thread token for the client's
    reading goroutine", a spare that no caller has.
- **Fix.** Give back `threadTok` in every branch of `KV.GetStreamTriple`: the fresh token from
  `Fork`, while the goroutine keeps the caller's until its exit. Or drop the premise. Then rewrite
  the margin: an abandoned stream leaks a goroutine (the nonissue), not the caller's token. The
  earlier review's S2 asked only for the margin text, which was added; the law was never changed.
  Not recorded.

### F2. No introduction law for `kvAt` or `txnAt`, so a wrapped `KV` cannot regain `isClient`

- **Spec.** `kvAt` (`Api.lean:483`) and `txnAt` (`:512`) are opaque. Their only introductions are
  for the package's own types: `kvHandle_kvAt` (`:1026`), and `kv.Txn.spec`'s post for `*txn`. The
  header claims "a wrapper (Kubernetes' latency tracker) proves it for itself" (`:62-65`), and
  `clientMut` exists "for a caller that wraps `c.KV`, as Kubernetes' storage factory does"
  (`:59-61`). `clientMut_KV` (`:985`) needs `kvAt v` for the value written. No law produces `kvAt`
  of a wrapper, nor `txnAt` of the wrapper's `Txn`.
- **Users not served.**
  - The Kubernetes factory, `k8s.io/apiserver/pkg/storage/storagebackend/factory/etcd3.go:468`:
    `client.KV = etcd3.NewETCDLatencyTracker(client.KV)`.
  - The tracker, `latency_tracker.go:30-108`. Its `Txn` returns `&clientV3TxnTracker{…}`, which
    needs `txnAt` of the tracker itself. Its `If`, `Then` and `Else` are promoted; its `Commit` is
    its own.
  - Every store call after the wrap goes through `isClient`.
  - `client/v3/ordering.NewKV` is the same pattern. It has no spec.
  - The previous round's F7 fixed only the builders' `r = iv` and left this gap.
- **Fix.** Add the bundles' introduction laws:
  - `kvAt_intro.spec : ∀ v γ who (P : IProp GF), Persistent P → KV.PutTriple (v @!! KV.ty @!! "Put") P γ who → … (the seven) → (P ⊢ kvAt v γ who)`.
  - `txnAt_intro.spec : ∀ iv γ who ctx (S : TxnSt → IProp GF), (the four triples with S st as the receiver's state) → S st ⊢ txnAt iv γ who ctx st`.

  Their intended realization ("an existential bundle") already admits both. Not recorded.

### F3. `ctxPrin_todo` is a second triple on `context.TODO()`, so no caller holds both `ctxOk` and `ctxPrin` of one context

- **Spec.** `Context.TODO.spec` (`context/Api.lean:103`) gives `ctx = todoCtxVal ∗ ctxOk ctx`.
  `ctxPrin_todo.spec` (`client/v3/Api.lean:1138-1142`) is a separate triple on the same call that
  gives only `ctxPrin dflt ctx dflt`. One execution of `TODO()` can be given only one of the two
  triples. No entailment law gives `ctxPrin` at `todoCtxVal`: there is `ctxPrin_background` and
  `ctxNoMeta_background`, but no `_todo` counterpart.
- **Users not served.** Every KV call of the recipes passes `context.TODO()` (11 sites in
  `client/v3/experimental/recipes/*.go`). The recipes' vocabulary assumes both facts
  (`recipes/Api.lean:65-71`), as do the sketches of `deleteRevKey.lean:8-9` (and through it
  `claimFirstKey` and the `Dequeue`s) and `newSequentialKV.lean`.
- **Fix.** Restate the law as an entailment at the value TODO.spec now names:
  `ctxPrin_todo.spec : ∀ dflt, ⊢ ctxPrin dflt (GoInterface.ok context.todoCtxVal) dflt`. Or add
  `Context.ctxNoMeta_todo` and use `ctxPrin_of_noMeta`. Not recorded: integration-I1 named the value
  but left the triple.

### F4. No `ctxPrin` for a context carrying a token no provider issued (recorded open decision)

- **Spec.** `ctxPrin`'s documentation (`Api.lean:547-568`) says an invalid token means "refused,
  any principal". There is no introduction for it: `ctxPrin_token` needs `tokenUser γ tok u`, and
  `ctxPrin_of_noMeta` needs no metadata.
- **Users not served.**
  - `examples/etcd/auth/authkv.go:151-205`: the "bad" principal, through `reqCtx` and `refused`.
  - 1c's snippet `ReqRefusedPrincipals` (`examples/specreq/clientv3client/auth.go:102`). It cites
    `Client.Put.spec` and asks for this law in `req/go_etcd_io_etcd_client_v3.md:477-482`.
- **Fix,** as integration-I1 wrote it:
  - 3d adds `tokenUnissued γ tok`, with an introduction and `tokenUnissued ∗ tokenUser ⊢ False`.
  - W0 adds `ctxTokenMd ctx tok ∗ tokenUnissued γ tok ⊢ ctxPrin none ctx p`, for any `p`. This is
    sound: the server's answers are `ErrInvalidAuthToken`, `ErrUserEmpty` and `ErrAuthOldRevision`,
    all `EtcdErr.refusal`, and with auth off no check depends on the principal.
- **Recorded:** `open-questions.md` 1.5 ("Now: out of scope", bundled with the in-process client).
  It still counts: two users stay unserved until it is decided.

### F5. The context API has no `Value` contract, and two verified callers compare or assert on `ctx.Value(k)`

- **Spec.** `Spec/context/Api.lean` states no triple for `ctx.Value(k)` under `ctxOk`. The only `Value`
  call it covers is grpc's metadata key, inside the transparent `ctxNoMeta` (`:171`). `ctxValueAt`
  (`:151`) does not even record the value stored. The header says "everything else the client does
  with a context is to pass it to gRPC" (`:31`), which is false.
- **Go.**
  - `client/v3/lease.go:296` stores `context.WithValue(ctx, keepAliveCtxKey{}, &ctx)`.
    `keepAliveCtxCloser` then compares `c.Value(keepAliveCtxKey{}) == ctx.Value(keepAliveCtxKey{})`
    at `lease.go:368`. That needs the call's spec and comparable results: the `==` of two
    interfaces of one uncomparable dynamic type panics.
  - `server/etcdserver/v3_server.go:1022` calls `ctx.Value(traceutil.StartTimeKey{}).(time.Time)` (a
    checked assertion: it needs only the call's spec).
- **Coverage.** The old tree's `specs-ref/Spec/context/ValueKeepAlive.lean` and `ValueStartTime.lean`
  have no counterpart.
- **Users not served.**
  - 1c's `lessor.keepAliveCtxCloser.spec`. Its sketch "compared by the `keepAliveCtxKey` value" has
    no callee spec; through it, `lessor.KeepAlive`.
  - 2c's `EtcdServer.raftRequest` sketch.
  - 1b's `valCtx_ctxOk` (`WatchInternal.lean:154`) forwards `Value` to its inner context, which
    makes the bundle's `Value` member part of what it must preserve.
- **Fix.**
  - Add `Context.Value.spec : {{ ctxOk ctx }} ctx.Value(k) {{ v, RET #v; True }}`.
  - Record the value in `ctxValueAt parent ctx' key v`, with
    `ctxValueAt_value : ctxValueAt parent ctx' k v ⊢ (ctx'.Value(k) returns v)` and, at another
    key, the parent's value.
  - Or give 1c a local premise on the keep-alive contexts, as the old `keepAliveOk`.

  Not recorded. `batch-W0.md`'s C-S4 fixed `WithValue`, not `Value`.

## Second tier

- **S1. zap specs missing for fields and methods that specced callers use.** This is W0's own
  "not done" C-S5 (`batch-W0.md:228`), so it is recorded, but its users are not served:
  - `zap.Float64`: `client.go:497`, which is `Client.roundRobinQuorumBackoff`; its sketch says only
    "the logger's `Debug`". Also `server.go:1623`.
  - `zap.Time`: `api/v3rpc/interceptor.go:188,204`, which is `logUnaryRequestStats`; its sketch cites
    "W0's `Zap`" for the logger's level. Also `server.go:917`.
  - `Logger.Core().Enabled`: `interceptor.go:94`.
  - `zap.Binary`: mvcc `kvstore_txn.go:135`.
  - `Logger.Named`: `client.go:401`, out of scope by `cfgOk`'s `LogConfig` premise.
  - `WithOptions`/`Sugar`: `backend.go:1137`, assumed there.

  Add trust-boundary specs for `Float64`, `Time`, `Binary`, `Logger.Core`, `Core.Enabled`,
  `Logger.Named`, `Logger.With`, `WithOptions`, `Sugar` and `Sync`, in the shape of the existing field
  constructors.
- **S2. Wrappers that cannot meet `kvAt` at all.** `client/v3/namespace/kv.go` rewrites keys. Its
  `prefixCmps` (`kv.go:200-207`) also writes into a cloned `Cmp`'s `Compare` (`WithKeyBytes`,
  `GetCompare().RangeEnd = …`), for which no spec exists (`Cmp.WithKeyBytes`,
  `Cmp.WithValueBytes`). Namespace has no spec in either tree, so the gap is old. With F2's
  introduction, namespace would need a contract of its own (as leasing's `lkvAt`) and
  `clientRest`. Note only.
- **S3. Doc inconsistency.** `OpM.putPanics` (`Api.lean:275-279`) says "the model of a range end
  does not say whether an empty one is nil". `OpM`'s own doc (`:152-154`) says it does: `none` is
  `nil`, `some []` a non-`nil` empty slice. The condition `rangeEnd ≠ none` is exactly `OpPut`'s
  `op.end != nil` check; only the sentence is wrong.
- **S4. Outside the area, seen while checking callers.**
  - `grpc/ClientConn__Invoke.lean:16` cites "V3rpc's `servesAt_serves`", which exists nowhere. It
    concerns `servesAt`, a predicate of this area's `State.lean`.
  - The old tree's 35 Kubernetes `apiserver/pkg/storage/etcd3` specs (`store__*`, `compactor__*`,
    `Compact`) have no counterpart and no batch in `batches.md` owns them. The Kubernetes store and
    compactor are therefore users checked by their Go code only.

## Users: patterns, snippets, one call site each

Every reliance below is checked against the specs as they are at HEAD. ✓ means a snippet covers the
pattern and the call site's pre and post fit; ✗ means it fails (the finding is named).

| # | Pattern (what the caller relies on) | Call site checked | Snippet | |
|---|---|---|---|---|
| P1 | read after an acknowledged write sees it | `examples/etcd/compactwatch/compactkv.go:73-95` | `ReqPutThenGet` | ✓ |
| P2 | a put's header revision; `WithPrevKV` | election `Proclaim`; compactkv's `Compact(presp.Header.Revision-1)` (≥ 1: a put's revision is ≥ 2, so `rev ≠ 0` holds) | `ReqPutRevision` | ✓ |
| P3 | delete | `concurrency/mutex.go:144` | `ReqDeleteThenGet` | ✓ |
| P4 | prefix, limit, `More` implies non-empty `Kvs`, `Count` | k8s `watcher.go:347-354` | `ReqListPrefix` | ✓ |
| P5 | paging from `lastKey+"\x00"` at a pinned revision | k8s `watcher.go:369-373`, `kubernetes/client.go:65` | `ReqListPrefix` + `ReqGetAtRevision` (the model's `storeAt`) | ✓ |
| P6 | CAS on mod revision, both branches at one state | `kubernetes/client.go:84` (OptimisticPut spec fits: `isClient_KV`, `KV.TxnTriple`, `Txn.*Triple`) | `ReqCASModRevision` | ✓ |
| P7 | create-if-absent; the else branch's `Kvs[0]` exists | `mutex.go:123`. `Mutex.tryAcquire`'s sketch fits: `etcdLent` builds the exclusive update, the failed compare means the key is in `s0`, and the else get reads `s0` | `ReqCreateIfAbsent` | ✓ |
| P8 | a txn reads its own writes | `mutex.go:123` (put then `getOwner`) | `ReqTxnReadsOwnWrites` | ✓ |
| P9 | nested range headers are the txn's read revision | `stm.go:288-292`, `stmSerializable.Get` | `ReqTxnNestedRangeHeaders` | ✓ |
| P10 | nested txn's compare before the outer writes | `leasing/txn.go:206` | `ReqTxnNested` | ✓ |
| P11 | read-only serializable txn at a stale view | `stm.go:288` with `WithSerializable` | `ReqTxnReadonlySerializable` | ✓ |
| P12 | `Op` getters | `leasing/util.go`, `cache.go` validateGet | `ReqOpGetters` | ✓ |
| P13 | `Do` answers in its kind's field | `leasing/kv.go:313`, `ordering/kv.go:63` | `ReqDo` | ✓ |
| P14 | serializable get | `stm.go` (stmSerializable) | `ReqSerializableGet` | ✓ |
| P15 | count-only, keys-only, `withTop`, revision filters + sort + limit | `cache.go:261`, k8s `store.go:711`, `concurrency/key.go:55` | `ReqGetOptions` | ✓ |
| P16 | `errors.Is`/`==` against rpctypes errors | k8s `interpretListError`; `errorsIs_errVal`'s pre is met by both of `getReply`'s error forms | `ReqPutErrors`, `ReqGetErrors` | ✓ |
| P17 | get at a revision; `ErrCompacted` | k8s `kubernetes/client.go:48` | `ReqGetAtRevision` | ✓ |
| P18 | compact at a reached revision after a CAS | k8s `compact.go:220-247`: the `rev == 0` check precedes `Compact`, so the premise is met | `ReqCompactReached` | ✓ |
| P19 | streamed list: chunks, final header and `Count`, `More` | k8s `store.go:951-1001`, `watcher.go:391-419` | `ReqGetStream`, `ReqGetStreamCompacted` | ✗ F1 |
| P20 | a `KV`/`Txn` wrapper standing for the client's | k8s `factory/etcd3.go:468`, `latency_tracker.go` | none | ✗ F2 |
| P21 | `context.TODO()` as a call's context | `recipes/client.go` (`deleteRevKey`), `key.go` | none (recipes' own) | ✗ F3 |
| P22 | forwarded token: a valid one (`v3lock`, proxy) / an unissued one | `examples/etcd/auth/authkv.go:153-155` | 1c's `ReqRefusedPrincipals` | valid ✓ (`ctxPrin_token`); unissued ✗ F4 (recorded) |
| P23 | `ctx.Value(k)` on the caller's context | `lease.go:368`, `v3_server.go:1022` | none | ✗ F5 |
| P24 | writing into or keeping a reply | k8s `watcher.go:357` (`Kvs[i] = nil`), namespace unprefixing, `cache.go:344` (`Restore`) | — (`rangeRespOwn` at `own 1`, `replyPersist`, `msgOwn_discard_persistent`) | ✓ |
| P25 | logging fields | `client.go:497`, `interceptor.go:94,188` | — | ✗ S1 (second tier) |

## Callers' specs on the branch (sampled)

These use the area's names, and the names exist. Each checked for premise sources and post
sufficiency:

- **Fit:**
  - concurrency: `Mutex.tryAcquire`, `stm.fetch`, `stm.commit`. For the read-only transactions,
    `etcdPeek` suffices, because `kvStep`'s `.range` and a read-only `TxnRun` leave the state
    unchanged.
  - cache: `Cache.serverRevision`.
  - kubernetes: `Client.OptimisticPut`.
  - leasing: `kvAt_lkvAt` and `txnAt_ltxnAt`, which follow from `kvAt_methods` and `txnAt_methods`.
  - 2a: `rangeStreamSpec` agrees with `streamMatches`.
  - 3h: `kVClient.Put`.
- **Do not close:**
  - `deleteRevKey` and `newSequentialKV` (F3).
  - `lessor.keepAliveCtxCloser` and `EtcdServer.raftRequest` (F5).
  - `Client.roundRobinQuorumBackoff` and `logUnaryRequestStats` (S1).

A scan for cited law names that exist in no file found `servesAt_serves` (S4) and
`isClient_conn`/`clientRest_conn`. The latter two appear only in a comment that records their
removal.

## Coverage against the old tree

- `client/v3`: every file of `specs-ref/Spec/go_etcd_io/etcd/client/v3/` (including the
  subpackages) has a counterpart.
- `zap`: all old files are present: `Defs` became `Api`, plus `Any` and `NamedError`.
- `context`: the old `Err`, `ErrAny`, `ErrDone`, `TODO`, `WithCancel*`, `WithTimeoutBackground`,
  `WithTimeoutBackgroundMd` and `WithValue` are covered by `Err`, `ErrDone`, `TODO`, `WithCancel`,
  `WithTimeout`, `WithValue` and `ctxNoMeta_*`. `ValueKeepAlive` and `ValueStartTime` are not (F5).

## Counts

- **Specs:** about 161 files in the area: 4 vocabulary files, about 131 client files on the KV path,
  26 zap files.
  - Read in full: the 4 vocabularies, the 7 `kv.*`, `txn.Commit`, `Client.Get`, `NewKV`,
    `NewKVFromKVClient`, the `Cmp` and `Op` accessors namespace uses, `OpResponse.Get`,
    `WithRequireLeader`, `withVersion`, `ContextError`.
  - The rest: checked for existence and for the users' option and accessor needs.
  - First-tier problems: `KV.GetStreamTriple` and `streamAt_recv` (F1); the `kvAt`/`txnAt`
    vocabulary (F2); `ctxPrin_todo` (F3); `ctxPrin` (F4); `Context/Api` (F5).
- **Snippets:** all 23 of `clientv3kv` checked for the pattern each covers. 22 rely only on what the
  specs give. `ReqGetStream` cannot be met by any caller holding only its own thread token (F1).
  Also 1c's `ReqRefusedPrincipals`, which does not close (F4).
- **Users:** about 60 call sites over 25 patterns (etcd's concurrency, recipes, leasing, kubernetes,
  cache, mirror, ordering, namespace, v3lock; Kubernetes' store, watcher, compactor, latency
  tracker and factory; the examples `putget`, `putget3`, `compacted`, `compactwatch`, `auth`,
  `restart`, `partition`, `txnlin`, `k8s/compactor`, `k8s/etcd3`, `lib/etcdstart`). 20 patterns
  close; 4 fail at first tier (one of them recorded) and 1 at second tier.
- **Callers' specs sampled:** 13; 9 fit, 4 do not (F3, F5, S1).

No new bug in the Go code. The leaking `GetStream` goroutine is already
`nonissues/etcd-client-getstream-abandoned-leak.md`.
