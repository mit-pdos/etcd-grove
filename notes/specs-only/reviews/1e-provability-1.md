# Batch 1e (leasing KV): provability review, round 1

Reviewer: provability. Read: `SpecPlan/Spec/go_etcd_io/etcd/client/v3/leasing/{Api,Internal}.lean` and the 66
specs (statements of all; sketches of the write, get, txn and monitor paths), the snippets
`examples/specreq/leasing/*.go`, the `## from 1e` requests, W0's `api/v3/{Model,State}.lean`,
`client/v3/Api.lean`, `context/Api.lean`; the Go code `.lake/src/client/leasing/{kv,cache,txn,util}.go`,
`.lake/src/client/op.go`, `.lake/src/server/proxy/grpcproxy/kv.go`,
`.lake/src/server/etcdserver/api/v3rpc/key.go`; the `leasing-*` issues in `specs-ref`. Findings were
written before reading `batch-1e.md`; where the author already reports one, it says so.

## First tier

### F1. The single-operation write path is unprovable over W0's transaction model (empty key, `IgnoreValue` with a value, `IgnoreLease` with a lease)

Every leasing write of one key is sent as a guarded transaction (`tryModifyOp`, kv.go:227-228;
`revoke`, kv.go:425-426; a range delete's `deleteRangeRPC`, kv.go:352-357), and the sketches of
`leasingKV.tryModifyOp`, `revoke`, `deleteRangeRPC` (and so `put`, `delete`, `deleteRange`, `Put`,
`Delete`, `Do`) fire the caller's update `some res` at the transaction's success, citing "the guard
held and the branch is the operation alone, a pure fact of the model". That fact is false of W0's
model:

- `kvStep (.put p)` succeeds only if `p.invalid = none` (Model.lean:638-642, 833-844: no empty key,
  no `IgnoreValue` with a value, no `IgnoreLease` with a lease); `kvStep (.deleteRange d)` only if
  `d.key ≠ []` (Model.lean:845-853);
- `kvStep (.txn t)`'s success disjunct (Model.lean:886-903) runs `TxnRun`, whose `put` case checks
  only `p.check` (leases, `keyNotFound`: Model.lean:632-635, 698-705) and whose `deleteRange` case
  checks nothing (706-711). The gRPC-layer refusals are a separate, unconditional error disjunct.

So the model lets `If(CreateRevision(pfx+k) < 1).Then(OpPut("", v))` succeed, committing a put of
`""`. At that commit the leasing proof must produce `etcdState γ σ'` from the caller's update (whose
`LStep` for `.put p` with `p.invalid ≠ none` has no successful `Step`, and `CachedAns` of a put is
`False`) or from `protoUpd` (`""` is not under a non-empty `pfx`): neither fits, so the inner
`Commit`'s update cannot be built. The pres admit these inputs: `LKV.PutTriple` excludes only
`putPanics` (`OpPut("", v)`, `OpPut(k, "v", WithIgnoreValue())`, `WithIgnoreLease()` + `WithLease`
do not panic), `LKV.DeleteTriple` only `deletePanics`, and `Do` takes the proxy's ops as they come.

The Go code is fine: etcd validates every operation of a transaction before applying it
(`checkTxnRequest` → `checkRequestOp` → `checkPutRequest`/`checkDeleteRequest`,
`server/etcdserver/api/v3rpc/key.go:182-200, 324-338`), so the leasing write returns the refusal
as an error, which the leasing post allows. The gap is W0's model being looser than etcd.

Affects: every client of `Put`/`Delete`/`Do` (the specs are false-as-provable, not false of the
code). Fix (a W0 request, not a leasing premise, since the code returns an error): in `kvStep
(.txn t)` the success (and the in-run error) disjuncts require the per-level validation to pass
(each `RequestOp`'s `invalid = none` at every depth, no empty compare key, the duplicate-key check;
exactly the refusals the first disjunct lists), as `checkTxnRequest` does. Then "guarded success ⇒
the operation's `Step`" holds and the sketches stand. Add it to `req/go_etcd_io_etcd_api_v3.md`
(`## from 1e`) and cite it in the three sketches.

### F2. "Any value meeting W0's contract meets the leasing contract" is false as stated (claim (c))

`Api.lean`'s header (and `batch-1e.md`) claims a `kvAt` value meets the leasing contract for any
`pfx`, so clients can be written once over it. Three gaps:

1. **Transactions.** `LKV.TxnTriple` returns `ltxnAt iv γ who pfx ctx TxnSt.empty`, and
   `LTxn.*Triple` are about `ltxnAt`, which is opaque, introduced only by the leasing package's own
   `Txn`. Nothing turns W0's `txnAt` into `ltxnAt`, so a plain KV's `Txn` cannot meet
   `LKV.TxnTriple`, and `Commit` cannot be reached.
2. **The bundle.** `lkvAt v γ who pfx γL` is opaque with only `isLeasingKV_lkvAt` as introduction,
   and `Get`/`Do` also need `lkvOpen γL q`, which only `NewKV` produces. A client written over
   `lkvAt ∗ lkvOpen` (the proxy, whose client may or may not be a leasing one: 1e's own W0 request 1
   asks W0 for a client whose KV field meets "another contract") cannot be given a plain KV.
3. **A range delete with `WithPrevKV`.** A W0 value fires its update with `Step who (.deleteRange d)`
   at `d.prevKv = true`: its answer carries the previous key-values `l`, and the step also checks
   read permission on the range (Model.lean:750, 845-853). `LStep`'s answer case is
   `Step who (execReq rq) ...`, at `prevKv = false`: answer `[]` and only the write permission.
   When `l ≠ []` (or the read permission is missing) the W0 step is not an `LStep`, so the update
   cannot be passed down and the reply (with `PrevKvs`) does not match the `res` given to `Q`.

(Also `KV.*Triple` does not give back `P`; harmless for the persistent `kvAt`.)

Fix: (3) `LStep pfx who rq σ σ' (some res) := Step who rq σ σ' res ∨ Step who (execReq rq) σ σ' res
∨ (σ' = σ ∧ CachedAns rq σ res)`: still true of leasing, and W0's step is now a case. (1, 2) State
`lkvAt` and `ltxnAt` as W0 intends `txnAt`: transparent existential bundles (a state predicate with
the triples over it; `lkvAt v γ who pfx γL := □ (the five LKV triples at P := lkvAt ∗ lkvOpen γL _,
plus W0's Compact and GetStream)`), or add the laws `kvAt_lkvAt.spec : kvAt v γ who ⊢ lkvAt v γ who
pfx γL` (for every `γL`), `lkvOpen_alloc.spec : ⊢ |==> ∃ γL, lkvOpen γL 1` and `txnAt_ltxnAt.spec`,
and add a snippet that runs one client function over both a plain and a leasing KV (the proxy's
pattern).

### F3. `ReqNewKVProxy` is unprovable (`cli.KV = kv`)

`lifecycle.go`'s `ReqNewKVProxy` assigns `cli.KV = kv` after `leasing.NewKV(cli, pfx)`. `NewKV.spec`
takes `isClient cl γ who`, whose KV field is `↦□` (`client/v3/Api.lean:915`): no write permission.
W0's `clientMut` has it, but `clientMut_KV`/`clientMut_freeze` need `kvAt` of the new value, which a
leasing KV is not (F2). So the snippet's write cannot be proved, and after it the client is neither
`isClient` nor `clientMut`. Already recorded by the author (`req/go_etcd_io_etcd_client_v3.md`,
`## from 1e` item 1; `batch-1e.md`, open question 2): first tier until W0 answers. The fix should
be designed together with F2: the frozen client's KV field should hold a value meeting the leasing
contract, which both a plain KV and a leasing one meet once F2 is repaired. Also `NewKV` should take
the client with its KV field still writable, as the proxy calls it.

## Second tier

### S1. Go findings: the author's three are real; two more; none is in `issues/`/`nonissues/` yet

The author reports these in `batch-1e.md`, but they are not filed (CLAUDE.md: record when found).

1. **A range delete drops `WithPrevKV`**: real. `deleteRange` (kv.go:373-388) calls
   `deleteRangeRPC(ctx, maxLeaseRev, key, end)`, which builds `OpDelete(key, WithRange(end))`
   (kv.go:356) from the key and the range end only, and returns `Responses[1]` (kv.go:368). So
   `Delete(ctx, p, WithPrefix(), WithPrevKV())` returns `PrevKvs == nil`. Deterministic: goes to
   `issues/` with a failing test (`UnmetDeleteRangePrevKV` is its shape).
2. **`gatherOps` writes into the caller's memory**: real, and harmless where etcd uses it.
   util.go:598, `gatherOps(append(thenOps, elseOps...))` on a nested `Op`'s `thenOps` (`op.Txn()`
   returns the `Op`'s own slices, op.go:94-96; `OpTxn` stores the caller's slices uncloned,
   op.go:330-336) writes `elseOps` into `thenOps`' spare capacity: within capacity, so no panic,
   but it changes a caller's array (and is a data race if two goroutines commit transactions
   sharing such an `Op`). The proxy's `TxnRequestToOp` builds slices with `make([]Op, n)`
   (grpcproxy/kv.go:230-243): no spare capacity, so `append` allocates. Goes to `nonissues/`.
3. **A `WithFromKey` (or empty-key or all-`0xff` `WithPrefix`) delete skips revocation**: real by
   code reading. `WithFromKey` sets `end = "\x00"` (op.go:445-452; `WithPrefix("")` sets key and
   end to `"\x00"`, op.go:427-429). `inRange` treats `"\x00"` as open-ended (cache.go:79), but
   `revokeRange` reads `Get(pfx+key, WithRange(pfx+"\x00"))` (kv.go:434-438), an empty range for
   every key ≥ `"\x00"`, so no other client's lease is revoked. `deleteRangeRPC`'s guard over the
   same empty range compares the zero key-value, so it holds (kv.go:353). The delete then removes
   `[key, ∞)`, which may include other clients' lease keys: their `monitorLease` ignores deletes
   (it reacts only to `"REVOKE"` values, kv.go:180), so they keep serving stale cache. The same
   holds in a transaction's `guardRanges` (txn.go:423, 440). Reachable with two leasing clients
   (`Delete(ctx, "", WithPrefix())`): goes to `issues/` with a test. Does not block the weak
   contract.
4. **New: a transaction can loop forever on the client's own lease key**, by code reading. After
   a `serverTxn` error, every compared key is evicted (txn.go:503-505, `Evict`), but the lease key
   `pfx+k` stays, with this client's lease. A later write transaction on `k` then compares
   `CreateRevision(pfx+k) < Rev(k)+1 = 1` (`guardKeys`, txn.go:409-410), which fails. Its fallback
   reads `pfx+k`, and `revokeLeaseKvs` skips it as its own (kv.go:451-454). Nothing changes, so
   `serverTxn`'s `for` (txn.go:496-517) resends the same transaction until `txn.ctx` ends: forever
   with a context that has no deadline, a busy loop of RPCs. (A `put`/`delete` recovers: `revoke`
   puts `"REVOKE"` on its own key and its monitor rescinds it. A `Get` of `k` two seconds later
   re-adds the entry.) A liveness bug; the triples are partial, so the specs are unaffected.
   `issues/` with a test if it reproduces, else `nonissues/`.
5. **New: `monitorLease` spins on the caller's context**, by code reading. `monitorLease(ctx, ...)`
   re-reads the lease key with the `Get`'s own context (`lkv.kv.Get(ctx, ...)`, kv.go:164) and
   `continue`s on error, in a loop bounded only by the KV's context (kv.go:162). This path runs
   once the watch channel closes without a `"REVOKE"` (kv.go:189: e.g. the watch canceled because
   its start revision was compacted on a reconnect). If the request's context is already done (the
   proxy's per-RPC context always is by then), the loop spins at full CPU until `Close`. How often
   the watch closes early is uncertain (not run). A liveness and resource bug.

(Minor, same family: `acquire` retries forever on an error that is neither an `EtcdError` nor a gRPC
status, kv.go:300-306, bounded only by `ctx`.)

### S2. `flatTxn` is stronger than the code needs and excludes a real proxy pattern

`LKV.DoTriple`'s `flatTxn` and `LTxn.{Then,Else}Triple`'s "no transaction" premise exclude nested
transactions. The proxy passes them through `Do` (`requestOpToOp` → `TxnRequestToOp`,
grpcproxy/kv.go:154-173, 230-243), and the code is safe for them because those slices have no
spare capacity (S1.2). Under PRINCIPLES "no unneeded premise", the premise should be what the code
needs: each nested transaction's branch slices have no spare capacity, or their capacity is owned.
That needs W0's `opAt` to expose it (author's decision 3). Keep it as the user decision it is, and
mark it in the `Do` docstring as a scope restriction that excludes the proxy's nested transactions.

### S3. The header's account of the four reasons, checked against the code (claim (a))

1. **Double commit and resend**: true. `tryModifyOp` returns a nil waiter for an uncached key
   (cache.go:53-61 → kv.go:226, 243), and `put`/`delete` read `wc == nil` as "not committed" and
   send it again through `revoke` (kv.go:252-253, 400-401). After an error they also resend
   (same lines, and `tryModifyOp`'s `Evict` path, kv.go:230-236).
   `issues/leasing-modify-uncached-once.md` has the failing test.
2. **Lease-key writes, `"REVOKE"`, session**: true (kv.go:281-290, 426, 198-201; `NewSession` in
   `monitorSession`, kv.go:147). `revoke`'s single transaction that is either the caller's write or
   the `"REVOKE"` put is real (kv.go:425-426).
3. **Cached reads not linearizable**: true under W0's default configuration. But the header says
   "W0: at any time", while W0 has `EnvCfg.leaseExpiry = false` (Model.lean:1127-1131). Under that
   configuration the expiry window closes, and what still breaks W0's `Get` is the stale header
   (cache.go:220 → `copyGetResponseMetadataOnly`: the answer's revision is the entry's, not
   `σ.kv.rev`), writers that do not go through leasing, and the bugs. `batch-1e.md`'s decision 2
   says so; `Api.lean`'s header should too.
4. **Errors passed through**: true. `acquire` returns an `EtcdError` as is (kv.go:300-303), e.g.
   `ErrLeaseNotFound` once the session's lease is gone. W0's `Get` cannot answer that
   (`leaseNotFound` is neither a refusal, Model.lean:321-326, nor a range error). A write's
   resend can also turn a committed first attempt into a definite error of the second (a
   `WithLease` put whose lease is revoked in between: `ErrLeaseNotFound` after the put took effect).

### S4. A write may take effect after it has returned: say so

With the update persistent, the contract lets a write fire after `Put` returned success, and the
code does this. A first attempt that failed indefinitely (`tryModifyOp`'s error path) may still
commit after the resend through `revoke` succeeded and returned. So after `Put(k, v1)` and then
`Put(k, v2)`, both successful, `k` may later be `v1`. That is a real difference from W0, where a
write that returned success fires no more. Say it in `LKV.PutTriple`'s and `DeleteTriple`'s Margin
and in the header's reason 1: a client's invariant must stay stable under a late re-application of
every leasing write it ever issued. (None of the snippets is affected.)

### S5. Header inaccuracy: thread tokens

"every call but `Compact`, `GetStream` and `Txn` takes a thread token" is wrong: W0's
`KV.GetStreamTriple`, which `GetStream` meets, takes one (`client/v3/Api.lean:700`, given back only
on the error branch). Say: every call but `Compact`, `Txn` and `If`/`Then`/`Else`.

## Checks that pass

**(b) The contract on every path.** Each path checked against the code:

- **`Get`.**
  - `do()` (kv.go:312-318, 322-331): W0's `Do`, with the update restricted to `Step`.
  - A cached answer (`leaseCache.Get`, cache.go:191-210): copied under the read lock; fresh header
    (`copyHeader`) and key-values (`copyKeyValue`), so `getReply`'s `own 1` holds. `More`/`Count`
    are copied, kept false and `≤ 1` by every writer of an entry (`Add` from `OpGet(key)`'s answer,
    `Update` cache.go:138-151, `delete` cache.go:160-165). The revision is reached (`etcdLb` in the
    invariant).
  - An acquisition: a `ProtoStep` (its only write is `pfx+key`), then `Add`'s copy, or, when the
    acquisition fails, the plain `OpGet(key)` answer fired as `CachedAns`. That answer has at most
    one key-value, of `key`, and its revision is the transaction's. Correct, since the options are
    ignored there (`issues/leasing-get-failed-acquire-options.md`).
  - No nil-map write: `Add` runs only after `waitSession`, after `monitorSession` made `entries`.
- **`Put`/`Delete`.**
  - Every `Responses[0]`/`Header` dereference follows `Succeeded` (kv.go:258-263, 408-411).
  - The waiter channel is closed once: `tryModifyOp` returns nil on its failure paths after closing
    its own.
  - The `"REVOKE"` put with `WithIgnoreLease` is on the else branch, taken only when `pfx+key`
    exists (`0 < rev+1` otherwise), so it cannot hit `keyNotFound`.
  - Revisions: a guarded transaction's revision is `v.rev+1` with a write, `v.rev` without
    (Model.lean:903), equal to the bare operation's.
  - Permissions: the transaction's permission set contains the operation's (`RequestOp.perms`,
    Model.lean:744-753), so a permitted transaction permits the operation. The only gap is F1's.
- **`Commit`.**
  - `eval`: under the read lock; `lc.header == nil` is checked (txn.go:372). Its answer is
    `CachedAns` for whichever branch, the header reached.
  - `serverTxn`:
    - the outer transaction (a write, since nested) has `v = σ.kv`. Its success is the user
      transaction's `Step` (the same `TxnRun` from `(s0, [])`, the same revision, the permissions
      and leases a superset). This direction holds even with W0's loose validation, since both
      sides are loose alike.
    - its failure branch reads only, and `revokeFallback` is `ProtoStep`s.
    - `commitToCache`: one level deep under `flatTxn`; `Update` keeps the shared header, hence
      `txnReplyL`'s `discard`.
    - `append(txn.opst, txn.opse...)` writes into `txnLeasing`'s own capacity.
- **Concurrency.**
  - Every read of an entry's response is under the read lock, every write under the write lock
    (`put` kv.go:259-261, `commitToCache`, `Delete`, `Add`). There is no nested locking.
  - `Update` keeps the caller's key and value bytes, which are read-only in `opAt`.
  - `closedCh` is never closed twice (`Lock`/`LockRange` replace it).
  - `wg.Add(1)` in `get` is ordered before `Close`'s `Wait` by the open-token share, as
    `nonissues/etcd-leasing-get-during-close-waitgroup.md` requires.
  - The forked monitor gets its thread token from the fork (`wp_fork_tok`, Perennial
    `GooseLang/BoundedLang.lean:39`).
  - `ctxOk` is persistent (`context/Api.lean:70`), so `monitorLease` may keep the caller's context.
- **`GetStream`.** `status.Error(Unimplemented)` is `callErr .other`, which is indefinite
  (`client/v3/Api.lean:425-428`), given 2a's request.
- **`Close`.** The open token excludes a concurrent `Add`; the result holds as a partial triple.

**(c) for the rest.** For `Get`, `Put`, single-key `Delete`, `Do` (non-range-delete), `Compact` and
`GetStream`, the triple families are implied by W0's (□-elimination, the update restricted, the
`Wire.lean:260-267` discard law for the read-only replies, `indefCall_pure` for `err ≠ nil`).

**(d) Is the contract useful?** For writes, yes: a successful leasing write applied the request's
own `Step` at least once, so a later read through the plain client sees it (`ReqPutRevision`,
`ReqDeleteThenPlainGet` are provable). For revisions, yes: a reply's revision is one the cluster
reached (`ReqGetThenPlainGet`, `ReqTxnReadOnly`). For the shape of a `Get` reply, yes
(`ReqGetKey`). For the content of a read, no: a cached answer says nothing of the key's value,
version or revisions, so no snippet can prove anything about what a leasing reader reads, and no
spec could, given `issues/leasing-update-stale.md` (values etcd never had). That is honest. One
cheap strengthening is true of the pinned code: a cached key-value's `ModRevision` and
`CreateRevision` are at most its header's revision, and its value is one a put of the key carried,
or empty (`Update` with `IgnoreValue`). Optional.

**(f) Snippets.** The 12 others are provable. Sketches:

- `ReqGetKey`: `Q := ⌜LStep … (some res)⌝`. A `Step` of a one-key range or `CachedRange` gives at
  most one key-value, of `k`; `getReply`'s header and `rangeRespOwn_unfold` give `Header ≠ nil`.
- `ReqGetThenPlainGet`, `ReqTxnReadOnly`: `Q` also keeps `etcdLb γ σ`. Then `etcdLb_reach` plus
  the revision being monotone along `Reach`, and `etcdState_revFits` for the `int64` comparison.
- `ReqGetStreamUnsupported`: W0's triple.
- `ReqPutRevision`, `ReqDeleteThenPlainGet`: every `some` firing is the request's `Step` (no
  `CachedAns` for writes), and `none` firings touch only `pfx` keys. The owned key must be outside
  `pfx`, as the common assumptions say. All firings write the same value or delete.
- `ReqPutError`, `ReqCompactThroughLeasing`, `ReqNewKVClose`: `lkvOpen_split`, then
  `closeFnAt_call` with the whole token.
- `ReqDoProxyRange`, `ReqDoTxn`, `ReqTxnCAS`: `doReplyL`/`txnReplyL` give a non-null reply
  (`msgOwn_ne_null`, `txnRespOwn_unfold`), the reply's kind fixed by `LStep`/`CachedAns`.

`unmet.go`: each of the six is unprovable from the specs (the persistent update, `CachedRange`
without values, `execReq`, `CachedAns`'s free branch), and each panic is reachable in Go:

- `UnmetPutOnce`: `issues/leasing-modify-uncached-once.md`.
- `UnmetRevisionsMonotone`: deterministic, the second `Get` is served from the entry with the
  acquisition's header.
- `UnmetGetOptions`: `issues/leasing-get-failed-acquire-options.md`.
- `UnmetDeleteRangePrevKV`: deterministic, S1.1.
- `UnmetTxnMissingKey`: deterministic. `evalCmp` gives result 0 for a missing key (util.go:556),
  so `<` fails, the empty else branch is evaluated from the cache and `Succeeded` is false.
- `UnmetReadAcross`: `issues/leasing-stale-entry-after-reset.md`, or the lease-expiry window.

Its header also lists `issues/leasing-wait-rescind-no-delete.md`, which is about range deletes, not
this snippet's `Put`: drop it or add a range-delete variant.

## Targets ranked by need of revision

1. **`Api.lean`**: F2 (the weakening claim; `LStep`'s answer case; bundles or bridging laws), S3.3,
   S4, S5.
2. **The single-key write specs** (`tryModifyOp`, `revoke`, `deleteRangeRPC`, `put`, `delete`,
   `deleteRange`, `Put`, `Delete`, `Do`): F1. The statements are fine once W0's transaction model
   requires validation; file the request and cite it in the sketches.
3. **`NewKV.spec` and `lifecycle.go`**: F3 (pending W0, together with F2).
4. **`Do`/`Then`/`Else`**: S2 (`flatTxn`, a user decision).
5. **`Internal.lean`, the cache specs, `eval`/`serverTxn`/`Commit`, the monitors, `reads.go`,
   `writes.go`, `txn.go`, `unmet.go`**: no change needed beyond the `unmet.go` header line.

Go findings to file (S1): `issues/` for the `WithPrevKV` drop and the `WithFromKey` revocation skip
(both deterministic), and for the own-lease-key livelock if it reproduces; `nonissues/` for
`gatherOps` and for the `monitorLease` spin if it cannot be triggered.

## Verdict

Not done. The weak contract is a faithful account of the pinned code: all four reasons check out
(one needs qualifying for W0's no-expiry mode), it holds on every path I traced, including revoke,
the transactions and the cache's locking, and it is honest that leasing reads tell nothing about
values. Three first-tier problems remain:

- **F1**: the write specs cannot be proved over W0's transaction model, which lets a transaction
  with an invalid operation succeed. The repair is a W0 model fix.
- **F2**: the claim that W0's KV meets the leasing contract fails, for transactions, for the
  opaque `lkvAt`/`ltxnAt` bundles and for range deletes with `WithPrevKV`. This blocks writing the
  proxy once over both kinds of KV.
- **F3**: `ReqNewKVProxy` is unprovable until W0 provides a client whose KV field meets the
  leasing contract (recorded by the author).
