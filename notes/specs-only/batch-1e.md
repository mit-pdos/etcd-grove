# Batch 1e (the client's leasing KV): report

Author's report. Everything builds (`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/client/v3/leasing`:
68 modules, against W0's round-1 names: `ctxPrin`, `OpResp.range rev a`, `Context.WithCancel.spec`);
the snippets vet (`cd examples && go vet ./specreq/leasing/`, gofmt-clean).

## The answer to "which KV contract does leasing meet" (W0's note, `req/go_etcd_io_etcd_client_v3_leasing.md`)

Of W0's KV contract (`ClientV3.KV.*Triple`) the leasing KV meets **`Compact`** (it delegates) and
**`GetStream`** (always gRPC's `Unimplemented`: an error that settles nothing). It meets none of
`Get`, `Put`, `Delete`, `Do`, `Txn`/`Commit`, for four independent reasons true of the pinned code
(`Api.lean`'s header says each with its code and issue):

1. **Writes are not at most once**: every first write of an uncached key is committed twice
   (`issues/leasing-modify-uncached-once.md`), and a write is resent after an error of its first
   attempt. The caller's update must be persistent.
2. **It writes keys nobody asked for**: lease keys under `pfx` (acquisitions, `"REVOKE"` puts,
   rescinds) and its session's lease grants/keep-alives. And `revoke` sends one transaction that is
   either the caller's write or the `"REVOKE"` put, known only at its commit: one update must cover
   both.
3. **Cached answers are not linearizable**, even with every bug fixed: the protocol fences writers
   by revisions but not cached readers, and a session's lease may expire (W0: at any time) while
   the holder still serves its cache. With the bugs a cached answer is not even a past state's
   (`issues/leasing-update-stale.md` and four others), and its header revision may be below
   revisions the caller saw since (W0's note).
4. **Errors settle nothing**: its own protocol requests' errors (`ErrLeaseNotFound`, permission
   denied on the prefix, its context) are returned as is.

So 1e states **the leasing contract** (`LKV.*Triple`, `LTxn.*Triple`): W0's contract with the
caller's update persistent for every request and over `LStep pfx who rq` (the request's `Step`,
a cached answer `CachedAns` at an unchanged state, or `none`: a protocol step `ProtoStep`), any
error settling nothing, read-only replies for `Put` and `Commit` (their header is shared with the
cache), a range delete without `prevKv` (`execReq`), a thread token per call, and the open token's
share for `Get`/`Do`. It is a weakening of W0's (any `kvAt` value meets it, for any `pfx`).

## Files

| path | what |
|---|---|
| `Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean` (`Leasing`) | the API's vocabulary and the leasing contract |
| `Spec/go_etcd_io/etcd/client/v3/leasing/Internal.lean` (`Leasing`) | the package-internal vocabulary (the lease cache) |
| `Spec/go_etcd_io/etcd/client/v3/leasing/*.lean` | 66 specs: every function with an old spec |
| `examples/specreq/leasing/{lifecycle,reads,writes,txn}.go` | 13 snippets the specs give |
| `examples/specreq/leasing/unmet.go` | 6 requirements of the KV contract's users the code violates (not claimed provable) |

Client-facing (full comments): `NewKV`, `leasingKV.{Close,Get,Put,Delete,Do,Compact,GetStream,Txn}`,
`txnLeasing.{If,Then,Else,Commit}`. Internal (two-line comments, as strong as the contract's
proofs need, no stronger): `leasingKV.{monitorSession,monitorLease,rescind,waitRescind,tryModifyOp,
put,acquire,get,deleteRangeRPC,deleteRange,delete,revoke,revokeRange,revokeLeaseKvs,waitSession,
readySession,leaseID}`, `txnLeasing.{eval,fallback,guardKeys,guardRanges,guard,commitToCache,
revokeFallback,serverTxn}`, `leaseCache.{Rev,Lock,LockRange,LockWriteOps,NotifyOps,MayAcquire,Add,
Update,Delete,delete,Evict,EvictRange,Get,notify,clearOldRevokes,evalCmp,evalOps}`, `leaseKey.get`,
`compareInt64`, `evalCmp`, `gatherOps`, `gatherResponseOps`, `copyHeader`,
`copyGetResponseMetadataOnly`, `copyKeyValue`, `closeAll`, `inRange`, `isBadOp`.

Left out: none (the package's `init` is covered by the law `init.spec`).

## Exported vocabulary (`Api.lean`)

* Pure: `evKey`; `ProtoStep pfx who σ σ'` (no change, a step of `who` whose events are all on keys
  under `pfx`, or a lease grant/keep-alive of `who`); `CachedRange r σ rev a` (rev reached, at most
  one key-value of the key, `more` false, count ≤ 1); `CachedAns rq σ res` (ranges; a transaction
  whose chosen branch, any, is all cached ranges); `execReq` (range delete without `prevKv`);
  `LStep pfx who rq σ σ' : Option Resp → Prop`; `flatTxn`.
* Resources: `LQ Q` (the update's `COMM`); `protoUpd γ who pfx` (def: `□` AU over `ProtoStep`, the
  program's permission, as `envUpd`); `LeasingNames` (opaque type); `isLeasingKV lkv γ who pfx γL`
  (persistent handle); `lkvAt v γ who pfx γL` (persistent bundle); `lkvOpen γL q` (fractional open
  token); `closeFnAt cf γL`; `ltxnAt iv γ who pfx ctx st` (exclusive, W0's `TxnSt`);
  `sessOptsOk osl cl` (**slot, 1d**).
* Replies: `putReplyL`, `txnReplyL` (W0's at `DFrac.discard`), `doReplyL`.
* Contracts: `LKV.{Get,Put,Delete,Do,Txn}Triple`, `LTxn.{If,Then,Else,Commit}Triple`.
* Laws: `handles_persistent`, `lkvOpen_split`, `lkvAt_methods` (the leasing triples plus W0's
  `KV.CompactTriple`, `KV.GetStreamTriple`), `isLeasingKV_lkvAt`, `ltxnAt_methods`,
  `closeFnAt_call`, `sessOptsOk_nil` (1d's obligation).

Internal (`Internal.lean`): `cachedRespOk`, `leaseGetM`, `evalCmpM`, `inRangeM`, `isBadOpM`,
`gatherRespM`/`gatherRespOk`, `bodyRevOp`, `guardedReply`; `lcAt`, `lcHeld`, `cachedRespAt`,
`sessionReady`, `waitCloser`, `waitRecv`, `sessMonitor`; laws `internal_persistent`,
`waitCloser_recv`, `init.spec` (`closedCh`), `isLeasingKV_lcAt`.

## Main changes from the old specs

* **Restated over W0's `etcdState`** as a weakening of the KV contract; the old outcomes
  (`getCached`, `getAcquired`, `getNotAcquired`, `putCommitted`, `commitOutcome`: the cache's log
  states, `entryFacts`) are gone from the API: a cached answer is one step (`CachedAns`).
* **No history premise** (`LeasingProtocol`): the contract claims nothing a protocol violation
  (another writer, a lease expiry, `waitRescind`'s early `nil`) could break. The protocol's
  correctness is now nobody's obligation; it becomes needed only for a stronger contract.
* **Relaxed**: any prefix (was non-empty, `≤ 2^26`), no size bounds (`OpShape`, `sizeOk`), no
  revision certificate (`etcdReached lo`), no `ThreadBoundLe GF (2^29)` on `NewKV`, any context
  (W0's `ctxOk`/`ctxPrin`; was `isCancelCtxCtx` for writes).
* **New**: `protoUpd` on `NewKV` (the protocol's writes are steps the program permits); the
  persistent update for writes; `execReq`; read-only `Put`/`Commit` replies.
* **Internal specs weakened** to what the contract's proofs need (any guard, any revision bound,
  any watch content), over an internal vocabulary (`lcAt`, `lcHeld`) instead of the old exact
  cache transitions over a client part `X` (HoCAP).

## Go findings (by code reading; not yet in `issues/`/`nonissues/`: outside this batch's paths)

1. **A range delete drops `WithPrevKV`** (`kv.go`, `deleteRangeRPC` builds
   `OpDelete(key, WithRange(end))`): `Delete(ctx, pfx, WithPrefix(), WithPrevKV())` through a
   leasing KV returns no `PrevKvs`. Blocks a proof of the KV contract; the spec states it
   (`execReq`). Snippet `UnmetDeleteRangePrevKV`. Should go to `issues/` with a test.
2. **`gatherOps` writes into the caller's memory**: for a transaction operation nested in a
   transaction, `append(thenOps, elseOps...)` writes `elseOps` past `thenOps`' length into its
   spare capacity, which may alias another slice of the caller (and races across concurrent
   `Commit`s sharing an `Op`). Precondition etcd meets (the proxy's `TxnRequestToOp` uses
   `make([]Op, n)`: no spare capacity). The spec restricts user transactions to flat ones
   (`flatTxn`). A `nonissues/` entry.
3. **Suspected** (not checked by a run): a `WithFromKey` (or empty-key `WithPrefix`) delete has
   range end `"\x00"`; `revokeRange` then reads lease keys in `[pfx+key, pfx+"\x00")`, an empty or
   wrong range, so other clients' leases are not revoked before the delete. Irrelevant to the
   weak contract; would matter to a protocol proof.

## Decisions for the user

1. **Spec the pinned code (weak contract) or retarget to the fixes.** The six issue branches
   (`leasing-*` on upamanyus/etcd), plus `put`/`delete` not resending after an error and finding 1,
   would make writes at most once and cached answers a past state's: then `CachedAns` becomes
   W0's serializable read (`Step who (.range {r with serializable := true})`), writes take W0's
   exclusive update, and only "reads are serializable, not linearizable" remains. The vocabulary
   is shaped so that this changes `CachedAns`, `LStep` and the `□` on writes only.
2. **Linearizable cached reads need a time model** (a lease not revoked before its TTL), which W0
   excludes (`EnvStep.leaseExpire` at any time). Without it, no spec can claim the doc's
   "linearizable reads from a local cache"; with `EnvCfg.leaseExpiry = false` (W0's new flag) the
   expiry window closes, but the protocol then needs a premise that every writer of the data keys
   is a leasing client (the old `LeasingProtocol`), a program invariant.
3. **Flat user transactions** (`flatTxn` on `Do`, `Then`, `Else`): a scope restriction from
   finding 2. Alternative: W0's `OpM` records whether a slice has spare capacity, or `opAt` owns
   it, so that the proxy's nested transactions are covered.

## Open questions

1. **The cache's reader slots**: every call that read-locks the cache takes a thread token (given
   back), as the bounds plan has it; the pool itself needs `threadBound` below the `RWMutex`'s
   reader limit, which the old `NewKV` took as `ThreadBoundLe GF (2^29)`. Dropped here (no spec
   mentions `threadBound`); the bounds machinery must supply the fact at the owner.
2. **The proxy's client** (`req/go_etcd_io_etcd_client_v3.md`, from 1e, item 1): W0's `clientMut`
   cannot hold a KV meeting a weaker contract than `kvAt`.

## `req/` sections written (`## from 1e`)

* `go_etcd_io_etcd_client_v3.md`: (W0) a client whose `KV` field meets another contract; (1c)
  `Client.Ctx()` gives `ctxOk` and `ctxPrin`; (1c) the lessor's updates buildable from a
  persistent one; (1b) `Watch`'s channel and events' shape.
* `go_etcd_io_etcd_client_v3_concurrency.md`: (1d) `NewSession` over the `sessOptsOk` slot with
  updates from a persistent lease-grant/keep-alive permission; `Session.Lease`, `Session.Done`.
* `google_golang_org_grpc.md`: (2a) `status.Error(Unimplemented, ...)` is `callErr .other`;
  `status.FromError`.

## Round 1 repairs (2026-11-09)

Reviews: `reviews/1e-provability-1.md` (P), `reviews/1e-completeness-1.md` (C). Built against W0's
round 2 (`TxnReq.valid`, `clientRest`/`clientMut_split`, `etcdPerm`). 68 modules build; the
snippets vet. **This section supersedes the earlier ones where they differ** (the vocabulary below).

**First tier.**

* **P-F1** (guarded single-op success ⇒ the op's `Step`): W0 added `TxnReq.valid` to `kvStep .txn`'s
  applied branch; cited ("`kvStep`'s `t.valid`") in `tryModifyOp`, `revoke`, `deleteRangeRPC`,
  `serverTxn`.
* **P-F2 / C-F4a** (one proof over both kinds of KV): `LStep`'s answer case accepts W0's `Step who rq`
  as well as `Step who (execReq rq)`; new laws `kvAt_lkvAt`, `txnAt_ltxnAt`, `lkvAlloc` (ghost names
  for a plain KV); `LTxn.{If,Then,Else}Triple` give `ltxnAt r` for the returned `r` (W0's new shape).
  Snippet `ReqOneClientBothKVs`.
* **P-F3 / C-F4a** (`ReqNewKVProxy`): `NewKV` takes `clientRest cl γ who` and the `KV` field at any
  share with its `kvAt` (given back), as W0's `clientMut_split` leaves the proxy; `NewSession` over
  `clientRest` requested of 1d (`req/..._concurrency.md`, from 1e round 1).
* **C-F1** (lend an exclusive token so a write cannot land after the return): **not done, false of
  the code.** `put`/`delete` resend after an error of the first attempt (`tryModifyOp`'s error path
  → `revoke`), and that first attempt may still be applied by the cluster after the resend succeeded
  and the call returned; its inner update must be able to fire then, so the caller's token cannot be
  given back (provability S4 found the same). Filed as `nonissues/leasing-write-resend-after-error.md`
  (blocks-proof: yes), stated in the header (reason 1) and `Put`'s Margin, and `UnmetSequentialPuts`
  records the requirement. Decision for the user (with the fixes, below).
* **C-F2**: a cached answer only for a single key at revision `≤ 0` (`CachedRange1`: `isBadOp`
  false), in a cached transaction too. Snippet `ReqGetPrefix`.
* **C-F3** (the old Theorem 1): new `lkvMarks γL M` (persistent: keys that may be written through
  the KV; every write takes the marks of `reqWrites rq`) and `lkvClean γL K` (exclusive; `NewKV` gives
  every key; `lkvClean_split`, `lkvClean_marks`, `lkvClean_mark`, `lkvMarks_none/mono/join`). A
  cached range is W0's serializable answer (`CachedSer`, up to a keys-only answer's lease), or a
  plain get's (the failed acquisition), or, for a marked key or an invalid sort, only its shape. The
  update's step is `lstep γL … := ∃ M, ⌜LStep … M …⌝ ∗ lkvMarks γL M`, so a program holding
  `lkvClean` of a key concludes the serializable case. Internal: `recAtHdr`, `entryOk` (the cache
  keeps, per entry, "the key's record at the header's revision, or the key marked"); `Update`,
  `delete`, `Delete`, `commitToCache` take the marks. `NewKV` again takes `pfx ≠ []` (with an empty
  prefix the acquisition overwrites the data key, and no cached answer is a past state's). Snippet
  `ReqCachedReadUnwritten`. *Uncertain (the reviewer's too)*: that `leaseKey.get`'s `Count` and
  filters agree with `RangeReq.answers` on one key; checked by reading (count = the unfiltered
  `all.length`, the filters as `keeps`), not by a run.
* **C-F4b** (per-request principal): W0's contract fixes `who` per handle; requested of W0
  (`req/go_etcd_io_etcd_client_v3.md`, from 1e round 1, item 5); the proxy snippets model auth off.
  Suspected bypass filed: `nonissues/grpcproxy-leasing-auth-cached-read.md` (blocks-proof: no:
  W0's serializable read may skip the permission check).
* **C-F5**: `flatTxn` dropped; `opCapOk op`/`opsCapOk sl` (persistent; `opCapOk_intro`: not a
  transaction, or branch slices with `cap = len` whose ops are `opCapOk`); `gatherOps` and
  `gatherResponseOps` at any depth (`gatherL`, `gatherRespL`, `respOkL`). `ReqDoTxn` is now nested,
  built as `TxnRequestToOp`.
* **C-F6**: snippet `ReqTxnPositional`.
* **C-F7**: `NewKV` takes 1d's `Concurrency.sessOptsAt osl gs` and `optCtxOk`; the slot `sessOptsOk`
  is gone; `protoUpd := etcdPerm γ (ProtoStep pfx who)` (W0's shape) and `ProtoStep` contains 1d's
  `grantEff` (inlined, any TTL), so `NewSession`'s `effIn` holds. Snippet `ReqNewKVWithTTL`.
* `unmet.go`: `UnmetReadAcross` no longer cites the range-delete issue.

**Second tier done.** P-S1 / the coordinator's list: filed in `nonissues/` (none has a run test yet;
each has its recipe): `leasing-delete-range-drops-prevkv` (blocks-proof: yes; deterministic, move to
`issues/` with its test), `leasing-gatherops-spare-capacity` (no), `leasing-delete-fromkey-skips-revoke`
(no; deterministic, move to `issues/` with its test), `leasing-txn-own-lease-key-livelock` (no),
`leasing-monitorlease-spin-done-ctx` (no), `grpcproxy-leasing-auth-cached-read` (no),
`leasing-write-resend-after-error` (yes); `etc/issues-status.py --index` run, `--check` passes.
P-S3.3 (the `leaseExpiry = false` mode in the header), P-S4 (late application: header, `Put`'s
Margin), P-S5 (thread tokens wording), P-S2 (via C-F5). C §3.2 (`ReqDeleteRangeThenPlainGet`), §3.4
(`UnmetTxnAtomicCache`), §3.6 (the package comment says the proxy snippets model auth off), §3.7
(`ReqDoProxyRange` builds its op as `RangeRequestToOp`). Not done: C §3.1 (two leasing KVs on one
prefix: provable as `ReqPutRevision` with two handles; no new proof obligation), §3.3 (health's
meaning: a note, not filed), §3.5 (a persistent "never closed" open share: a law the proxy may want).

**Vocabulary now** (`Api.lean`): `ProtoStep`, `CachedRange`, `kvUpToLease`, `CachedSer`,
`plainGet`, `CachedRange1`, `CachedAns who M`, `execReq`, `opWrites`/`opsWrites`/`reqWrites`,
`LStep pfx who M`, `lstep γL`, `LQ`, `protoUpd`; `LeasingNames`, `isLeasingKV`, `lkvAt`, `lkvOpen`,
`closeFnAt`, `ltxnAt … γL …`, `lkvMarks`, `lkvClean`, `opCapOk`, `opsCapOk`; replies `putReplyL`,
`txnReplyL`, `doReplyL`; contracts `LKV.*Triple`, `LTxn.*Triple` (now with `γL`); laws
`handles_persistent`, `lkvOpen_split`, `lkvMarks_none/mono/join`, `lkvClean_split/marks/mark`,
`lkvAlloc`, `opCapOk_intro`, `lkvAt_methods`, `isLeasingKV_lkvAt`, `kvAt_lkvAt`, `txnAt_ltxnAt`,
`ltxnAt_methods`, `closeFnAt_call`.

**Decisions for the user, updated.** (1) The pinned code (this contract) or the fixes: with the six
fixes, `put`/`delete` not resending after an error, and the `WithPrevKV` fix, writes would take W0's
exclusive update (no late landing) and every cached answer, marked or not, would be serializable;
the marks would then be unnecessary. (2) Linearizable cached reads need a time model. (3) The
per-request principal (W0).
