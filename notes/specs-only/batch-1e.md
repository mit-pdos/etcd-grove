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
