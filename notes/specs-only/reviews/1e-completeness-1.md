# Batch 1e (leasing KV): completeness review, round 1

Reviewer: completeness. Read-only; the batch report (`batch-1e.md`) was read only after these
findings were formed, and is cited only to say which ones the author already lists.

Go sources: `.lake/src/client/leasing/{kv,txn,cache,util}.go` (pinned `a4d2bb17`); the proxy
`server/v3@…-a4d2bb1720b9/{etcdmain/grpc_proxy.go, proxy/grpcproxy/*.go}`; `client/v3@…-a4d2bb1720b9/
naming/endpoints/endpoints_impl.go`; the tests `tests/v3@v3.0.0-20261103162249-673da07c8fab/
integration/clientv3/lease/leasing_test.go` (no `tests` module at `a4d2bb17` is in the cache; this
is the newest).

## 1. The users

No user in `examples/` (only comments in `specreq/clientv3kv/history.go`), none in Kubernetes. The
users are the gRPC proxy and the integration tests.

**The gRPC proxy** (`etcdmain/grpc_proxy.go:466-502`). With `--experimental-leasing-prefix` it runs
`client.KV, _, _ = leasing.NewKV(client, prefix)` (`:488`), *after* the optional
`client.KV = ordering.NewKV(...)` (`:469`) and `namespace.NewKV/NewWatcher/NewLease` (`:482-484`).
Everything built from `client` afterwards reads `client.KV`, so it goes through the leasing KV:

| user | call | what it relies on |
|---|---|---|
| `grpcproxy.NewKvProxy` (`kv.go:39`) | `Do(ctx, RangeRequestToOp(r))` (`:62`): a single key, a range (`WithRange`), `WithRev(r.Revision)`, filters, `WithSerializable` | on success `resp.Get()` non-nil (it is put in the proxy's cache, `:73`); the answer is the range's answer, revision-keyed (its cache is keyed by `Revision`) |
| | `Do(ctx, PutRequestToOp(r))` (`:86`), `Do(ctx, DelRequestToOp(r))` (`:94`) | reply or error, forwarded |
| | `Do(ctx, TxnRequestToOp(r))` (`:116`), **nested transactions** included (`requestOpToOp`, `:168-170`) | on success `opResp.Txn()` non-nil, `resp.Succeeded`, and `resp.Responses[i]` of the kind of `r.Success[i]`/`r.Failure[i]` by position: `txnToCache` (`:99-113`) dereferences `reqs[i].GetRequestPut().Key` and `GetRequestDeleteRange()` for each response kind (a nil-pointer panic otherwise) |
| | `Compact` (`:144`) | as the plain client |
| `NewWatchProxy` (`watch.go:61`, `:227`) | `checkPermissionForWatch`: `Do` of a serializable, count-only, limit-1 range of the watched key or range, **only its error used** | nil error = the requester may read the range (the watch is then shared with other watchers) |
| `HandleHealth` (`health.go:51-62`, wired at `grpc_proxy.go:276`, `:566`) | `c.Get(ctx, "a")` | nil error = a member answered |
| `grpcproxy.Register` (`:494`, `register.go:70-76`) and `NewClusterProxy` with a resolver prefix (`cluster.go:65`, `:98`) through `endpoints.Manager` | `client.KV.Txn(ctx).Then(OpPut(k, v, WithLease(id))).Commit()` (`endpoints_impl.go:82`); `client.Get(ctx, pfx, WithPrefix(), WithSerializable())` then `Watch(pfx, WithRev(resp.Header.Revision+1))` (`:96-120`, `:177`) | the prefix Get is the **whole** prefix at its header revision (snapshot, then watch from the next revision) |
| `NewSession` in the leasing KV's own monitor | `concurrency.NewSession(lkv.cl, ...)` (`kv.go:146`), run after the proxy has overwritten `client.KV` | a client whose `KV` field holds the leasing KV |

(The election and lock proxies use `client.ActiveConnection()`, not `client.KV`: not users.)

All of these run in gRPC handler goroutines, concurrently, with the **requester's** auth token: the
proxy's client dials with `AuthUnaryClientInterceptor` (`grpc_proxy.go:345`, `util.go:59-66`), which
sends the token from the incoming context, so each proxied request runs as its requester, not as
the proxy client's principal.

**The integration tests** (`leasing_test.go`), by pattern:

- NewKV with no options (all) or with `concurrency.WithTTL(1)` (`TestLeasingSessionExpire*`,
  `:1677`, `:1749`); several leasing KVs on one prefix over one or several clients
  (`TestLeasingPutGet`, `TestLeasingDeleteNonOwner`); `defer closeLKV()`, sometimes after the client
  is closed (`TestLeasingTxnOwnerGet`, `:540-549`).
- Single-key Get with the cached value checked (`TestLeasingGetSerializable` `:221`,
  `TestLeasingGetWithOpts`, `TestLeasingOverwriteResponse` `:458-471`, `TestLeasingOwnerPutResponse`).
- **Range and revision Gets** checked as full answers: `TestLeasingInterval` (`:104`, 3 keys under
  a prefix), `TestLeasingTxnOwnerGetRange` (`:523-525`), `TestLeasingRevGet` (`:264`, the value at
  an old revision).
- **Sequential writes to one key** with a later read: `TestLeasingPutGet` (`:62-87`, a put by lKV1
  then by lKV2 of the same key), `TestLeasingDo` (`:1548-1584`: a put of `a/abc`, then a delete of
  prefix `a`, then a plain read of the prefix is empty).
- Put/Delete then read (`TestLeasingDeleteOwner`, `TestLeasingDeleteNonOwner`), concurrent puts
  (`TestLeasingConcurrentPut`), errors (`TestLeasingOwnerPutError`, ...), cancellation
  (`TestLeasingTxnCancel`, `TestLeasingSessionExpireCancel`).
- Transactions: CAS (`TestLeasingTxnOwnerIf`, `TestLeasingTxnRandIfThenOrElse`), read-only from the
  cache with values and positions (`TestLeasingTxnOwnerGet`), **atomic read-only transactions**
  (`TestLeasingTxnAtomicCache` `:1405-1415`: every Get of one cached transaction has the same
  `ModRevision`), `Do` of every op kind including the empty `OpTxn(nil, nil, nil)` (`TestLeasingDo`).

## 2. First tier

### F1. A persistent update lets a write be applied after its call returned; sequential writes to one key are not served

`LKV.PutTriple`/`DeleteTriple`/`DoTriple`/`LTxn.CommitTriple` (`Api.lean`) take the caller's update
as `□ AU`, and the post does not take it back. A persistent update may be kept by the
implementation and fired *after the call returned* (from a monitor goroutine, say). The code never
does so (every resend is inside `put`/`delete`/`serverTxn`, `kv.go:246-271`, `:405-432`), but the
spec allows it, and then any reasoning of the form "my later write wins" fails:

- `TestLeasingPutGet` (`:62-87`): `lKV1.Put(abc, def)`, then `lKV2.Put(abc, ghi)`, then a read
  expects `ghi`; a late `def` application is allowed by the spec.
- `TestLeasingDo` (`:1548-1584`): `Do(OpPut("a/abc"))`, then `Do(OpDelete("a", WithPrefix()))`, then
  a plain prefix read expects nothing; a late put application is allowed.
- The proxy's remote clients: two sequential `Put`s of one key through the proxy.

No snippet covers it (`writes.go` has one write per snippet; `ReqPutRevision` passes only because a
late application writes the same value).

Fix: confine the firing window to the call. E.g. take an exclusive token the caller chooses,
`∀ (tok : IProp GF), tok ∗ □ (tok -∗ AU<…><…, COMM tok ∗ LQ Q σ σ' r>)` in the pre and `tok` back
in the post (so the implementation cannot fire after it has returned `tok`), or the equivalent
with a ghost token of `LeasingNames`. Add a snippet: `lkv.Put(k, v1)`, `lkv.Put(k, v2)`, plain Get
of `k` sees `v2` (k owned), and one with a put then a prefix delete as in `TestLeasingDo`.

### F2. `CachedAns` allows a cached answer for ranges and revision reads, which the code never gives

`CachedAns (.range r)` = `CachedRange r …` for any `r` (`Api.lean`, `CachedRange`/`CachedAns`),
including a range end or a revision. The code answers from the cache only when `isBadOp` is false,
i.e. `op.Rev() == 0 && len(op.RangeBytes()) == 0` (`cache.go:189`, checked by `leaseCache.Get`
`:192` before both the cached and the acquiring path of `get`, `kv.go:320-327`, and by `evalOps`
`:276`; `evalCmp` also refuses range compares, `:259`). A range or revision Get is always a
member's answer (`do()`, `kv.go:312-325`). As stated, a caller of a prefix Get can conclude only
"at most one key-value, of the range's first key", so these users are not served:

- `TestLeasingInterval` (3 keys), `TestLeasingTxnOwnerGetRange`, `TestLeasingRevGet` (the old value);
- the proxy's prefix and revision `Range`s (`kv.go:62`; its own cache is keyed by revision);
- `endpoints.Manager.NewWatchChannel`/`List` through the proxy client (`endpoints_impl.go:96`,
  `:177`): a prefix Get, then a watch from `Header.Revision+1`, which needs the whole prefix at that
  revision.

Fix: `CachedAns (.range r) σ res := r.rangeEnd = [] ∧ r.revision = 0 ∧ CachedRange …`, and the
same on every range of a cached transaction's branch. Snippet: a `WithPrefix` Get through the
leasing KV after puts of owned keys under the prefix returns all of them, or a prefix Get then a
watch from its revision as the endpoints manager does.

### F3. A cached answer is given no content, although the code guarantees a past state's answer for every key this KV has not written

`CachedRange` says nothing of the key-value. The header (3.) justifies this by the bugs, but every
listed bug that makes the record one etcd never had needs a write **through this leasing KV**:
`issues/leasing-update-stale.md` (all four cases are own puts/deletes, `cache.go:132-152`). The
others leave a record that was etcd's at the entry's header revision, only stale:
`leasing-evictrange-key` (a failed own range delete keeps old records),
`leasing-stale-entry-after-reset` (the acquisition's response), `leasing-wait-rescind-no-delete`
(the record from before the delete). `leasing-get-failed-acquire-options` answers `OpGet(key)` of
the current state without the options. An entry comes from the acquisition's `Get` at the commit
revision (`kv.go:333-341`), `leaseKey.get` (`cache.go:212-229`) applies the options to it, and
`lc.delete` writes `Kvs = nil` with the delete's header (`:160-165`). So the code gives:

> a cached answer to `r` is W0's serializable answer (`kvStep … (.range {r with serializable :=
> true})`, `Model.lean:827`: the answer at a view `σ.kv.IsView v`) of `r`, or of `OpGet(key)` (the
> failed-acquire path), **unless** `r.key` was written through this leasing KV.

The old proof proved this part (specs-ref `Proof/.../leasing/Results.lean`, "Theorem 1, cached
reads": "etcd's record of the key at the entry's revision"), so dropping it is a backtrack against
a proven result. Users it serves and the current contract does not: `TestLeasingGetSerializable`
(`:221`, the cached `"abc"` while both members are down), `TestLeasingGetWithOpts`,
`TestLeasingOverwriteResponse`, the values in `TestLeasingTxnOwnerGet` (`:590-597`), and every
read-only use (the watch proxy's permission check and `checkHealth` read and never write through
the KV). Under it, the proxy's forwarded reads would be serializable reads, which is what a
remote client can be told. The `Assumes:` of the snippets already has the needed program fact
("k owned"); the "written through this KV" side needs a ghost record, e.g. a persistent
`lkvWrote γL k` that `Put`/`Delete`/`Commit` produce for the keys they write (before their first
attempt), so that `CachedAns` gets the disjunct `lkvWrote γL r.key ∨ <serializable answer>`.
The batch report's decision 1 says this becomes true "with the fixes": the evidence above says it
is already true of the pinned code for keys not written through the KV. Mark what of this you
could not check as uncertain (I did not check `RangeAns`'s `count` against `leaseKey.get`'s
`Count`, which is the unfiltered entry's).

Snippet: `cli.Put(k, "abc")` (plain client, k owned, never written through `lkv`); `lkv.Get(k)`
twice; the second (cached or not) returns `"abc"` or nothing at a revision before the put
(`panic` if the value is anything else).

### F4. The proxy cannot establish `NewKV`'s pre, nor the context premise of its requests

(a) `NewKV.spec` takes `isClient cl γ who`, whose `KV` field is frozen to a `kvAt` value. The proxy
has a writable client at that point and writes `client.KV` right after (`grpc_proxy.go:488`), and
`ReqNewKVProxy` does `cli.KV = kv` under `isClient`. Also, with `--namespace` or
`--experimental-serializable-ordering`, `cl.KV` (read once, `kv.go:60`) is a namespace or ordering
KV, which does not meet `kvAt` over the cluster's keys. And the session monitor's
`concurrency.NewSession(lkv.cl, …)` runs after the overwrite, but 1d's `NewSession.spec`
(`concurrency/NewSession.lean:64`) also takes `isClient c γ who`. Known (author's open question 2,
`req/go_etcd_io_etcd_client_v3.md` "from 1e" item 1), still open in W0 (`Api.lean:927-934`:
`clientMut_KV`/`clientMut_freeze` need `kvAt`). Until W0 answers, `ReqNewKVProxy` is unprovable.
The fix must also reach 1d: `NewSession` should need only the client's non-KV part.

(b) Every leasing triple takes `ctxPrin ctx who`. The proxy's requests carry the requester's token
(`AuthUnaryClientInterceptor`), so with auth enabled the proxy cannot establish `ctxPrin ctx who`
for its one `who`. If the premise were relaxed to "some principal per request", the cache would
have to be stated as shared across principals: a cached entry acquired by requester A is served to
requester B (`leaseCache.Get` checks no permission). Under F3's serializable semantics that is
consistent with W0 (`Model.lean:828-830`: a serializable read may skip the permission check), but
it means the proxy with leasing and auth serves a key to a user without read permission on it, and
`checkPermissionForWatch` (`watch.go:213-228`) passes for a single-key watch the requester may not
read. **Suspected Go bug** (code reading only, not run): an authorization bypass in the gRPC proxy
with `--experimental-leasing-prefix` and auth enabled. Not in `issues/` or `nonissues/` (searched
`leasing-*`, `*proxy*`, `*auth*`). The proxy's own range cache (`kv.go:48-58`) already serves
serializable reads across principals, so the leasing part may be the same known design limit:
record it in `nonissues/` (or `issues/` with a test). The spec side is W0's (2a's) handling of a
per-request principal, and it should be in 1e's `req/` to W0.

### F5. The proxy's nested transactions are excluded (`flatTxn`)

`LKV.DoTriple` requires `flatTxn o`, `LTxn.Then/ElseTriple` `∀ o ∈ os, o.t ≠ tTxn`. The proxy, the
only production user, forwards nested transactions (`kv.go:168-170`, `:230-244`), so it cannot
establish the pre for an arbitrary `Txn` request. The code does not need flatness: the only hazard
is `gatherOps`' `append(thenOps, elseOps...)` (`util.go:80`) writing into spare capacity, and the
proxy builds every level with `make([]clientv3.Op, len(...))` (no spare capacity). Known (author's
decision 3). Restatement: replace `flatTxn` by "every nested transaction's `thenOps` has no spare
capacity" (or `opAt` owning the capacity: a `req/` to W0), and make `ReqDoTxn` nested, built as
`TxnRequestToOp` builds it.

### F6. The proxy's positional use of a transaction's responses has no snippet

`kvProxy.Txn` (`kv.go:115-136`) reads `resp.Succeeded` and, in `txnToCache`, dereferences
`reqs[i].GetRequestPut()` or `GetRequestDeleteRange()` by the kind of `resps[i]`: a nil-pointer
panic if the i-th response is not of the i-th request's kind in the chosen branch. The contract
seems to give it (`txnReplyL`'s `m.ofResps ok rs`; `CachedAns`' `Forall₂` over the branch `ok`
picks), but no snippet checks it: `ReqDoTxn` checks only `resp.Txn() != nil`. Add one that indexes
`resp.Responses` by the branch `Succeeded` names and panics if the kinds differ.

### F7. `NewKV` with session options: the tests' `WithTTL(1)` cannot establish `sessOptsOk`

`sessOptsOk` is a 1d slot with one introduction, `sessOptsOk_nil`. The tests pass
`concurrency.WithTTL(1)` (`leasing_test.go:1677`, `:1749`), and 1d now has the vocabulary for it:
`Concurrency.sessOptsAt sl gs` and `WithTTL.spec` (`concurrency/Api.lean:443`,
`concurrency/WithTTL.lean`). No snippet covers NewKV with options (the brief names this pattern).
Fix: replace the slot by `sessOptsAt osl gs` (plus 1d's `optCtxOk` of the options' context, which
`NewSession.spec` takes, `NewSession.lean:65`), and add a snippet `NewKV(cli, pfx,
concurrency.WithTTL(1))`.

## 3. Second tier

1. **Several leasing KVs on one prefix** (the tests' main scenario; several proxies sharing a
   prefix): no REQ snippet. `protoUpd` is persistent, so it should be provable. Add one: `lkv1.Get(k)`,
   then `lkv2.Put(k, v)` (k owned), then a plain read sees `v`. This exercises `revoke`/`waitRescind`
   across two KVs.
2. **Range delete then plain read** (`TestLeasingOwnerDeletePrefix`, `TestLeasingDo`, the proxy's
   `DeleteRange` with a range end): `writes.go` covers only a single-key delete. The range path
   (`deleteRange`, `revokeRange`, `deleteRangeRPC`, `kv.go:362-403`) is a different proof. Add a
   snippet: a `WithPrefix` delete, then a plain prefix Get is empty.
3. **Uses that read only the error** (`checkPermissionForWatch`, `checkHealth`): no snippet, and
   the contract cannot give their reading ("permitted", "a member answered"): a cached answer is an
   unchanged state with no member contacted. With leasing, `/health` reports healthy from the cache
   while the proxy is partitioned, until the session expires (`health.go:54`, a single key `"a"`,
   acquired on the first check). This is the leasing doc's "disconnected reads", so not a bug of
   leasing, but the health handler's meaning changes. Worth a `nonissues/` note. At least an UNMET
   snippet.
4. **UNMET coverage**: no UNMET snippet for `TestLeasingTxnAtomicCache` (one cached read-only
   transaction's Gets share a revision: evaluated under one `RLock`, `txn.go:72-89`, but with
   per-entry headers), nor for `issues/leasing-update-stale.md` (a value or version etcd never had,
   after an own put). The header cites both.
5. **The proxy never closes**: it holds `lkvOpen γL 1` for good and splits shares across unbounded
   concurrent handlers. That is possible (an invariant holding the remaining share, halving), but
   awkward. A law turning the whole token into a persistent "never closed" share
   (`lkvOpen γL 1 ⊢ |==> □ lkvOpenAll γL`, accepted by `Get`/`Do`) would serve it directly.
6. **The `Assumes:` of the snippets** ("contexts carry the client's principal") is false of the
   proxy (F4b). Say in `ReqDoProxyRange`/`ReqDoTxn` that they model auth-disabled proxying.
7. `ReqDoProxyRange` uses `OpGet(k, WithSerializable())`. The proxy always also passes `WithRev`,
   `WithLimit`, `WithSort`, and the min/max filters (zeros by default, `kv.go:176-202`). Build the op
   as `RangeRequestToOp` does, so that the snippet checks the premises (`toReq = some _`) the proxy
   meets.

## 4. What the weaker contract still gives, per user

- **grpcproxy `kvProxy`**: the shapes it needs (`Get()`/`Put()`/`Del()`/`Txn()` non-nil on success,
  header, positional responses: F6). Nothing about content, which it only forwards. Through it,
  its remote clients get the leasing contract, not W0's (unmet.go). With F2 and F3 they would get
  linearizable or serializable ranges and serializable single-key reads. Blocked on F4 and F5 for
  its real configuration.
- **watch proxy, health**: nothing they read the error for (§3.3).
- **endpoints manager over the proxy client**: its Txn-put is served; its snapshot-then-watch is
  not (F2).
- **tests**: shapes, revisions reached (`ReqGetThenPlainGet`, `ReqTxnReadOnly`), a plain read after
  a single write (`ReqPutRevision`, `ReqDeleteThenPlainGet`). Not sequential writes (F1), ranges
  (F2), or cached values (F3), all of which the code meets. Cross-client freshness, put-once,
  monotone revisions, options on a failed acquire, prevKV on range deletes and the missing-key
  comparisons are genuinely unmet (unmet.go, correct).

## 5. Ranking (need of revision)

1. `Api.lean` (`CachedAns`/`CachedRange`, the `□ AU` of the write triples, `flatTxn`,
   `sessOptsOk`): F1, F2, F3, F5, F7.
2. `NewKV.lean`: F4a (with W0 and 1d), F7.
3. The snippets: `lifecycle.go` (F4a, F7, §3.1), `txn.go` (F5, F6, §3.7), `writes.go` (F1, §3.2),
   `reads.go` (F2, F3), `unmet.go` (§3.3, §3.4).
4. `leasingKV__{Get,Put,Delete,Do}.lean`, `txnLeasing__Commit.lean`: follow `Api.lean`. Their
   "Margin" paragraphs should be updated for F2 and F3.
5. `leasingKV__Close.lean`, `leasingKV__Compact.lean`, `leasingKV__GetStream.lean`: fine for their
   users.

## Verdict

Not complete. The contract serves the proxy's and tests' panic-freedom and revision facts, but
three things are weaker than both the code and its users need. Writes may be applied after their
call returns (F1). Range and revision reads may come from the cache (F2). Cached answers say
nothing, although for keys not written through the KV they are serializable answers (F3), as the
old proof showed. The production user, the proxy, cannot establish the pre: its client is
writable, its requests run as many principals, and it forwards nested transactions (F4, F5). F4a
and F5 are known and recorded. F1, F2, F3, F4b, F6 and F7 are new. A second round is needed. F4b
also carries a suspected authorization bypass (proxy + leasing + auth) for `nonissues/` or
`issues/`.
