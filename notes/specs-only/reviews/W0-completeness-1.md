# W0 (the anchor: the client-observable model and the client's KV API): completeness review, round 1

Reviewer: completeness, independent of the author. Commit under review: `f1ec1df585` (the draft;
first round, so nothing is stale). Read: `SpecPlan/Spec/go_etcd_io/etcd/api/v3/{Model,State,Wire}.lean`,
`SpecPlan/Spec/context/Api.lean`, `SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean` and the KV-path specs
(`kv__*`, `Client__*`, `txn__*`, `ContextError`, `WithRequireLeader`, `kv__GetStream`, ...),
`SpecPlan/Spec/go_uber_org/zap/`, the snippets `examples/specreq/clientv3kv/*.go`, `notes/specs-only/top.md`
and the `req/` sections from W0; the skill's PRINCIPLES and the examples `range.md`, `put.md`,
`compact-client.md` (by their rules). I read `batch-W0.md` only after forming the findings below.

Users scanned (pinned sources under `.lake/src/`, Kubernetes at
`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`): `client/{concurrency,leasing,
experimental/recipes,namespace,ordering,kubernetes,mirror}`, `cache/`, Kubernetes'
`pkg/storage/etcd3/{store,watcher,compact,errors,latency_tracker}.go` and
`storagebackend/factory/etcd3.go`, and `examples/{etcd/*,k8s/*,lib/*}`. **etcdctl is not in the
module cache** (no `go.etcd.io/etcd/etcdctl` anywhere under `/home/ubuntu/go/pkg/mod`): not scanned.
Line numbers below are in those sources.

## Users and patterns

| # | pattern (what the caller relies on) | example call site | snippet | verdict |
|---|---|---|---|---|
| P1 | read-your-write: a get after an acknowledged put sees it, revision not lower | `examples/etcd/compacted/putgetc.go:47-59`, `txnlin/linkvtxn.go:837-884` | `ReqPutThenGet` | covered |
| P2 | a write's header revision is new; `PrevKv` | `concurrency/election.go:81`, `recipes/key.go:73` | `ReqPutRevision` | covered |
| P3 | delete and its `Deleted` count | `txnlin/linkvtxn.go:887-893` | `ReqDeleteThenGet` | covered |
| P4 | list a range: key order, `Count`, `More` vs limit | `client/kubernetes/client.go:58-72` | `ReqListPrefix` | covered |
| P5 | **paginated list**: `More` ⇒ a non-empty page, next page from `lastKey+"\x00"` at the first page's revision | `client/mirror/syncer.go:96-110` (indexes `Kvs[len-1]` when `More`), k8s `watcher.go:347-377`, `store.go:881-918` | none | S3 |
| P6 | compare-and-swap on mod revision, `Else(OpGet)`, `Responses[0]` of the branch taken | `client/kubernetes/client.go:83-131` | `ReqCASModRevision` | covered |
| P7 | create-if-absent with a lease; the else-branch's key (and its `Lease` field) | `concurrency/mutex.go:115-130`, `leasing/kv.go:281-295` | `ReqCreateIfAbsent` | covered, except the `Lease` field (S3) |
| P8 | reads after writes inside one transaction; nested transactions | `leasing/txn.go:191-216` | `ReqTxnReadsOwnWrites`, `ReqTxnNested` | covered |
| P9 | **the nested range responses' `Header.Revision`** of a transaction reply | `concurrency/stm.go:193,201,293,325` | none | **F3** |
| P10 | read-only serializable transaction (stale view) | `concurrency/stm.go:277-293` with `WithSerializable` | `ReqTxnReadonlySerializable` | covered |
| P11 | `Op` built with options, its getters; `Do` dispatch | `leasing/kv.go:102-118`, `ordering/kv.go:63-67` | `ReqOpGetters`, `ReqDo` | covered |
| P12 | serializable get (no lower bound) | `concurrency/stm.go:124-128` | `ReqSerializableGet` | covered |
| P13 | count-only, keys-only, `WithFirstCreate`/`WithFirstKey` | `cache/cache.go:261`, k8s `store.go:711` | `ReqGetOptions` | covered |
| P14 | **revision filters with a sort and limit 1** (the max create/mod revision at most a bound) | `concurrency/key.go:53-62`, `recipes/rwmutex.go:71-82` | none | S3 |
| P15 | a get at a revision the caller saw: the history is the cluster's; `ErrCompacted` below the floor | k8s `watcher.go:368-375`, `cache/cache.go:340` | `ReqGetAtRevision`, `ReqGetErrors` | covered |
| P16 | compaction at a reached revision (`rev ≠ 0`), other compactors | k8s `compact.go:219-251` | `ReqCompactReached` | covered |
| P17 | revisions never go back across linearizable reads | k8s `store.go:830-838` | `ReqRevisionsMonotone` | covered |
| P18 | **streamed list**: first header seen, the final chunk's `Count`/`More`, a mid-stream `ErrCompacted` | k8s `store.go:951-1001`, `watcher.go:391-420` | `ReqGetStream` (partly) | **F1, F2** |
| P19 | errors: `err == rpctypes.ErrCompacted`, `errors.Is(err, ErrFutureRev)`, `errors.As(err, &EtcdError)`, grpc codes (`Unimplemented`, `Unavailable`) | k8s `errors.go:68`, `store.go:923`; `leasing/kv.go:300-305` | `ReqPutErrors`, `ReqGetErrors`, `ReqCtxErrors` | covered for etcd errors; grpc codes S8 |
| P20 | **auth on: refusals by principal, reads holding only permitted keys, a principal carried by the context** | `examples/etcd/auth/authkv.go:152-264` | none | **F4, F5** |
| P21 | contexts passed: `WithTimeout(Background())`, `TODO()`, `client.Ctx()`, `WithRequireLeader`, k8s request contexts (`WithValue` chains), `wait.ContextForChannel`, `metadata.AppendToOutgoingContext` | `recipes/key.go:66`, `concurrency/mutex.go:89`, k8s `compact.go:193`, `authkv.go:155` | `ReqCtxErrors` | S4 (and F4) |
| P22 | a `KV`/`Txn` wrapper standing for the client's (`cli.KV = NewETCDLatencyTracker(cli.KV)`) | k8s `latency_tracker.go:31-108`, `factory/etcd3.go:468` | none | **F7** |
| P23 | the receiver writes into the reply (`Kvs[i] = nil`, `pr.Header = resp.Header`) and keeps it | k8s `watcher.go:362`, `leasing/kv.go:262-263`, `cache/cache.go:343` | none | covered by the unfold laws at `own 1` and `replyPersist`; no snippet (S3) |
| P24 | zap logging | throughout the server | n/a | S5 |

Model against what users observe: watch histories (the whole `KVHist`, events per revision,
`compacted`) are enough for the cache's and Kubernetes' get-then-watch; members and alarms are
enough for every user found; **leases** (F6) and **auth errors** (F4, F5, F6) are not.

## First tier

### F1. A streamed range can end with `ErrCompacted` that no `Step` of its request gives (unsound; Kubernetes handles it)

`Api.lean`, `streamAt_recv.spec` and `wireStreamAt_recv.spec`: a terminal error chunk is either
`Q σ σ' (.err e)` with `closeErr = errVal e` (so `Step who (.range r) σ σ' (.err e)`) or
`indefCall`. The server pins an unpinned stream to its first chunk's revision
(`server/etcdserver/v3_server.go:236-240`: `if r.Revision == 0 { r.Revision = headerRev }`) and
reads each later chunk at it (`:223`); a compaction between chunks makes that read fail with
mvcc's `ErrCompacted`, which `togRPCError` and the client's `ContextError` turn into
`errVal .compacted`, a definite error. But for the request the spec names
(`(opGetM key gs).rangeReq`, revision `0`), `RangeReq.revErr` is `none` (`Model.lean:597-600`:
`0 < r.revision` fails), and `.compacted` is not a refusal: no `Step` answers it, so the post
cannot hold. Kubernetes relies on this case: `watcher.go:410-415` ("a compaction mid-stream can't
be resumed ... surface it as ResourceExpired"; its stream is unpinned, `:387-391`) and
`store.go:978-980` (`listReadError`, whose `ErrCompacted` branch is the paging one).

Fix: make the stream's request what the server reads after its first chunk: the terminal error
after `ms ≠ []` is a `Step` of `{ r with revision := rev₀ }` where `rev₀` is the revision the first
chunk was read at (a ghost value `streamAt` fixes at the first chunk), or give the stream its own
`Req` case (`.rangeStream r`) whose step admits `.err .compacted` once the pinned revision is below
the floor. Add a snippet: an unpinned `GetStream` whose loop treats `ErrCompacted` as "relist" and
panics on any other definite error.

### F2. The stream's chunk shape is too weak for Kubernetes (author's open question 3 says it is enough)

`streamMatches` (`Api.lean`, "A streamed range's chunks") says only: the last chunk has the
header's revision and, at the default ordering with no filter, the chunks' key-values and the last
`More` are the answer's. Kubernetes reads more:

* `store.go:986-989` and `watcher.go:416-418` take the **first chunk whose `Header` is non-nil** as
  the list's revision, not the last chunk's. The server sets a header only on the final chunk
  (`v3_server.go:249-252`, `client/kv.go:81-84`: "Header, More, and Count are populated only on the
  final chunk"), so the first non-nil header is the last chunk's; the spec does not say the
  earlier chunks' headers are `nil`, so the revision Kubernetes records (and validates against
  `withRev`, `store.go:830-838`) is unconstrained.
* `store.go:843` and `:993` keep each chunk's `Count` as "etcd's count of keys remaining in the
  range, including this batch" (`:877`) and pass the last one to `PrepareContinueToken`
  (`remainingItemCount`, `:865`). The server's final `Count` is the whole range's count
  (`v3_server.go:252-258`: the keys streamed plus `txn.Count` of the rest), i.e. the answer's
  `count`; the margin "its counts are the pages' sums: neither is modelled" is wrong about the
  code and leaves Kubernetes' count unproved.
* `store.go:840-842`: a chunk with no key-values and `hasMore` is an error; the server never sends
  one, but nothing says so (an error return, not a panic: no proof is blocked).

Restatement: `streamMatches r ms rev a` adds, for every chunk but the last, `hdr = none ∧ more =
false ∧ count = 0`, and for the last, `count = W64 a.count` at the default ordering with no filter
(the server's code gives both). The snippet `ReqGetStream` should take the revision from the
first non-nil header, as Kubernetes does, and check `Count` on the final chunk.

### F3. A transaction reply's nested range responses have unconstrained headers; the STM dereferences them

`Wire.lean`: `ResponseOpM.ofResp`'s `range` case requires only `m.ofAns a`; `RangeRespM.hdr` is an
`Option` and the model's `OpResp.range` carries no revision ("The nested responses' headers are
not modelled", `Model.lean:467`). `concurrency/stm.go` stores the nested range responses of its
read transactions as `*GetResponse`s (`:193`, `:293`) and reads `resp.Header.Revision` of them
(`readSet.first`, `:201`; `stmSerializable.Get`, `:325`, which pins every later read at it with
`WithRev`). With a `nil` header that is a nil dereference, so the STM's proof (1d) cannot show it
panic-free, and its snapshot isolation needs the value: the revision the read was answered at. The
server gives both: every nested range response has a header (`server/etcdserver/txn/range.go:157`)
whose revision is the transaction's read view's revision so far (`range.go:162`, `rr.Rev`, which
mvcc's write transaction sets to `beginRev`, plus one after its own first write).

Restatement: `OpResp.range (rev : Nat) (a : RangeAns)` with `TxnRun`'s `range` case giving
`rev := if st.2 = [] then h.rev else R`, and `ResponseOpM.ofResp.range` requiring
`m.hdr.map (·.revision) = some (W64 rev)`. Snippet: a read-only transaction of two gets whose
nested `Header.Revision`s equal the outer one (the STM's `fetch`).

### F4. The principal of a request comes from the context's metadata as well as the client; the KV specs take any `ctxOk`

Every `KV.*Triple` states the step as `Step who ...` with `who` fixed by the client handle, for any
`Context.ctxOk ctx`. The server reads the principal from the request's incoming metadata
(`server/auth/store.go:1077-1096`: `md["token"]`, else `md["authorization"]`, `ts[0]`). A client
built without credentials (`who = none`) attaches no token of its own, so a context carrying
`"token"` outgoing metadata (`metadata.AppendToOutgoingContext`, a `WithValue` chain, which
`ctxOk` admits) decides the principal: with a live token of user `u`, a put that `Step none`
refuses (`permErr none = .userEmpty`) succeeds and changes the state. The KV specs are false at
such a context, and req item 4 to 1c ("`who` is what the server's auth applier sees for every
request") cannot be met. The pattern is used: `examples/etcd/auth/authkv.go:152-158` (`reqCtx`:
the "bad" principal's contexts carry a token no provider issued) for every KV call of `Work`; the
old specs modelled it (`specs-ref`: `metadata.outgoingOf`, `auth.ctxTokenOf`,
`notes/auth-plan.md`, E2c). No snippet covers auth at all (refusals by principal, reads holding
only permitted keys: `authkv.go:163-234`).

Restatement (one of): (a) a premise of the KV contract that the context carries no `token`/
`authorization` outgoing metadata when `who = none` (a persistent `ctxNoToken ctx` with intro laws
for `Background`, `TODO`, Perennial's contexts, `WithRequireLeader`), plus an intro for a context
whose token was issued to no one (then its principal behaves as `none`: the server answers
`ErrInvalidAuthToken`, a refusal), which is what `authkv` needs; or (b) the step's principal a
function of the client and the context (`ctxPrincipal who ctx p`, a slot of 2a/1c). Add an auth
snippet: a client of principal `u` whose range outside its permission returns an error and whose
permitted range returns only permitted keys.

### F5. `ErrAuthFailed` is returned for a request that was never applied; it is neither a refusal nor indefinite (unsound)

On `ErrInvalidAuthToken`/`ErrAuthOldRevision` (and `ErrUserEmpty` with a token bundle) the retry
interceptor refreshes the token and **returns the refresh's error** if it fails
(`client/retry_interceptor.go:86-95`, `return gtErr`); `getToken` returns `Authenticate`'s error
unchanged except `ErrAuthNotEnabled` (`client/client.go:297-304`), so a password changed or a user
deleted by an administrator makes a KV call return `errVal .authFailed` with nothing applied.
`EtcdErr.refusal` (`Model.lean:316-320`) does not contain `.authFailed`, and it is definite, so the
client's contract claims `Step who rq σ σ' (.err .authFailed)`, which no step gives. Fix: add
`.authFailed` to `EtcdErr.refusal` (it is a refusal: the request will never take effect), and say
so in 1c's req (item 2's "if it gives up, it fires the caller's update with that refusal").

### F6. The lease part of the model does not serve the lease examples, and misses its auth errors

Judged against `examples/etcd/{lease,leasegrant,leaseexpiry,leasecatchup}` (the model is W0's; the
specs are 1c's):

* `leaseStep .leaseLeases` (`Model.lean:894-895`): any list of granted ids. `lease/leasekv.go:68-73`
  panics if `Leases` lists an id twice: needs `ids.Nodup` (true: `lessor.Leases()` walks a map).
* `leasegrant.go:73-81` (a grant, then `Leases` must list it), `leaseexpiry.go:96-101` (after
  `TimeToLive` says gone, `Leases` must not list it) and `leasecatchup.go:165-170` (a member that
  lists the last filler lists the earlier lease) need `Leases` to answer **the live leases of a
  state the cluster has been in** (`∃ σv, Reach σv σ ∧ ids ≈ live(σv)`), plus a lower bound for a
  client that talks to one member (`leasegrant` is single-member: its member answered the grant
  after applying it). The model has neither the view nor any per-member monotonicity
  (`KVHist.IsView` has none either: a serializable read on the one member a client uses is not
  read-your-writes in the model). Options: views attached to the member answering, with a
  monotone per-member lower bound the client can carry; or a single-member mode in `EnvCfg`.
  This is a design decision for the user.
* `leasegrant.go:1-6` proves its `Main` "under the deployment premise that no lease granted in the
  run expires before the run ends". With time unmodelled, `envUpd` may fire `leaseExpire` at any
  time and `EnvCfg` has only `autoCompact`: the premise is not statable. Restatement: an
  `EnvCfg.leaseExpiry : Bool` (as `autoCompact`), false for a run whose leases outlive it.
* Auth: `LeaseLeases` checks range permission on every attached key and answers
  `ErrPermissionDenied` (`server/etcdserver/v3_server.go:751-783`), and `LeaseTimeToLive` with
  keys does too (`:705-711`, `checkLeaseTimeToLive`); neither error is a refusal nor in
  `leaseStep`'s cases, so the model is false of etcd with auth on. Add the permission branch
  (`¬ σ.permits who [(read, k) for attached k] [] ∧ res = .err (permErr who)` or the admin check).

### F7. The `Txn` bundle forces `If`/`Then`/`Else` to return their receiver; Kubernetes' wrapper returns the inner `Txn`

`Txn.IfTriple`/`ThenTriple`/`ElseTriple` (`Api.lean`) post `⌜r = iv⌝ ∗ txnAt iv ...`. The
vocabulary is meant to admit a wrapped `KV` (header of `Api.lean`: "a wrapper (... Kubernetes'
latency tracker) proves it for itself"; req to 1c, item 1: `cli.KV =
etcd3.NewETCDLatencyTracker(cli.KV)`, `factory/etcd3.go:468`). The tracker's `Txn` returns
`&clientV3TxnTracker{ctx, Txn: c.KV.Txn(ctx)}` (`latency_tracker.go:91-93`), which overrides only
`Commit` (`:100-108`): `If`, `Then` and `Else` are promoted from the embedded inner `Txn` and return
the **inner** value, so `kvAt` of the tracker cannot be proved. (The example `examples/k8s/etcd3`
builds its store without the factory, so only real Kubernetes hits this.) Restatement: post
`(r : GoInterface), RET #r; txnAt r γ who ctx st'` (no `r = iv`); the concrete `txn.If.spec` may
keep `r = iv` as its instance. Every user found chains the result (`recipes/key.go:108-109`
included), so nothing relies on the identity.

## Second tier

* **S1. `kvAt` cannot be realized by leasing's KV** (the header's claim). A cached `Get` returns
  the cached response's header (`leasing/cache.go:212-227`, `copyGetResponseMetadataOnly` over
  `lk.response`, `util.go:101-126`; served at `kv.go:320`), whose revision is the one leasing last
  saw for that key, not the cluster's current revision, while `KV.GetTriple`'s linearizable answer
  is `.range σ.kv.rev a`; and `issues/leasing-update-stale.md` (blocks-proof: yes) already makes
  its values diverge. 1e needs its own contract (as the old `getOutcome`); drop leasing from the
  header's list. The stale header is also observable (`ReqRevisionsMonotone` would panic through
  a leasing KV after a put elsewhere): worth a `nonissues/` entry (documentation level) by the
  author; I did not write one (read-only).
* **S2. `GetStream`'s goroutine leaks when the consumer stops reading** (a Go bug, code reading):
  the producer sends with `respCh <- ...` and no `select` on `ctx.Done()` (`client/kv.go:175-188`,
  channel capacity 1), so once its consumer stops, the second pending chunk (or the terminal error
  after the context is cancelled) blocks it forever. Kubernetes stops mid-stream on an item error
  (`store.go:845-848` returns, so the iterator's `yield` is false, `:993-995`). The spec is safe
  (the `threadTok` stays inside the abandoned `streamAt`), but Kubernetes then loses one thread token
  per abandoned list, so a bounded-threads proof of the store does not close. Record it
  (`nonissues/` or an `issues/` test with a two-chunk stream abandoned after one); the spec's
  margin should say the token comes back only on a drained stream.
* **S3. Uncovered patterns (snippets missing)**: P5 (paging: `More` ⇒ non-empty `Kvs`, the next page
  from `lastKey+"\x00"` at the pinned revision, `mirror/syncer.go:96-110` would panic otherwise),
  P14 (revision filters with a sort and limit 1, `concurrency/key.go:53-62`), P7's `Lease` field
  (`leasing/kv.go:293-295`), P23 (the caller writes into and keeps the reply), and a two-client
  pattern (a put through one client, then a get through another sees it: Kubernetes' several API
  servers, `txnlin`'s concurrent goroutines). Each is provable from the model as it stands; they
  are missing requirements, not missing facts.
* **S4. Context introductions**: `SpecPlan/Spec/context/Api.lean` owns the context bundle but gives no spec
  for `context.WithValue` (Kubernetes' request contexts; Perennial has none) nor intro for
  `wait.ContextForChannel` (k8s `compact.go:193,256`; no batch in `batches.md` owns the Kubernetes
  store, whose old specs exist: `specs-ref/Spec/k8s_io/apiserver/pkg/storage/etcd3/`);
  `metadata.AppendToOutgoingContext` is in the grpc req (item 7) only as `NewOutgoingContext`;
  `Client.Ctx()` (`concurrency/mutex.go:89`, `stm.go:90`) is not in the req to 1c. The header
  lists a law `ctxOk_todo` that does not exist (it is `TODO.spec`).
* **S5. zap coverage** (W0 owns the logger for every batch): no spec for `Logger.Named`
  (`etcdserver/bootstrap.go:590`, `storage/backend/backend.go:1136`, `client/client.go:401`),
  `Logger.Sugar` and the `SugaredLogger` methods (`etcdserver/zap_raft.go:35-49`,
  `api/v3rpc/watch.go:407`, `backend.go:1137`), `Logger.WithOptions`/`zap.AddCallerSkip`
  (`backend.go:1137`), `zap.Time` (`etcdserver/server.go:917`, `api/v3rpc/interceptor.go:188`,
  `pkg/traceutil/trace.go:241`), `zap.Float64` (`server.go:1623`, `client/client.go:497`),
  `zap.Binary` (`storage/mvcc/kvstore_txn.go:135`); the header says `Named`/`With`/`WithOptions`
  keep `isLogger`, which only such specs can give. Uncertain: `Logger.Info` and its siblings take
  no ownership of what their fields reference, yet `Stringer`/`Error`/`Any` fields call the user's
  `String`/`Error` during the call; true of every use I saw (enum `String`s, error values), but the
  trust-boundary statement claims it for all.
* **S6. The transaction's validation disjunct is always admissible** (`Model.lean:838-839`): any
  transaction may answer `tooManyOps`, `duplicateKey`, `emptyKey`, ... with no condition, so a
  caller cannot conclude that a well-formed transaction was not refused for validation. No user
  found tests these errors (they propagate them), so nothing is blocked; condition each on the
  model's check, or make them refusals.
* **S7. `namespace`'s KV** (`client/namespace/kv.go`) cannot meet `kvAt` at all (it rewrites keys;
  no projected cluster exists in the vocabulary, and a projected history would need revisions with
  no visible event, which `KVHist.commit` drops). It is in no batch; note only.
* **S8. grpc status codes**: Kubernetes falls back to paged lists on `codes.Unimplemented`
  (`store.go:956-959`), leasing retries on `codes.Unavailable` (`leasing/kv.go:303`); `callErr
  .other` says nothing of the code. Both are safe either way; a stronger result would need the
  code in `CallErr`.

## Sampled call sites: pre establishable, post sufficient

* P6, `client/kubernetes/client.go:83-104` (`OptimisticPut`): `Compare(ModRevision(key), "=",
  expectedRevision)` (`CmpArg.i64`), `OpPut(..., WithLease(opts.LeaseID))` (not `putPanics`),
  `Else(OpGet(key))`; `Commit` takes the exclusive update; the post gives `Succeeded`,
  `Header.Revision` and, on failure, one `.range` response whose `Kvs` has at most one element
  (`kvFromTxnResponse`): sufficient. Its context is Kubernetes' request context: pre establishable
  only once S4's `WithValue` exists.
* P16, k8s `compact.go:219-251`: `rev ≠ 0` is checked at `:243`; `rev` is an earlier header
  revision, so `etcdLb` from the earlier update and `Reach` give no `ErrFutureRev`; the
  `Kvs[0].Version` at `:234` needs the key to exist when the compare fails, a workload fact of the
  compactor's invariant (no one deletes `compact_rev_key`; it has no lease, so lease expiry cannot):
  sufficient. Context `wait.ContextForChannel`: S4.
* P7, `concurrency/mutex.go:115-130`: on failure `Responses[0].GetResponseRange().Kvs[0]` exists
  because the compare `CreateRevision(myKey) = 0` failed at `s0` and the else-branch's get reads
  `s0` (`TxnRun`): sufficient. `Unlock(client.Ctx())`: S4.
* P9, `concurrency/stm.go:277-293`: pre fine; post insufficient (F3).
* P18, k8s `store.go:951-1001`: pre needs a `threadTok` per list (S2) and the context (S4); post
  insufficient (F1, F2).
* P20, `authkv.go:196-264`: pre not establishable soundly for the "bad" principal (F4).
* P22, `factory/etcd3.go:468`: `kvAt` of the tracker not provable (F7).

## Per target

**`api/v3/Model.lean`.** Good: one state for everything a client sees, the whole history kept (a
stale view and a past read need no second notion), etcd's range quirks in `RangeReq.answers`, the
transaction's run with reads after writes and nested branches decided at `s0`, refusals as
linearized no-ops, the environment's steps separate. Findings: F5 (`refusal` misses
`authFailed`), F6 (leases: `Nodup`, views, the expiry premise, auth errors), F3 (nested range
revision in `OpResp`), F1 (a stream's pinned revision), S6.

**`api/v3/State.lean`.** Good: `etcdState`/`etcdLb` with `etcdLb_reach`/`etcdLb_ord` serve every
"revision reached"/"history prefix" pattern (P15-P17); `errVal` with `errVal_inj`/`errVal_ty`
serves `==`, `errors.Is` and `errors.As` tests (P19). `envUpd`'s `EnvCfg` needs the lease-expiry
knob (F6). No other finding.

**`api/v3/Wire.lean`.** Good: field-by-field unfold laws let users write into replies (P23) and
persist them (`replyPersist`). Finding: F3 (nested range headers).

**`context/Api.lean`.** Good: one persistent bundle for any context, with `Err`'s two specs.
Findings: F4 (the token in a context's metadata), S4 (missing introductions).

**`client/v3/Api.lean` and the KV specs.** Good: one contract per method (`KV.*Triple`) shared by
`*kv`, the promoted `Client` methods and wrappers; persistent updates for reads, exclusive for
writes; a definite error is a linearized answer, which every error test found (P19) can use; the
premises (`putPanics`, `deletePanics`, `prefixAndFromKey`, `rev ≠ 0`, the `Txn` call order) are
each met by every caller found. Findings: F1, F2 (streams), F4 (principal), F7 (`Txn` bundle), S1
(leasing claim), S2 (stream leak), S8.

**Snippets `examples/specreq/clientv3kv/`.** Good: 18 snippets cover the common patterns P1-P4,
P6-P8, P10-P13, P15-P17, P19 with explicit panics. Missing: F3's nested header, F1/F2's stream
reliances, F4's auth patterns, S3's list.

**`go_uber_org/zap/`.** Good: the level methods, `Check`/`Write`, `Panic`/`Fatal` and the common
field constructors. Findings: S5.

**`notes/specs-only/top.md`.** The Kubernetes paragraph says the stream snippets cover its
patterns (F2 says not); the client's `KV` wrapper claim (F7, S1).

## Ranking by need of revision

1. `client/v3/Api.lean` (F1, F2, F4, F7; S1, S2)
2. `api/v3/Model.lean` (F5, F6, F3, F1; S6)
3. `context/Api.lean` (F4; S4)
4. `examples/specreq/clientv3kv/` (snippets for F1-F4, S3)
5. `api/v3/Wire.lean` (F3)
6. `go_uber_org/zap/` (S5)
7. `notes/specs-only/top.md` (claims to correct)
8. `api/v3/State.lean` (the `EnvCfg` knob only)

## Verdict

Not done: seven first-tier findings. Two make specs false of etcd (F1: a mid-stream `ErrCompacted`;
F5: `ErrAuthFailed` from a failed token refresh), one makes the KV contract false for contexts
carrying a token (F4), one model gap makes the lease examples unprovable (F6), and three leave a
real user unserved (F2 Kubernetes' streamed lists, F3 the STM, F7 Kubernetes' latency tracker). The
common KV patterns are well covered and the vocabulary's shape (one client-owned state, the
contract once, definite errors as linearized answers) serves every user found. Each fix is local:
a field or a conjunct (`streamMatches`, `OpResp.range`, `EtcdErr.refusal`, `leaseStep`, `EnvCfg`),
a weaker `Txn` post, and a context premise or principal slot.
