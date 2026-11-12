# W0 (the anchor), round 2: provability and completeness

Reviewer: round 2, both kinds. Commit under review: `143abd4caa` ("specs-only W0 round-1 repairs"),
against round 1's `reviews/W0-provability-1.md` (P-) and `reviews/W0-completeness-1.md` (C-).
Read: the diff of `143abd4caa` on `SpecPlan/Spec/go_etcd_io/etcd/api/v3/{Model,State,Wire}.lean`,
`SpecPlan/Spec/context/Api.lean`, `SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean` (and `kv__GetStream.lean`,
`txn__If.lean`), the snippets `examples/specreq/clientv3kv/`, `notes/specs-only/top.md` (K1-K8),
the `req/` items naming `ctxPrin`, and the two new nonissues. Go: the fork under `.lake/src/`
(`a4d2bb17`), Go 1.27.3's `context` (`~/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.27.3.linux-amd64/src/context/context.go`),
grpc v1.84.0, Kubernetes' apiserver `v0.0.0-20261021221356-9c4ec15b8038`, Perennial's
`Perennial/Proof/context/`. File references are to `.lake/src/` unless they start with `Spec/`,
`notes/` or a module path. Read-only; nothing built (the author reports the batch builds).

## Round-1 first-tier findings: status at `143abd4caa`

| round 1 | status | evidence |
|---|---|---|
| P-F1 / C-F5 `ErrAuthFailed` | **fixed for unary calls**, **not for streams** (F2 below) | `Model.lean` `EtcdErr.refusal` has `.authFailed`; unary `gtErr` (`client/retry_interceptor.go:91-99`) is now a refusal the interceptor fires (the caller's AU suffices: it opens `etcdState` itself, σ' = σ) |
| P-F2 / C-F1 mid-stream `ErrCompacted` | **partly fixed**: the `ms ≠ []` guard is false (F1 below) | `Api.lean` `streamAt_recv`, `wireStreamAt_recv` |
| P-F3.1 empty permission checks | fixed | `State.permits` puts `∃ u` per pair; `apply/auth.go:198-205` (`checkLeasePuts`: no lease or no key, nothing checked) |
| P-F3.2 serializable read-only txn auth | fixed | `kvStep .txn`, both refusal and success `∨ (t.readonly ∧ t.serializable)` |
| P-F3.3 negative revisions in a txn | fixed, verified | `RangeReq.txnRevErr`; `checkTxn` runs on `kv.Read`'s view (`txn/txn.go:44,54`), whose `firstRev` is `compactMainRev` (`mvcc/kvstore_txn.go:61`), `-1` before a compaction; `checkRange` (`txn/range.go:172-182`) |
| P-F3.4 empty `RequestOp` | fixed | `.keyNotFound` among the txn's gRPC refusals |
| P-F3.5 `AuthEnable` keeps the revision | fixed, verified | `auth/store.go:299` (`setRevision(tx.UnsafeReadAuthRevision())`) |
| P-F3.6 orders | fixed | `l.Perm` in `userGet`, `roleGet`, the member answers, `alarmList` |
| P-F3.7 self `UserGet`, own-role `RoleGet`, root's perms, validations, password-less | fixed, one corner left (S1) | `AuthState.mayCall`; `apply/auth.go:222-242` |
| P-F3.8 TTL above granted; permission errors on lease reads | fixed | `leaseStep .leaseTimeToLive`, `.leaseLeases` |
| P-F3.9 member errors; admin checked at a stale local state | fixed | `clusterStep` |
| P-F4 `ReqListPrefix` count | fixed | `etcdState_sizeFits` (`State.lean`) |
| P-F5 `WithCancel` over `ctxOk` | fixed for the snippet; the new context laws have two false statements (F3, F4) | `SpecPlan/Spec/context/Api.lean` |
| C-F2 stream chunk shape | fixed, verified | `streamMatches` against `EtcdServer.rangeStream` (`server/etcdserver/v3_server.go:197-283`): non-final chunks have no header, `More`/`Count` zero and key-values (not done ⇒ `resp.More` ⇒ a non-empty page, `asembleRangeResponse`, `txn/range.go:147-160`); final `Count` = streamed + `txn.Count` of the rest = the range's count at the pinned revision |
| C-F3 nested range headers | fixed, verified | `TxnRun.range` revision `if st.2 = [] then h.rev else R` = `storeTxnWrite.Range`'s `beginRev` (+1 once `changes` non-empty: an empty delete adds none, `kvstore_txn.go:189-201`); read-only txns' `NewReadOnlyTxnWrite` reads at `currentRev`; `rangeKeys` returns `Rev: curRev` on every path (`kvstore_txn.go:84-150`); `Wire.lean` `ResponseOpM.ofResp.range` requires the header |
| C-F4 principal from the context's metadata | **sound**, but one introduction law is false (F5) and Kubernetes cannot establish the premise (F6) | below |
| C-F6 leases | partly (Nodup, permission errors, the `leaseExpiry` knob); the views are the user's open question 6; the knob's realizability is S3 | |
| C-F7 `Txn` builders on wrappers | fixed | `Txn.{If,Then,Else}Triple` post `txnAt r ...`; `txn.If.spec` instantiates the bundle; the tracker's promoted `If` (Kubernetes `latency_tracker.go:91-93`) returns the inner `Txn`, which meets it |

**`ctxPrin` against the token path.** Sound. The server takes `md["token"]`, else
`md["authorization"]` (Bearer-trimmed), `ts[0]` (`auth/store.go:1072-1100`); with auth off it
reads nothing. The client's own token is a per-RPC credential (`credentials/credentials.go:69-77`,
nothing sent while the token is empty: auth was off at the last `getToken`, `client.go:298-301`),
and grpc puts the credentials' headers before the context's outgoing metadata
(`grpc@v1.84.0/internal/transport/http2_client.go:628-643`). `ctxPrin ctx who` excludes a token of
any other user, so the server sees `who`, or no token (auth on: `ErrUserEmpty`, a refusal the
interceptor may refresh past), or an invalid one (`ErrInvalidAuthToken`, a refusal; with no
credentials the interceptor does not refresh). `WithRequireLeader`/`withVersion` add
`hasleader`/`client-api-version` only (`client/ctx.go:29-50`). Concurrency's contexts are
establishable (`Client.Ctx()` from 1c over `TODO()`/the config's context and `WithCancel`;
`WithCancel(Background())` in recipes and `waitDelete`; caller contexts passed through as
premises). Kubernetes' are not (F6).

## First tier

### F1. `streamAt_recv`/`wireStreamAt_recv`: `ErrCompacted` can end an unpinned stream before any chunk; the `ms ≠ []` guard makes the slot false

`EtcdServer.rangeStream` (`server/etcdserver/v3_server.go:216-266`): on the first page it pins
`r.Revision = headerRev` (`:236-240`); if that page is already the last because the caller's limit
is reached (`done := !resp.More || count == totalLimit`, `:249`) with `resp.More`, it reads the
remaining count **at the pinned revision** before sending anything (`txn.Count(..., r.Revision)`,
`:253-258`, `return cerr`). A compaction applied between the page's read and that count (each
`txn.Range` opens its own read view, `txn/range.go:53`; the apply loop runs concurrently) makes the
count fail with `ErrCompacted` (`mvcc/kvstore_txn.go:81-83`), and the stream ends with that error
and **no chunk**. For the client's request (revision `0`) `RangeReq.revErr` gives no `.compacted`,
`.compacted` is no refusal and not indefinite, and the new disjunct requires `ms ≠ []`: no
disjunct of `streamAt_recv.spec` (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean`, the terminal error
case) holds. Kubernetes reaches it: `streamChunks` streams unpinned (`withRev == 0`) **with**
`WithLimit(limit)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:944-951`).
Fix: drop `ms ≠ []` from both slots (`⌜v.closeErr' = errVal .compacted⌝` with no `Q`, and
`callErr err (.etcd .compacted)` in `wireStreamAt_recv`); reword the docstring ("the revision the
server pinned at the first page was compacted before a later read"), the header of
`kv__GetStream.lean` (its sketch should also name this no-`Q` case) and the snippet's comment.

### F2. A definite error at stream open: `getToken`'s `ErrAuthFailed` is not `indefCall`

`streamClientInterceptor` calls `c.getToken(ctx)` on **every** stream open and returns its error
as the open's (`client/retry_interceptor.go:123-127`); with a username and password that is
`Authenticate`'s error (`client.go:285-306`): `ErrAuthFailed` after a password change or a user
deletion, `ErrTooManyRequests`, ..., i.e. definite. `kv.GetStream` returns it through
`ContextError` (`kv.go:171-173`). `RemoteKV.RangeStreamTriple` and `KV.GetStreamTriple` post
`indefCall err` for every open error, and `indefCall_pure` makes that false of `errVal .authFailed`.
This is the stream half of round 1's P-F1 ("the same for every ... call"), not repaired: every
auth-mode client's `GetStream` (Kubernetes with etcd credentials) and 1b's watch streams (the same
interceptor; 1b's slots should be checked the same way).
Fix: the open-error disjunct `⌜sc = nil⌝ ∗ (indefCall err ∨ ⌜∃ e, e.refusal = true ∧ err = errVal e⌝)`
(nothing fired: a refusal settles nothing), or let the client fire the persistent update with the
refusal and give `Q` (it can: the AU opens `etcdState` itself). Say it in 1c's req item 2 for the
stream interceptor.

### F3. `Context.ctxChild_done` is false: a child is cancelled after its parent is done

`ctxChild ctx ctx' ⊢ □ (ctxDone ctx -∗ ctxDone ctx')`, with `ctxDone` meaning "`Err()` is not nil"
(the header) and `ErrDone.spec` giving a non-nil `Err()` from `ctxDone`. Go 1.27's
`cancelCtx.cancel` stores the error, closes `done`, and only then cancels the children
(`context.go:562-572`), and `Err()` is an atomic load (`:464-471`): between the two, the parent's
`Err()` is non-nil (so `Err.spec` gives `ctxDone parent`) while the child's is `nil`, contradicting
`ErrDone.spec` on the child through the law. For a parent of another type the child is cancelled
by `AfterFunc` or a goroutine (`propagateCancel`, `:508-535`), later still. No spec uses the law yet
(grep); it is a false obligation a client could use. Fix: drop it (Perennial's own spec states the
converse: a child's `PDone` is `parent.PDone ∨ cancelled`, `Perennial/Proof/context/WithCancel.lean:52-60`).

### F4. `Context.WithValue.spec` is false for a nil or non-comparable key

`WithValue` panics on `key == nil` and on a key whose type is not comparable (`context.go:732-737`);
the spec quantifies over every `key` with no premise (the docstring's "(a comparable key)" is not in
the statement). Fix: `⌜key ≠ GoInterface.nil⌝` and the key type's comparability as pure premises.

### F5. `ctxPrin_of_isContext` is false: Perennial's `isContext` says nothing of a context's values

`isContext c s` constrains `c`'s methods only; its `Value` clause covers `&cancelCtxKey` alone and
"the `Values` field of `ContextDesc` is unused" (`Perennial/Proof/context/Base.lean:610-611`). A
`*cancelCtx` made over `metadata.AppendToOutgoingContext(Background(), "token", t)` meets every
clause of `isContext` (its `Done`, `Err`, `Value(&cancelCtxKey)` and `parentCancelCtx` are its
own), yet carries another user's token, so the law `isContext c s ⊢ ctxPrin c who` has no
realization. Unused (grep). Fix: drop it; `ctxPrin_background`, `ctxPrin_todo` and
`ctxPrin_child` (with W0's `WithCancel`/`WithTimeout` specs) cover the contexts the law was for.
(`ctxOk_of_isContext` is fine: `ctxOk` is about the methods.)

### F6. Kubernetes cannot establish `ctxPrin` for its request contexts

Every `KV.*Triple` (and `Txn(ctx)`) now takes `ctxPrin ctx who`. Kubernetes' storage calls pass
the request's context, a chain of `context.WithValue` (request info, tracing, `klog` loggers),
`WithTimeout`/`WithCancel` over net/http's request context, and `wait.ContextForChannel` for the
compactor (`compact.go:193`). W0 gives `ctxPrin` only to `Background()`, `TODO()`, their
`WithCancel`/`WithTimeout` children, `WithRequireLeader` and `withVersion`; `WithValue.spec`
deliberately gives no `ctxChild` "because a value may be grpc's outgoing metadata" (batch report,
open question 7). That reason does not hold for any call outside grpc: the outgoing metadata is the
value at key `metadata.mdOutgoingKey{}`, an unexported type (`grpc@v1.84.0/metadata/metadata.go:231,244`),
so only grpc's `metadata` package can set it. And `ctxPrin` is a `ClientV3` predicate, so a
Kubernetes batch cannot introduce it for net/http's or `ContextForChannel`'s contexts without a
law of W0. As it stands, every Kubernetes call through `kvAt` (P1, P4, P6, P15-P18 of round 1's
table) has a premise its caller cannot meet. This is a missing law, not a user decision.
Fix: (a) `WithValue.spec` keeps the key (`ctxWithValue parent ctx key v`, or a pure premise) and a
law `ctxPrin_withValue : ctxPrin ctx who ∗ ctxWithValues ctx ctx' ∗ ⌜key's type ≠
grpc.metadata.mdOutgoingKey⌝ ⊢ ctxPrin ctx' who`; and (b) an introduction a non-W0 batch can
discharge for a root context of its own (net/http's request context, `ContextForChannel`): e.g. a
context-level persistent `Context.ctxNoMeta ctx` ("no grpc outgoing metadata in its chain", with
the intro laws above) and `ctxPrin_of_noMeta : Context.ctxNoMeta ctx ⊢ ctxPrin ctx who`, grpc's
`NewOutgoingContext`/`AppendToOutgoingContext` (2a) keeping `ctxPrin` when no `token`/`authorization`
key is added. Kubernetes' tracing interceptor adds `traceparent` metadata only, which (b) allows.

### F7. A stream with a negative revision is not pinned: `streamMatches` is false of it

`rangeStream` pins only `r.Revision == 0` (`v3_server.go:238`); a negative revision passes
`checkRangeStreamRequest` (`api/v3rpc/key.go:169-179`) and `toRangeRequest` (`client/op.go:185`)
unchanged, and each page reads at the then-current revision (`rangeKeys`: `rev <= 0` → `curRev`,
`mvcc/kvstore_txn.go:78-80`), the final count too. So `GetStream(ctx, k, WithRev(-1))` returns
pages of different revisions, and `streamMatches` (the pages' key-values are one answer `a`, at
the default ordering) claims what no single `Step` gives. Not new in round 2 (round 1 missed it);
no user found passes a negative revision (Kubernetes passes `withRev > 0` or nothing,
`store.go:945-947`), but the slot is false and `ReqGetStream` takes any `rev int64`.
Fix: a premise `0 ≤ (opGetM key gs).rev` on `KV.GetStreamTriple` (and `0 ≤ r.revision` on
`RemoteKV.RangeStreamTriple`), or `streamMatches` only for `0 ≤ r.revision`; `ReqGetStream`'s
Assumes gains `rev ≥ 0`. Record the Go behavior in `nonissues/` (unary `Range` treats a negative
revision as the current one, `RangeStream` as "unpinned current": its stream is no snapshot); I
did not write it (read-only).

## Second tier

* **S1. `UserGet("")` by an unauthenticated principal with auth on answers `ErrUserNotFound`**:
  `authApplierV3.UserGet` lets the call through when `r.Name == aa.authInfo.Username` and both are
  `""` (`apply/auth.go:222-230`), then `UserGet` fails `ErrUserNotFound` (`auth/store.go:589-594`);
  `mayCall none (.userGet [])` is false, so the model answers only `adminErr none = .userEmpty`.
  Fix: `.userGet n => who = some n ∨ (who = none ∧ n = [])` in `mayCall` (a user named `""` cannot
  exist, so the success branch is `userNotFound`). Reachable by `cli.UserGet(ctx, "")`; no user found.
* **S2. `ctxOk`'s intended realization does not support `WithCancel.spec`/`WithTimeout.spec`.**
  The header realizes `ctxOk` as the triples of `Err`, `Done`, `Value` with `Value` "whatever". The
  constructors over an arbitrary parent also call `parent.Deadline()` (`WithDeadlineCause`,
  `context.go:637`), rely on `parent.Value(&cancelCtxKey)` returning a valid `*cancelCtx` whose
  `done` they lock and mutate (`parentCancelCtx`, `propagateCancel` `:492-505`), and on an
  `afterFuncer` parent's `AfterFunc` (`:508-519`). The specs are true of Go's documented contract,
  but the realization must say so: add `Deadline`'s triple, "`Value(&cancelCtxKey)` is `nil`, not a
  `*cancelCtx`, or one meeting Perennial's `isCancelCtx` with this context's Done channel", and an
  `AfterFunc` contract when the dynamic type has one.
* **S3. `EnvCfg.leaseExpiry = false` has no realization at the server.** K2 says which `cfg` a
  member gets only for `autoCompact`; with `leaseExpiry = false` the lessor's revoke of an expired
  lease (K5) must fire an `envUpd` that forbids it, which no timeless proof can show unreachable.
  Say in K2/K8 that it is a trusted deployment premise (time), so the user sees it as such.
* **S4. The doSerialize nonissue's suggested fix does not fix it.**
  `nonissues/etcd-doserialize-auth-enable-race.md` is accurate about the race (checked:
  `v3_server.go:1035-1057`, `AuthInfoFromCtx` returns `nil` with auth off, `store.go:1073-1075`,
  so `ai.Revision == 0` skips the re-check; `Range`, the read-only `Txn` and `RangeStream` all use
  it; reachable since the apply loop runs beside the read). But its Notes' fix ("fail with
  `ErrAuthOldRevision` when `s.authStore.Revision()` changed") misses it: `AuthEnable` keeps the
  auth revision (`store.go:299`) and a key write does not touch it. The Proof section's alternative
  (re-check the permission after the read whenever auth is enabled then) is the one that works; fix
  the Notes. The model relies on the race not happening (`kvStep .range`'s linearizable success
  needs `permits` at the firing state), which is disclosed in K8 as open: not silent, but
  `kvStep`'s comment should cite the nonissue too.
* **S5. The GetStream leak nonissue overstates the window.** With capacity 1, after the consumer's
  last receive the next send fills the buffer; the goroutine blocks only on the send after that
  (`kv.go:175-188`). A stream of exactly two chunks that ends normally does not leak; the test
  needs at least three chunks (or two and a terminal error). Same in the `streamAt_recv` docstring.
* **S6. Snippet assumptions.** `ReqAuthRefusal` needs `outside ∉ [pfx, end)` (it only says so by the
  name) and `end` neither `""` nor `"\x00"` with `pfx < end` (with `end = ""` the range is the
  key `pfx`, `kv.Key >= end` holds and it panics). `ReqGetStream` needs `rev ≥ 0` (F7).
  `ReqGetStreamCompacted`'s comment "the only definite error mid-stream" is wrong
  (`ErrAuthOldRevision` can follow the final chunk: `doSerialize`'s post-check after
  `rangeStream` returned, `v3_server.go:1053`; it is covered by the `Q` disjunct).
* **S7. Obsolete wording**: `streamMatches`' and `kv__GetStream.lean`'s "a sorted or filtered stream
  is sorted page by page": the server refuses custom orders and revision filters with
  `Unimplemented` (`api/v3rpc/key.go:173-178`, an `.other` error), except the `NONE`-order quirk of
  `issues/etcd-rangestream-sort-none.md`. `ctxPrin_persistent.spec` duplicates the clause added to
  `handles_persistent.spec`. `ctxPrin`'s future token intro should be for malformed tokens only
  ("issued to no one" is not a persistent fact of a well-formed simple token string).
* **S8. Lease-read permission errors are unconditioned**: `leaseStep`'s `.leaseTimeToLive` (keys)
  and `.leaseLeases` may answer `permErr who` at any state, auth off included, where etcd cannot
  (`v3_server.go:607-632,751-776` check only with auth on). No user found relies on excluding it;
  `σ.auth.enabled ∨ <stale local state>` cannot be stated without views, so leave it, but say so in
  the docstring.

## Snippets

* `ReqListPrefix`: provable (`etcdState_sizeFits` bounds `count`; `cut ⇒ limit < length`, so a
  `More` page is non-empty).
* `ReqCtxErrors`: provable (`WithCancel.spec`, `ctxPrin_child`, `cancelOk`; a revision-0 read is
  never `.compacted`; `getReply`'s `nil` on error).
* `ReqTxnNestedRangeHeaders`: provable (linearizable read-only txn: `v = σ.kv`, every nested
  `.range` at `v.rev`, the outer header `v.rev` as `evs = []`; `ResponseOpM.ofResp.range` gives the
  non-nil header; `etcdState_revFits` for `W64`).
* `ReqGetStream`: provable for `rev ≥ 0` (non-final headers `none`, so the first non-nil one is the
  last's; `last.count = W64 a.count = len(keys)` with `sizeFits`; `revErr` none gives `rev ≤ hdr`;
  a non-empty key list forces `hdr ≥ 1`); for `rev < 0` it is "proved" from the false F7.
* `ReqGetStreamCompacted`: provable (the terminal error is `Q` of a `Step` of a revision-0 range,
  never `.futureRev`, or `.compacted`, or indefinite; `errorsIs_errVal`, `errVal_inj`); stays so
  after F1's fix.
* `ReqAuthRefusal`: provable once S6's assumptions are added (u not root, `covers u read {outside}`
  false, so success is impossible; the second read's keys are in the range by `rangeKVs`).
* The others are unchanged from round 1 and stay provable (the new `ctxPrin` premise is in the
  package comment).

## Targets ranked by need of revision

1. **`SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean`**: F1 (`ms ≠ []`), F2 (stream open), F5, F6
   (`ctxPrin` intros), F7 (negative-revision streams); S7.
2. **`SpecPlan/Spec/context/Api.lean`**: F3 (`ctxChild_done`), F4 (`WithValue`'s key), F6 (keep the key),
   S2 (the realization).
3. **`nonissues/`**: S4 (the doSerialize fix note), S5 (the leak window); a new entry for F7.
4. **`examples/specreq/clientv3kv/`**: S6.
5. **`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`**: S1, S8; `notes/specs-only/top.md`: S3.
6. **`Wire.lean`, `State.lean`**: no finding (the nested header and `sizeFits` check out).

## Verdict

Not done. The model repairs (P-F3's nine mismatches, `authFailed`, the nested headers, the chunk
shape, the `Txn` builders, `sizeFits`) are correct against the code. Seven first-tier findings
remain, all local: two stream slots still false of etcd (F1: `ErrCompacted` before any chunk on
Kubernetes' limited unpinned lists; F2: `ErrAuthFailed` at stream open), one stream slot false for
negative revisions (F7, found this round), three false context or principal laws (F3
`ctxChild_done`, F4 `WithValue`'s key, F5 `ctxPrin_of_isContext`), and the new `ctxPrin` premise
unmeetable by Kubernetes (F6: a missing `WithValue` law and a root introduction other batches can
discharge).
