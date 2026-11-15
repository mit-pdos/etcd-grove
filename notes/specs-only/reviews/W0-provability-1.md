# W0 (the anchor), provability review, round 1

Reviewer: provability (soundness, snippets). Commit under review: `f1ec1df585` (draft, before
review). Read: `SpecPlan/Spec/go_etcd_io/etcd/api/v3/{Model,State,Wire}.lean`, `SpecPlan/Spec/context/Api.lean`,
`SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean` and the KV-path specs (`kv__*`, `txn__*`, `ContextError`,
`isSafeRetry*`, `retryKVClient__*`), `SpecPlan/Spec/go_uber_org/zap/`, `examples/specreq/clientv3kv/*.go`,
`notes/specs-only/top.md`, the `## from W0` sections of `req/`. Go: the pinned fork (`.lake/src`,
`a4d2bb17`): `client/{kv,txn,op,compare,retry,retry_interceptor,client}.go`,
`server/etcdserver/{v3_server.go,txn/,apply/auth.go,api/v3rpc/{key,member,maintenance}.go}`,
`server/storage/mvcc/{kvstore,kvstore_txn,index}.go`, `server/lease/{lessor,lease}.go`,
`server/auth/store.go`, `api/v3rpc/rpctypes/error.go`; `examples/etcd/txnlin`. The batch report
`batch-W0.md` was read only after these findings were formed (its open question 2 anticipates
F7's `UserGet`/`RoleGet` point; nothing else below is in it).

File references below are to the fork's sources under `.lake/src/` unless they start with `SpecPlan/Spec/`.

## What is good

* **The model's KV semantics are close to the code, quirks included.** Checked line by line:
  `RangeReq.pushdownLimit` = `rangeLimit` (`server/etcdserver/txn/range.go:84-93`), the filters,
  `sorted` (the `NONE`-with-non-key-target ascend rule, `range.go:115-145`), the response cut and
  `More` (`range.go:147-160`), `count` the index's total (`withTotalCount = true` for unary
  `Range`, `v3_server.go:149`; `mvcc/index.go:112-137`), `FastKeysOnly` reporting lease 0
  (`mvcc/kvstore_txn.go:90-105`), the header revisions of put, delete (`kvstore_txn.go:197-207`) and
  txn (`txn/txn.go:96-100`), `checkPut`'s order (lease, then the ignore flags' key: `txn/put.go:69-100`),
  `compareKV` including the mismatched-target and missing-key value cases (`txn/txn.go:283-361`),
  compares and nested branch choices at the pre-transaction view (`compareToPath`, `txn.go:262-276`),
  reads after earlier writes in a txn (`storeTxnWrite.Range`, `kvstore_txn.go:189-195`), the
  check errors on the chosen path only, in order (`checkTxn`, `txn.go:225-252`), the permission
  pairs including `prevKv` reads, nested txns and `checkLeasePuts` (`apply/auth.go`), and
  `Compact`'s `ErrCompacted`/`ErrFutureRev` (`mvcc/kvstore.go:197-221`).
* **The error discipline is right in shape**: a definite error is a linearized answer, an
  indefinite one gives nothing; the fork's `8a24be2a3` (`retry_interceptor.go:83`) closes the
  context-error resend of writes, and the remaining resends (token refresh, learner refusal,
  never-sent) are all after attempts the server never applied.
* **`envUpd` works for the clients that matter**: txnlin's invariant (`σ.leases = ∅`, the store
  and revision untouched by alarms, publications and compaction) is stable under every
  `EnvStep`; Kubernetes' and an "owned key, no lease" invariant are too. The cluster can fire it:
  the lessor's revoke goes through raft under `WithRoot`, and an already-revoked or auth-stale
  revoke changes nothing and fires nothing.
* **Snippets**: 15 of 18 are provable from the specs as written (sketches in "Snippets" below).
* `etcdState`/`etcdLb`'s laws are not vacuous (exclusivity and `etcdLb_reach` are false at `True`);
  `callErr`'s laws pin the kinds (`indefCall_pure` rules out `callErr (errVal e) .other` for a
  definite `e`).

## First tier

### F1. `KV.*Triple` is false in auth mode: a failed token refresh returns `ErrAuthFailed`, which no `Step` answers

`unaryClientInterceptor` (`client/retry_interceptor.go:91-99`): on `ErrUserEmpty` (with a
password configured), `ErrInvalidAuthToken` or `ErrAuthOldRevision`, it calls `refreshToken` →
`getToken` (`client/client.go:285-306`) → `c.Auth.Authenticate`, and **returns that call's error
as the write's error** (`return gtErr`). If the user's password was changed or the user deleted
meanwhile, that is `rpctypes.ErrAuthFailed` = `errVal .authFailed` after `ContextError`. Then
`KV.PutTriple`'s post (`SpecPlan/Spec/.../client/v3/Api.lean:602`) needs either `Q σ σ' (.err .authFailed)`
with `Step who (.put _) σ σ' (.err .authFailed)`, which no disjunct of `Step` gives (`kvStep .put`
never answers `authFailed`, and `EtcdErr.refusal` (`Model.lean:316`) does not list it), or
`indefCall err`, which `indefCall_pure` forbids for a definite error. The same for every KV,
lease, auth, cluster and maintenance call of a client with a username and password.
Callers affected: every client in auth mode (`isClient c γ (some u)`), and 1c's interceptor proof,
which cannot discharge its `req/` item 2 ("if it gives up, it fires the caller's update with that
refusal, or returns an indefinite error").
Fix: add `.authFailed` to `EtcdErr.refusal` (the attempt was refused, nothing applied; the client
library fires the refusal itself), and say in 1c's `req/` item 2 that `gtErr` is such a refusal or
indefinite. Check what else `Authenticate` can return definitively (`ErrNoPasswordUser` is not in
rpctypes' map, so `.other`).

### F2. `streamAt_recv`/`wireStreamAt_recv`: a mid-stream `ErrCompacted` of an unpinned stream is no `Step` answer

`EtcdServer.rangeStream` (`server/etcdserver/v3_server.go:197-283`) reads a stream as several
`txn.Range` calls, pinning `r.Revision = headerRev` after the first page when the client asked for
revision `0`. A compaction above `headerRev` between two pages makes the next page fail with
`ErrCompacted` (`mvcc/kvstore_txn.go:81-83`), which ends the stream after chunks were delivered.
`wireStreamAt_recv.spec` (`Api.lean:983`) and `streamAt_recv.spec` (`Api.lean:966`) say a terminal
definite error carries `Q σ σ' (.err e)`, i.e. `Step who (.range r) σ σ' (.err .compacted)` for the
request `r` the client sent, whose `revision` is `0`: `RangeReq.revErr` (`Model.lean:597`) never
gives `.compacted` then, and `.compacted` is not a refusal. The slot is unrealizable by etcd's
server, so `kv.GetStream.spec` rests on a false boundary. (A stream pinned by the client,
`revision > 0`, is fine: the persistent update fires at the later state where `revErr` is
`.compacted`.)
Callers affected: Kubernetes' `GetList`/watcher initial list (`etcd3/store.go`), the snippet
`ReqGetStream` (which only returns on the error, so stays provable once the slot is weakened).
Fix: a terminal error after at least one chunk carries no `Q` (it settles the stream as failed:
an `indefCall`-like disjunct, or a `.compacted` disjunct without `Q`); or model the pinning (the
stream's `Step` is of `r` with `revision := headerRev` from the second page on).

### F3. The model forbids answers etcd gives (the anchor is what K4 says every answer is)

Each of these is an answer etcd's code gives that no `Step` admits, so the server batches cannot
prove K4 for it (`req/..._api_v3rpc.md` item 2). Small fixes each, but together they make `Step`
unsound outside the KV path:

1. **`State.permits` needs a principal even when nothing is checked** (`Model.lean:759`). etcd
   checks per pair and per attached key (`isOpPermitted`), so with no pair to check no user is
   needed: `LeaseRevoke` of a live lease with no attached keys by an unauthenticated client
   succeeds (`apply/auth.go`, `checkLeasePuts`: `Lookup` then per-key checks only), and the empty
   txn (`Txn(ctx).Commit()`, `OpTxn(nil,nil,nil)`) succeeds for `who = none` with auth on
   (`checkTxnPermission` loops over nothing; `doSerialize`, `v3_server.go:1035-1057`). The model
   forces `permErr none = .userEmpty` there. Fix: put the `∃ u, who = some u` inside each check
   (`∀ p ∈ ps, (auth off ∨ ∃ u, ...)`), or add `ps = [] ∧ no attached key` as a disjunct.
2. **A serializable read-only txn's permission is checked at `σ`** (`Model.lean:835-847`), but etcd
   checks it at the answering member's auth state (`EtcdServer.Txn`, `v3_server.go:344-370`: `chk`
   in `doSerialize` on the local store), which may be behind (auth not yet enabled there, a role
   not yet revoked). The range case already has the relaxation (`¬ permits ∨ serializable`); the
   txn case needs the same (`permits ∨ (t.readonly ∧ t.serializable)` on the success side).
3. **`TxnRun` checks a range's revision as a plain range does**, but in a txn `checkRange`
   (`txn/range.go:162-172`) compares against `FirstRev()` = `compactMainRev`, which is `-1` before
   any compaction (`mvcc/kvstore.go:105`): a negative `revision` below it is `ErrCompacted` inside
   a txn (and current outside one). `TxnRun.rangeErr` (`Model.lean:674`) with `revErr` forbids it.
   Fix: a txn-specific `revErr` (`r.revision ≠ 0 ∧ r.revision < max(compacted, -1)`), or treat a
   negative revision in a txn as `.compacted`-or-current.
4. **A txn containing an empty `RequestOp`** is rejected by the gRPC layer with `ErrKeyNotFound`
   (`api/v3rpc/key.go:330-344`, `checkRequestOp`'s default), not among the txn's refusals
   (`Model.lean:835-840`), while `TxnRun.empty` executes it. Unreachable from `clientv3`
   (`toRequestOp` panics), reachable over the wire. Fix: add `.keyNotFound` to the txn's gRPC
   refusals.
5. **`AuthEnable` does not bump the auth revision** (`auth/store.go:270-303`: `setRevision` of the
   stored one, no `commitRevision`); the model's `bump` (`Model.lean:945`) does, so a later
   `authStatus` reports a revision etcd does not. `AuthDisable` does bump (`store.go:316`).
6. **Orders the model fixes and etcd does not keep**: `UserGrantRole` sorts the roles
   (`store.go:572-573`; model appends, `Model.lean:971`, and `userGet` returns the list);
   `RoleGrantPermission` sorts by key (`store.go:836-845`; model appends, `Model.lean:1003`);
   `MemberList`/`MemberAdd`/... return `RaftCluster.Members()` sorted by id
   (`membership/cluster.go:123-132`; model `σ.members` in insertion order, `Model.lean:1034,1060`);
   `Alarm(GET)` iterates maps (`v3alarm/alarms.go:95-110`; model `σ.alarms` exactly,
   `Model.lean:1062`). Fix: answer a permutation (or the sorted list) in each.
7. **Auth reads and validations**: `UserGet` of oneself and `RoleGet` of a role one has need no
   administrator (`apply/auth.go`, `UserGet`/`RoleGet`; `needAdminPermission` lists neither); the
   model requires admin (`Model.lean:916`). `RoleGet "root"` returns `rootPerm`, not the stored
   permissions (`store.go:662-672`). `RoleGrantPermission` fails with `ErrInvalidAuthMgmt` on an
   invalid range and `ErrPermissionNotGiven` on a nil permission (`store.go:813-819`). `UserChangePassword`
   of a no-password user keeps it password-less (`store.go:513-518`), so `Authenticate` still
   fails, where the model sets `some pw` and then requires success (`Model.lean:961`).
8. **Lease reads**: `LeaseTimeToLive` reports a remaining TTL above the granted one after a leader
   change (`lessor.Promote` → `refresh(extend)` sets expiry to `extend + remainingTTL`,
   `lease/lessor.go:480-492`, `lease.go:84-89`; reported at `v3_server.go:650`), while the model
   requires `ttl ≤ gttl` (`Model.lean:891`); `LeaseTimeToLive(keys)` and `LeaseLeases` may answer
   `ErrPermissionDenied` (`checkLeaseTimeToLive`/`checkLeaseLeases`, `v3_server.go:607-632,751-776`),
   which the model's `leaseStep` does not allow.
9. **Membership**: `MemberAdd` with unparsable peer URLs answers `ErrMemberBadURLs`
   (`api/v3rpc/member.go:44-47`); an id of a removed member or an existing one answers
   `ErrMemberNotFound`/`ErrMemberExist` (`v3rpc/util.go:36-38`); neither is in `clusterStep`'s
   `memberAdd`. The admin check of member and alarm changes is made at the member's local auth
   state before proposing (`server.go:1385-1404`, `authMaintenanceServer.Alarm`), not at `σ`: the
   same relaxation as F3.2 is needed.

### F4. Snippet `ReqListPrefix` is unprovable: nothing bounds `Count`

`resp.More != (resp.Count > int64(len(resp.Kvs)))` (`examples/specreq/clientv3kv/put_get.go`)
needs `count < 2^63` (`RangeRespM.ofAns`: `m.count = W64 a.count`, `Wire.lean`). `count` is the
number of keys in the range, bounded by no law: `etcdState_revFits` bounds revisions, but one
revision may write any number of keys in the model (`max-txn-ops` is not in it). Fix: a law
`etcdState_sizeFits` (the number of events, hence of keys and of any key's version, fits `int64`),
proved by the cluster from the same step bound as `revFits`; or drop the comparison.

### F5. Snippet `ReqCtxErrors` is unprovable: no spec of `context.WithCancel` over `ctxOk`

`ReqCtxErrors` (`errors.go`) calls `context.WithCancel(ctx)` on an arbitrary `ctxOk ctx` ("Contexts
are any contexts"). Perennial's `WithCancel` specs (`Perennial/Proof/context/WithCancelGen.lean`)
take a parent that is `isContext` or `Background()`; `SpecPlan/Spec/context/Api.lean` gives none over
`ctxOk`. Fix: a `WithCancel.spec` in `SpecPlan/Spec/context/Api.lean` (parent `ctxOk`, child `ctxOk` and
`ctxDone` after `cancel`), or start the snippet from `context.Background()`.

## Second tier

* **S1. `callErr`'s `.other` excludes "etcd's messages", but rpctypes has errors the model lacks**
  (`ErrGRPCCanceled`, `ErrGRPCDeadlineExceeded`, `ErrGRPCNotSupportedForLearner`,
  `ErrGRPCPermissionNotGiven`, `ErrGRPCInvalidClientAPIVersion`, `ErrGRPCWatchCanceled`:
  `rpctypes/error.go:30,40,68,88,97-98`); `rpctypes.Error` turns them into `EtcdError`s
  (`Api.lean:85`). They fit no kind as worded. `Canceled` is exactly the write-may-have-applied case
  of the fork's `retry_put_ctx_error_test.go`, so it must be indefinite. Fix: `.other` is "any error
  that is not `.etcd e` for a modelled `e`", or add the six to `EtcdErr` (the first two indefinite).
* **S2. The interceptor's write resends are listed incompletely.** The Api header (`Api.lean:19`:
  "only when it was never sent") and 1c's `req/` item 2 omit the learner path:
  `isSafeRetry` resends any call, writes included, after `ErrGRPCNotSupportedForLearner` when the
  client has more than one endpoint (`retry_interceptor.go:346-348`). Sound (the server's
  interceptor refuses before the handler), but 1c's proof needs it stated: "resent only after an
  attempt never sent or refused before the handler (learner) or refused without effect (token)".
* **S3. "Answers at the last firing" is wrong for linearizable reads** (`top.md:55,124`,
  `req/..._api_v3rpc.md` item 3). The member reads its applied state after the read index, which
  may be behind the latest committed state the update was already fired at. The client specs only
  need "the `Q` of some firing" (they say `∃ σ σ' res, Q σ σ' res`), and txnlin resolves which with
  its read-revision prophecy `rp` (`linkvtxn.go:968-978`), not the last firing. Restate: "answers
  with the `Q` of the firing at the state it read", and require the update to be registered before
  the read index is taken.
* **S4. A possible TOCTOU in `doSerialize` (Go code, found by reading; not tested).** With auth
  disabled at the check, `AuthInfoFromCtx` returns `nil` (`auth/store.go:1072-1075`), `chk` passes
  with empty credentials and the post-read revision check is skipped (`ai.Revision == 0`,
  `v3_server.go:1053`). If `AuthEnable` and then a permitted write apply between `chk` and `get`,
  an unauthenticated (or unpermitted) client reads a value written after auth was enabled. No
  model state has both that store and auth off, so K4 cannot be met in that interleaving. Not in
  `issues/` or `nonissues/` (only the TLS variant, `nonissues/etcd-auth-old-revision-auth-disabled.md`).
  Suggest a `nonissues/` entry (or an `issues/` one with a failpoint test) and a scope note in K8;
  uncertain how reachable the window is.
* **S5. `--max-request-bytes`-reachable crash not in K8**: `UserAdd`/`RoleAdd` with a name over
  32768 bytes makes every member exit (`issues/etcd-auth-useradd-long-name-fatal.md`, unfixed in
  the fork: `store.go:428-431` checks only emptiness). With zap's `Fatal` as divergence it does not
  break safety, but the old proof bounded names and K8 claims to list every scope premise; say which
  (a premise on the auth client calls, or "liveness only, no premise").
* **S6. `ReqPutErrors` relies on `errors.Is` against `.other` errors** (Kubernetes' style). The
  grpc `req/` item 2 asks 2a for it ("true only for `.etcd e`"), but the `.other` kind includes the
  interceptor's `gtErr` (any `Authenticate` error) and arbitrary transport errors; 2a must state it
  of the client's own returned values, not only of statuses. Fine as a need; make it a law of the
  slot (`callErr_isNot`) so the snippet's proof cites a law rather than a `req/`.
* **S7. `callErr` is not stated functional.** `ContextError.spec`'s case split on `k` is sound only
  if one error has one kind (two `.etcd e`, `.etcd e'` for one status would make it false). Add
  `callErr_agree : callErr err k ∗ callErr err k' ⊢ ⌜k = k'⌝` (2a's obligation).
* **S8. `etcdState_revFits` is plausible but its realization is not sketched**: etcd itself
  never refuses at `2^63` (mvcc wraps), so the cluster's invariant can keep `rev < 2^63` only from a
  step budget fixed by the adequacy theorem, which no `req/` names (K7 says "from the adequacy
  theorem's step bound"). Uncertain whether Perennial's adequacy offers a per-step token today;
  name the resource in K7 (and use it for F4's size law too).

## Checks asked for in the brief

* **(a) Model vs. server.** KV: matches, except F3.1 (empty-permission checks), F3.2 (serializable
  txn auth), F3.3 (negative txn revisions), F3.4 (empty op). Over-approximations that are harmless:
  any request may be refused (`.userEmpty`, `.noSpace`, ... at any state); `tooManyOps` and
  `duplicateKey` at any txn; `tooManyLearners` at any learner add; a lease may expire at once.
  Leases, auth, members, alarms: F3.5-F3.9.
* **(b) Linearizability.** txnlin: goes through as sketched (single member, its generator never
  sends a compare-only txn, `NThen ≥ 1` at `linkvtxn.go:780`; no leases, so `EnvStep` changes
  neither store nor revision; failed writes are pending in porcupine's model, which absorbs a
  firing after return), with S3's correction on reads. Kubernetes: fine; its compactor guards
  `rev == 0` (`apiserver/pkg/storage/etcd3/compact.go:243`), so the `Compact` premise is met.
  `Mutex` fencing by `If(CreateRevision(myKey) = myRev)`: follows from `TxnRun`'s compares at the
  pre-state.
* **(c) `envUpd`.** Usable (above) and dischargeable for lease expiry (root token,
  `WithRoot`), compaction (the compactors skip `rev ≤ 0`), alarms (a re-activation is a no-op that
  fires nothing) and publication. No other observable change by the environment found (checkpoints,
  cluster version and downgrade change nothing in `State`). Missing only as a request: a client's
  `Alarm(ACTIVATE)` (maintenance API; `Req` has no constructor for it).
* **(d) At-most-once.** Holds of the fork: the context-error resend is closed for
  `nonRepeatable` (`retry_interceptor.go:83`), streams are not retried (`withMax(0)`,
  `client.go:269`), no gRPC service-config retry (`internal/resolver/resolver.go:44`), the other
  resends follow unapplied attempts (S2). F1 is the gap.
* **(e) Definite vs. indefinite.** Every model-definite error a write can get is decided before the
  proposal or is its entry's apply result; `.unhealthy` is both refusal and indefinite (harmless).
  Gaps: F1 (`authFailed` from the refresh), S1 (unmodelled rpctypes errors).
* **(f) `Compact(0)` and `revFits`.** The premise is needed (`mvcc/kvstore.go:199`: `0 > -1`
  succeeds at first, then the restart divergence of the issue), and every compactor meets it.
  `revFits`: S8.
* **(g) Snippets**: below.

## Snippets

* `ReqPutThenGet`, `ReqPutRevision`, `ReqDeleteThenGet`, `ReqGetAtRevision`: provable. The owner's
  invariant keeps "k written only by this caller, lease 0" (stable under `EnvStep`: `leaseExpire`
  touches only keys whose lease is live and non-zero; `σ.leases 0 = none` by `Reach` from
  `State.init`); each update's `Q` records `etcdLb` (`etcdState_lb`), the next call's firing gives
  `Reach` (`etcdLb_reach`); `kvStep .put` gives `modRev = createRev or prev`, the header
  `σ.rev + 1`; `revFits` at the post-state makes the `int64` comparisons exact.
* `ReqListPrefix`: F4. Otherwise the arithmetic holds (`pushdownLimit = 3`, `cut ⇔ count > 2`).
* `ReqPutErrors`: provable given S6's law (the `errors.Is` panics); `putReply` gives `resp = nil`
  exactly on error, `msgOwn_ne_null` non-nil on success.
* `ReqGetErrors`: provable (`rev ≤ σ.rev` by `etcdLb_reach`; `futureRev` is no refusal).
* `ReqCtxErrors`: F5; with a `WithCancel` spec, provable (`.compacted` impossible at revision 0).
* `ReqCASModRevision`, `ReqCreateIfAbsent`, `ReqTxnReadsOwnWrites`, `ReqTxnNested`,
  `ReqTxnReadonlySerializable`: provable from `TxnRun` (one response per op of the branch; the
  missing key compares as zero; reads after writes in the txn store; the nested compare at `s0`;
  `createRev ≤ v.rev` and `createRev ≥ 2` by `Reach`).
* `ReqCompactReached`: provable (`rev ≥ 1` meets `rev ≠ 0`; `rev ≤ σ.rev` excludes `futureRev`;
  `compacted ≥ rev` afterwards by monotonicity, so the read at `rev - 1 ≥ 1` errs).
* `ReqRevisionsMonotone`, `ReqSerializableGet`, `ReqGetOptions`, `ReqDo`, `ReqOpGetters`: provable
  (`IsView` keeps the view a prefix: `modRev ≤ v.rev`, `createRev ≤ modRev` by `Reach`; withTop's
  limit 1 after the sort; the empty txn `succeeded`).
* `ReqGetStream`: provable from the specs as written (chunks non-nil without an error, key order and
  range by `streamMatches` at the default ordering, `hdr ≥ rev` from `revErr`), but the slot it
  rests on is F2's.

## Targets ranked by need of revision

1. **`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`**: F1 (refusal list), F3 (nine places where `Step`
   forbids etcd's answer), S1.
2. **`SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean`**: F2 (stream slots), S1 (`callErr` wording), S2,
   S6, S7.
3. **`examples/specreq/clientv3kv/`** with **`SpecPlan/Spec/context/Api.lean`** and **`Wire.lean`/`State.lean`**:
   F4 (a size law), F5 (`WithCancel` over `ctxOk`), S8.
4. **`notes/specs-only/top.md`** and the `req/` sections: S3 (reads), S4/S5 (K8), S2 (1c's item 2).
5. **`SpecPlan/Spec/go_uber_org/zap/`**: no finding (`Fatal` as divergence follows the repository's decision,
   `specs-ref/notes/decisions.md:2393`).

## Verdict

Not done: five first-tier findings. F1 and F2 make client contracts false of the code (auth mode;
unpinned streams under compaction), F3 makes the anchor's `Step` forbid answers etcd gives outside
the plain KV path (so K4 is unprovable there), and F4/F5 leave two snippets unprovable. The KV core
of the model is accurate and the at-most-once argument holds of the fork; each repair is local
(a refusal, a relaxed slot, a permission definition, permutations, a size law, a context spec).
