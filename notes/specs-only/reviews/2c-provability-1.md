# Batch 2c, provability review, round 1

Reviewer: provability (soundness, snippets). Commit under review: `b5cecfd608` (the 2c draft).
Read: `ApiReq.lean` and every 2c spec named in the brief, `read/`, `pkg/v3/{wait,idutil,notify}/`,
the snippets `examples/specreq/{etcdserverreq,wait}/`, `req/go_etcd_io_etcd_server_v3_etcdserver.md`
("from 2c"), W0's `Model.lean`/`State.lean`, 1c's `ApiClient.lean` (`callAU`, `reqRetryRep`), 2a's
`v3rpc/Api.lean` (`etcdUnary`), 2d's `ApiApply.lean` (`histPropose`), R1's `Api.lean` header. The Go
code: `.lake/src/server/etcdserver/{v3_server.go,read/read.go,server.go,txn/}`,
`.lake/src/server/auth/store.go`, `.lake/src/pkg/{idutil,notify}`. `batch-2c.md` was read only
after the findings below were written; where it already records a point, the finding says so.

## What is good

- **`SrvCallTriple`** is the right shape: the update written once, three outcomes, `B` returned on
  every path. I walked `processInternalRaftRequestOnce` (`v3_server.go:1059-1134`) path by path:
  `ErrTooManyRequests`, the token error, the marshal error and `ErrRequestTooLarge` are before
  `Register` and before `Propose` (outcome 2 is honest); a `Propose` error, `cctx.Done()` and
  `s.done` are outcome 3 (sound: a dropped proposal could be given back, but unsettled is never
  wrong); the apply's `ErrAuthOldRevision` is given back (the auth applier refuses before any
  change). `parseProposeCtxErr` (`server.go:2382-2413`) only returns `ErrCanceled`, the timeouts or
  the context's error: all `srvIndef`.
- **The wait registry** (`wait/Api.lean`) is sound as stated. The one-time `waitTok` excludes the
  `dup id` panic; `Trigger`'s `P id x ∨ waitRecv` covers the apply's trigger and the requester's
  "GC wait" (after a GC trigger the late trigger finds nothing, and the `P id x` it brought is
  dropped, harmlessly). Id reuse across runs is excluded by the per-run registry plus `idFresh`;
  where `idFresh` fails (below) the apply could not prove `P id x` for a stale entry, which is the
  right failure point. The HoCAP departure is limited to a generic primitive, like `isLock`.
- **The read loop** (`read.go`): `Read.LinearizableReadNotify.spec` and the realization (the
  readers' bounds deposited under `RLock`, frozen at the swap under `Lock`, the longest bound
  registered with each fresh context, `ApplyWait` then `notify(nil)`) match the code, including the
  retries under fresh ids and the ignored stale read states. The spec is over R1's vocabulary only.
- **`srvStep`'s two extra disjuncts are the code's and no more than a relation over states can say.**
  The race disjunct: `AuthEnable` keeps the revision (`auth/store.go:299`), and with `ai == nil`
  `doSerialize` skips the re-check (`v3_server.go:1052`), so a stalled read can be answered at any
  later auth-enabled state; a TLS `AuthInfo` read while auth is off also passes (`AuthEnable` keeps
  the revision). The keep-alive disjunct: `checkLeaseRenew` (`v3_server.go:574-605`) returns
  `ErrPermissionDenied` (`IsPutPermitted`, `isOpPermitted` also for a missing user), otherwise only
  refusals (`ErrUserEmpty`, `ErrAuthOldRevision`, `ErrInvalidAuthToken`).
- **Writes**: one-shot firing needs `γ.raft.dup = false`, which 2f's rafthttp spec supports; the
  derived update for `LeaseGrant`'s chosen id (`leaseStep` of `id' > 0` implies that of `0`) checks
  out.
- `waitAppliedIndex`, `waitLeader` and `Watchable` are true of the code as assumed contracts.

## First tier

### F1. `Authenticate.spec` is unprovable on three counts (Authenticate, read registry, W0)

(a) **The registry cannot fire an authentication's success.** The read registry fires every
registered update "once for each answer `srvStep` allows" at each history point, and says those
answers are finitely many (`req/…etcdserver.md`, from 2c, item 5). W0's `authStep` answers
`∃ tok, res = .ok (.authenticate tok)` (`Model.lean:1031`), one answer per string: infinitely many,
so the registry cannot fire them all. Firing only the answer the code returns is not possible
either: the token is made later (`GenTokenPrefix` and the apply's `assign`), after the history
point `kp` the ticket must fire at.
*Fix (W0, with 2c):* make the answer carry no token (`.ok .authenticate`), and let `authReply`
carry the token and `tokenUser γ tok name` from the reply, which `irrReply (.authToken name)`
already supplies.

(b) **The token entry's apply errors are not covered.** `raftRequest`'s error (`v3_server.go:877-880`)
is returned before the revision check. The apply's `authStore.Authenticate` (`auth/store.go:337-356`)
returns `ErrAuthNotEnabled` if auth was disabled between `CheckPassword` and the apply, and
`ErrAuthFailed` if the user was deleted. `IrrBody.authToken` fires nothing, and `irrStep .authToken`
leaves `res` free. So outcome 1 of `raftRequest` gives `applyResult` with an arbitrary error and no
history point. `ErrAuthNotEnabled` is neither `refusal` nor `indefinite`, so `Authenticate` can
place it in none of the three outcomes. The ticket was fired at the apply's point, where the step
does allow it, but the proof cannot reach that point.
*Fix:* give `.authToken name` a relation (the apply's answers: `authNotEnabled` iff auth is off,
`authFailed` if the user is missing or has no password, `ok` otherwise; the state unchanged). Have
`Authenticate` pass `raftRequest` an update derived from its persistent one: it fires the caller's
update on an error answer and commits without firing on `ok` (the state is unchanged).

(c) **Known (decision 2): nothing supplies the persistent update.** `Authenticate` takes `rep =
true`. The client passes a one-shot update (`reqRetryRep (.authenticate ..) = false`,
`ApiClient.lean:170-174`), and 2a's `etcdUnary` asks for persistence only for `Req.isRead`
(`v3rpc/Api.lean:185`). 2a's `AuthServer.Authenticate` therefore cannot call this spec today. With
(a) fixed, W0 could count `.authenticate` as a read (`isRead`, and the client's `rep`): its step
never changes the state.

### F2. `RangeStream.spec` (assumed contract) is false of the code; candidate Go bug

(a) **The post misses "terminal chunk sent, then `ErrAuthOldRevision`".** `get` runs
`rangeStream` (`v3_server.go:188`), which sends every chunk, the terminal one included
(`v3_server.go:262`). Only after that does `doSerialize` re-check the token's revision and return
`ErrAuthOldRevision` (`v3_server.go:1052-1054`). The post (`EtcdServer__RangeStream.lean:61-63`)
allows `fin = true` only with `err = nil`.
The proof cannot repair this inside the spec either. The terminal chunk delivers `Q` from the
ticket at the first page's point `kr1`, which needs `srvStep` to allow the `ok` answer there, that
is the permission at `kr1`. The proof learns that only from the revision check, which runs after
the send.

**Go bug, candidate (no file written: this review is read-only).** In a unary `Range` the answer
is dropped when the auth revision moved during the read. A `RangeStream` has already sent its
chunks by then: a user whose read permission is revoked between the check and the paged reads
receives keys read after the revocation, and only then the error. No `issues/` or `nonissues/`
file covers it (checked: `etcd-rangestream-*`, `etcd-doserialize-auth-enable-race`). Fix on the
fork: re-check the revision (when `ai.Revision != 0`) before each `Send`.

(b) **Missing premise.** The pre has only `rm.key ≠ [] ∧ rm.validSort`. The handler also refuses
custom sort orders and revision filters (`checkRangeStreamRequest`, `v3rpc/key.go:169-180`), and
`rangeStream`'s paging (`nextKey = last key + 0`) is wrong without that check. Add the premise (the
default ordering and no revision filters); 2a establishes it.

### F3. `read/Api.lean`: `readEnvOk` can never be established

`readEnvOk` (`read/Api.lean:132`) is a `Prop` whose conjuncts are Texan triples with precondition
`True`. Outside `iprop(…)`, a triple expands to `⊢ ∀ Φ, P -∗ ▷ … -∗ WP …`
(`iris/BI/WeakestPre.lean:155-157`), which is closed: it may use no resource. But `srv.Done()`,
`Stopping()`, `AppliedIndex()`, `ApplyWait`, `NextRequestID` and `rf.ReadIndex` load fields of the
`*EtcdServer` or `*raftNode` and need their points-to's and invariants. So 2e cannot prove
`readEnv` at `start`. Then `readNew_init` gives no `readAt`, and every linearizable read
(`Range`, `Txn`, `RangeStream`, `Authenticate`, the corruption checker) loses its source.
*Fix:* move the method triples into the Iris part of `readEnv`, as `□ (…)` (inside `iprop`, a
triple becomes `□ …`), beside the registration fancy update. Or have each triple take a persistent
`envInv` that `readEnv` holds.

### F4. `leaseTimeToLive.spec` (assumed contract): its post is false

The post (`EtcdServer__leaseTimeToLive.lean:46`) is `∀ σ, Reach σ₀ σ → Step … σ σ res` for the
caller's `etcdLb γ σ₀`, and `Reach` includes `σ₀` itself. The member's lessor may be past `σ₀`.
Take a lease granted after `σ₀` and then looked up (`v3_server.go:643`): `leaseAnsAt` needs a table
of `σ₀` naming it, and there is none. The same holds for keys attached after `σ₀`.
*Fix:* the post produces its own bound, `∃ σ₁, etcdLb γ σ₁ ∗ ⌜∀ σ, Reach σ₁ σ → …⌝` (σ₁ the point
the lessor or the leader answered from). `LeaseTimeToLive` still fires at the return, since the
current state is reachable from `σ₁`.
Two smaller gaps in the same contract:
- **Partial key sets.** `le.Keys()` can see a write transaction's attachments half done:
  `storeTxnWrite.put` and `delete` attach or detach one key at a time (`mvcc/kvstore_txn.go:273,285,338`),
  while the apply runs concurrently. The result is a key set no revision had, which W0's
  `∃ r, … storeAt r …` excludes. This is a W0 model mismatch, a candidate `nonissues/` entry
  (found by code reading).
- **Peer replies.** The forwarding path panics on malformed peer replies
  (`issues/etcd-leasehttp-timetolive-nil-{response,header}-panic.md`). The contract should state
  its assumption that the peer URLs are etcd members.

### F5. `Put` and `DeleteRange` (and `raftRequest`/`processInternalRaftRequestOnce` at `.req`) lack the validation premise

The server applies what it is given. Only the gRPC layer checks `key ≠ []`, `ignoreValue` with a
value, and `ignoreLease` with a lease (`checkPutRequest`/`checkDeleteRequest`, `v3rpc/key.go:182-199`;
no other `ErrEmptyKey`/`ErrValueProvided`/`ErrLeaseProvided` in `server/`). W0 answers those
requests with the error and leaves the state alone (`kvStep`'s `p.invalid`, `d.key = []`):
- a put of the empty key is applied (it writes `""`) and answers `ok`;
- an `IgnoreValue` put with a value is applied, ignoring the value;
- an empty-key delete answers `ok` with `Deleted 0`.

No AU allows those commits, and outcome 1's reply contradicts the answer fired. `Range` has the
premise `rm.key ≠ [] ∧ rm.validSort` for exactly this reason, and `Txn` has `txnChecked`.
*Fix:* `Put`: `⌜p.invalid = none⌝`; `DeleteRange`: `⌜d.key ≠ []⌝`. At the internal level, widen
`IrrBody.depthOk` to an `IrrBody.wf` that includes them. The internal requesters never build such
requests, and 2a establishes the premises after its checks.

### F6. `raftRequest`/`processInternalRaftRequestOnce` never give back `irrOwn`, so the writers' `B` has no source

`Put`, `DeleteRange`, a write `Txn`, `LeaseGrant`, `LeaseRevoke`, `Alarm` and the auth methods
wrap the caller's request message in `&pb.InternalRaftRequest{X: r}`. `raftRequest` consumes
`irrOwn r ir`, the owned message tree with `r` inside, and returns no ownership of it. Yet these
specs give back `putReqOwn r dq p` (and the others), at the caller's fraction `dq`. In Go nothing
keeps the struct after the return (only the marshalled bytes are proposed).
*Fix (mechanical):* return `irrOwn' r ir` (the header now set) in both posts, and add a 3h law to
take the inner request back out.

### F7. `AuthInfoFromCtx.spec` and `reqPrin` assume the context names one principal; the code picks one by the auth flag

`EtcdServer.AuthInfoFromCtx` (`v3_server.go:1206-1216`) returns the token's user when auth is on
(`auth/store.go:1072-1100`). When auth is off, the store returns `nil` and the server falls back to
the TLS certificate's common name (`v3_server.go:1214`) when `ClientCertAuthEnabled` is set. Take a
context with a valid JWT for `A` and a certificate for `B`: the call gives `A` with auth on and `B`
with auth off. The post's `⌜who = some u⌝` (`EtcdServer__AuthInfoFromCtx.lean:49`) cannot hold of
one persistent `reqPrin ctx who` both ways. (A JWT outlives `AuthDisable`; simple tokens do not.)

It matters for writes. `processInternalRaftRequestOnce` writes `B` into the header while auth is
off (`v3_server.go:1078`). If `AuthEnable`, which keeps the revision, commits before the entry, the
apply checks `B`'s permissions (`isOpPermitted`, `auth/store.go:862-901`). The caller's update is
for `A` (`srvStep A`), so the commit fires an answer `Step A` may not allow. The race disjunct
covers reads only.

This is a candidate Go quirk, of the same family as `nonissues/etcd-doserialize-auth-enable-race.md`:
a write authorized as the certificate's user, not the token's, during `AuthEnable`. Found by code
reading; no file written.
*Fix options:*
- the realization of `reqPrin` requires that a token and a certificate, when both present, name
  the same user (2a's `mdPrin` cannot establish this from the wire);
- a "principal at the auth flag" pair `reqPrin ctx (tokUser, tlsUser)`, with the write race added
  to `srvStep` for `who ∈ {tok, tls}`;
- a fork fix: no TLS fallback while auth is off.

The same ambiguity sits in `doSerialize.spec`'s `chk` premise (`who = some u`).

### F8. Four snippets cannot be proved from the specs

- **`read.go` `ReqReadErrIndef`.** `Read.readErr` is `opaque … : Prop` (`read/Api.lean:114`), with
  no law listing its values, so the `errors.Is` chain cannot exclude the `panic`. Make `readErr` a
  transparent definition over the named values, or add `readErr_cases`.
- **`kv.go` `ReqRefusalNotApplied`.** Nothing turns `errors.Is(err, srverrors.ErrTooManyRequests)`,
  or the other three, into `srvErrOf err .tooManyRequests`: `srvErrOf` is opaque with laws only
  `ne_nil` and `fun`. So outcome 3 (an unmapped error, possibly still applied) cannot be excluded,
  and the later range may see the key. Add introduction laws for the server's sentinel values
  (`srvErrOf (srvErrVal e) e`, 2a's map) and say `errors.Is` is equality on them.
- **`kv.go` `ReqTxnCAS`, `ReqTxnReadOnly`.** `Txn.spec` needs `txnChecked t`, which is opaque and
  introduced only by 2a's `checkTxnRequest` law. The snippets build literal transactions and call
  the server directly. Call `checkTxnRequest` in the snippets, or add an introduction law for
  simple transactions.
- **`wait/notify.go` `ReqNotifyAfterReceive`.** `notifyChan_recv` yields only `notifyLb γ (k+1)`,
  and `Notify` takes no client resource. A client cannot tie the count to its own `notified`
  counter (it has no authority or token over the count), so `notified ≥ 1` does not follow. Either
  give `NewNotifier` a client predicate `P k` that `Notify` must supply for `k+1` (the same HoCAP
  form as `wait`), or drop the snippet: no user relies on more than the read loop's retries.

## Second tier

1. **The raft namespace must be inside `etcdN`, and nothing says so.** The registry and
   `histPropose` (`ApiApply.lean:438-448`) fire the callers' updates (mask `⊤ \ ↑etcdN`) from
   inside raft's proposal and read updates (mask `⊤ \ ↑γ.raft.ns`). That needs
   `↑γ.raft.ns ⊆ ↑etcdN`, with the history invariant in a disjoint sub-namespace. Neither 2d's
   `Names` nor 2e's allocation states it (grep finds no `raft.ns`). Add it as a fact of `Names`.
2. **Duplicate commits: firing an entry's update only at its first commit is unsound.**
   `req/…etcdserver.md` item 4 (and the batch report's open question) offer "`dup = false`, or fire
   only an entry's first committed occurrence". The apply applies every occurrence; it does not
   dedupe by id. A second commit of a put would change the state with no update to cover it. Keep
   only `dup = false` (2f's rafthttp supports it).
3. **`idutil` has no prefix for members added later.** `idSpace_alloc` is for the initial members
   only, and no law adds a prefix. A member joining after `MemberAdd` (2e's `memberStart_join`)
   cannot get the `idPrefix` its generator needs. Add an allocation authority with an add law
   (fresh, non-zero, distinct prefix). Also, the header's restart condition ("within the
   millisecond, or the clock back") is narrower than the real one: more than `256` ids per
   millisecond since the previous run's start, as `nonissues/etcd-request-id-restart-reuse.md`
   says. Mark `Generator.Next.spec` itself as an assumed contract: it is false across runs.
4. **The race disjunct holds at every auth-enabled state.** A relation over states cannot say
   more, as above. So the client contract for reads is weaker for every read, not only during
   `AuthEnable` (known, decision 1). Only the fork fix recovers K4.
5. **`Alarm` (assumed contract).** For an activation, `irrReply` says `True`, so `Alarm`'s
   `resp.(*pb.AlarmResponse)` is safe only through 3a's applier, which answers
   `&pb.AlarmResponse{}` for `ACTIVATE` too. Keep the `req/` request; F6 applies to it as well.
6. **`Txn` read-only error path (uncertain, probably unreachable).** `txn.Txn` returns
   `txnResp, trace, err` with both set when `executeTxn` fails (`txn/txn.go:78,101`), while
   `srvReply` for `.err` says `resp = null`. The revision errors are checked by `checkTxn` under
   the same read transaction, which holds `s.mu.RLock` against compaction (`mvcc/kvstore_txn.go:46-63`),
   so I found no reachable error.
7. **Snippet text.**
   - `ReqSerializableRange`'s "Assumes" mentions a `maxRev` the code does not use.
   - The KV snippets do not state `len(k) > 0`, which `Range`'s premise needs. It follows from
     "present" only where the snippet says present.
8. **Compact's docstring** says "returns only after the compaction is done and committed"; the post
   (`SrvCallTriple`) says nothing of it. Either move it to the Margin or state it.

## Snippets: the proofs I sketched (those not listed in F8)

- **`ReqPutThenRange`.** `Put.spec` (outcome 1 `ok`, `Q` = `etcdLb` of the commit's state via
  `etcdState_lb`), then `Range.spec`. The ticket's state is after the registration, which is after
  `Put` returned. The key is owned and attached to no lease, so it holds `v`; `putReply`'s header
  revision is the mod revision; the revision is monotone (`etcdLb_ord`). Provable once F5 and F6 are
  fixed, assuming `k ≠ []`.
- **`ReqDeleteThenRange`**, **`ReqTxnCAS`** (modulo F8), **`ReqTxnReadOnly`** (modulo F8),
  **`ReqCompactorCompact`** (`compactRespOwn` must expose a header; the code makes one), and
  **`ReqUserAddGet`**, **`ReqAuthStatus`** (both go through raft, `etcdLb_ord`): provable.
- **`ReqGrantThenRevoke`**: `leaseStep` gives `id' ≠ 0`, `ttl' ≥ ttl`. **`ReqTimeToLive`**: `id' = id`
  by `leaseAnsAt`, but F4 makes its callee's spec false today. **`ReqLeases`**: `Nodup`.
  **`ReqKeepAlive`**, **`ReqExpiryRevoke`** (the update derived from `envUpd` aborts the inner update
  and commits the outer one with `σ' = σ` on every non-revoking answer): provable.
- **`ReqAuthenticate`**: blocked by F1. **`ReqReadAfterWrite`**: plausible through 2e's
  `EtcdServer.LinearizableReadNotify` and a 3e law relating `Rev()` to `srvApplied`/`histAt`.
  Uncertain: 2e's spec of `interface.go` and that 3e law are not written yet.
- **`ReqRegisterTrigger`**, **`ReqGiveUp`**, **`ReqWaitTime`** (`P d` a persistent lower bound of
  `applied`; `closec` for the passed deadline), **`ReqIdsDistinct`** (`idFresh_excl`,
  `idFresh_ne_zero`, given the snippet's `idPrefix`), **`ReqNotifyConcurrent`**: provable.

## Answers to the brief's questions

- **(a) Linearizability.**
  - A write fires once, at its entry's commit, inside raft's proposal update (`histPropose`, the
    proposing member's `mc`). This needs `dup = false` (second tier 2) and the namespace fact
    (second tier 1). Members configured differently can still compute different answers
    (`nonissues/etcd-lease-ttl-differs-across-members.md`); that is 2d's and W0's concern.
  - A linearizable read fires at a point at least the read index. The registry's "fire every
    answer" works where the answer set is finite: ranges, read-only transactions (ties only
    permute a finite list) and the serializable views. It fails for `.authenticate` (F1a).
  - Serializable reads are fine.
  - The three outcomes are true on every path of `processInternalRaftRequestOnce` and `Range`;
    `RangeStream` (F2) and `Authenticate` (F1b) are the exceptions.
- **(b)** The disjuncts are exactly the code's (above). The missing one is the write-side
  principal race (F7).
- **(c)** The wait registry is sound with id reuse excluded per run. Freshness across runs is not
  true of the time-seeded generator in general: it fails when the previous run issued more than
  `256` ids per millisecond on average since its start, or the clock went back. This is recorded
  (`nonissues/etcd-request-id-restart-reuse.md`), but the API header understates it.
- **(d)** Persistence is needed, since `CheckPassword` reads a past point. Today nothing supplies
  it (F1c), and it does not suffice without a token-free answer (F1a) and a modelled token apply
  (F1b).
- **(e) Premises.**
  - `Range` and `RangeStream`: `key ≠ []` and `validSort` are needed, since the server does not
    check them. `RangeStream` also needs the default ordering and no filters (F2b).
  - `Txn`: `txnChecked` and the depth bound are needed: the apply's sequential semantics, and
    `issues/etcd-txn-nested-depth-apply-panic.md`.
  - `Compact`: `rev ≠ 0` is needed. `mvcc` starts at `compactMainRev = -1`, so `Compact(0)`
    succeeds where W0 answers `ErrCompacted`. 2a still has to establish it for raw wire clients.
  - `Put` and `DeleteRange`: missing (F5).
- **(f) Assumed contracts.**
  - `waitAppliedIndex`, `waitLeader`, `Watchable`: true.
  - `Alarm`: true, but 3a's applier must answer `*AlarmResponse` for an activation.
  - `RangeStream`: false (F2). `leaseTimeToLive`: false (F4).
- **(g)** See above; four snippets are unprovable (F8).

## Ranking by need of revision

1. `Authenticate` (F1), with the read registry's statement in `req/` and W0's `authStep`.
2. `RangeStream` (F2), with a Go-level fix on the fork.
3. `read/Api.lean` `readEnv` (F3): every linearizable read hangs on it.
4. `leaseTimeToLive` (F4).
5. `Put`/`DeleteRange`/`raftRequest`/`processInternalRaftRequestOnce` (F5, F6).
6. `AuthInfoFromCtx`/`reqPrin`/`doSerialize` (F7).
7. Snippets and laws (F8): `readErr`, `srvErrOf` introduction, `txnChecked` introduction, `notify`.
8. `idutil` (second tier 3), `Compact`, `Alarm`, the rest of the second tier.
9. `wait` (sound as is).

## Verdict

Not done: eight first-tier findings. F1 (`Authenticate`) and F7 (the principal) need a design
decision with W0, 2a or the user. F2 also needs a fork fix: `RangeStream`'s post-send revision
check is a candidate Go bug, not yet recorded in `issues/` or `nonissues/`. The other first-tier
findings (F3 to F6, F8) are local restatements. The overall design holds up: the three-outcome call
shape, the registry for reads, the generic wait, id and notify APIs, and the read loop over R1. A
second round is needed.
