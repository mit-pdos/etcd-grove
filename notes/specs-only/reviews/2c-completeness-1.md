# Batch 2c, completeness review, round 1

Reviewer: completeness (users), independent of the author. Commit under review: `b5cecfd608`
(the 2c draft). Read: `ApiReq.lean`, every `EtcdServer__*.lean` of 2c, `read/`, `pkg/v3/{wait,
idutil,notify}/`, the snippets `examples/specreq/{etcdserverreq,wait}/`, the `## from 2a` /
`## from 2b` / `## from 1c` / `## from 1d` sections of `req/go_etcd_io_etcd_server_v3_etcdserver.md`,
and 2a's and 2b's consuming specs (`v3rpc/Api.lean`, `ApiWatch.lean`, `togRPCError.lean`,
`kvServer__*.lean`, `LeaseServer__*.lean`). I read `batch-2c.md` only after forming the findings
below; where the author's report answers a finding, I say so.

Go paths below are relative to `.lake/src/server/` (the pinned fork `a4d2bb17`).

## The users, by pattern

| # | Pattern | Call sites (one example each) | What the caller relies on |
|---|---|---|---|
| U1 | gRPC KV handlers | `etcdserver/api/v3rpc/key.go:53,95,104,130,144` | the reply (non-nil `Header`, written by `hdr.fill`), or an error passed to `togRPCError` (ctx error / mapped / unmapped with a message) |
| U2 | gRPC lease handlers | `api/v3rpc/lease.go:45,54,63,79,136` | as U1; **`errors.Is(err, lease.ErrLeaseNotFound)`** turned into a reply (`TTL: -1`, `lease.go:64-73`) or `ttl = 0` (`lease.go:128-131`) |
| U3 | gRPC auth handlers, `AuthAdmin` | `api/v3rpc/auth.go:36-60,183,196` | as U1; `AuthInfoFromCtx`'s `AuthInfo` passed to `IsAdminPermitted` |
| U4 | Maintenance `Alarm`, quota alarmer | `api/v3rpc/maintenance.go:259`, `quota.go:48` | GET/DEACTIVATE as U1 (a nil `Header` tolerated); ACTIVATE with the client's ctx, result ignored |
| U5 | in-process client (v3election, v3lock through `v3client.New`) | `api/v3client/v3client.go:33-50` | goes through the U1-U3 handlers with a context *derived* from the outer RPC's incoming context |
| U6 | compactors | `api/v3compactor/periodic.go:142`, `revision.go:92` | `Compact(pc.ctx, rev)` with `pc.ctx = WithCancel(Background())`, `rev ≥ 1`; `err == nil \|\| errors.Is(err, mvcc.ErrCompacted)` only for logging |
| U7 | lessor expiry | `etcdserver/server.go:881-882` | `LeaseRevoke(authStore.WithRoot(s.ctx), …)`, reply ignored |
| U8 | internal `raftRequest`s | `server.go:402` (checkpoint), `:1848` (publish: `err == nil` closes `readych`), `:2025`, `corrupt.go:441` (alarms, `s.ctx`), `:2344`, `adapters.go:50,56` | no update; `err == nil` / `errors.Is(err, ErrStopped)`; errors logged |
| U9 | health checks | `api/etcdhttp/health.go:224,435` | **`Range` with an empty key** (`KeysOnly, Limit: 1`), `WithRoot` ctx, `err != nil` and `%s` of it |
| U10 | linearizable-read barrier | `server.go:688,924,1695`, `interface.go:47` (`corrupt.go:187`) | `nil` ⇒ the member has applied what was committed at the call |
| U11 | watch server (2b) | `api/v3rpc/watch.go` (`NewWatchServer`, `isWatchPermitted`) | `s.Watchable()` delivers the cluster's history; `AuthInfoFromCtx` from 2b's `srvCtxPrin` and `watchMemberAt` |
| U12 | wait registry | `v3_server.go:1107-1129`, `server.go:1781-1811` (`configure`, `lg.Panic` on a nil value at `:1793`), `server.go:2007,2026` (apply's `Trigger`), **`apply/apply.go:40`** (`IsRegistered`) | register-before-propose, one value per id, non-nil value of the right type; `IsRegistered == false` ⇒ skip the result |
| U13 | applied-index waiters | `interface.go:23`, `server.go:353,630,985` | the channel closes only once the index is applied |
| U14 | id generator | `server.go:327`, `v3_server.go:438,1068`, `server.go:1781`, `interface.go:35` | distinct, non-zero ids across members and runs |
| U15 | notifiers | `server.go:786,1985,2241,2265`, `membership/cluster.go:620`, `read/read.go` | a receive completes only after a later `Notify` |

No direct server call from `cache/`, the gRPC proxy (it wraps handlers or clients), the client, or
this repository's examples (`examples/etcd/*` use the client over `embed`).

## First tier

### F1. No error a server spec returns can be passed to `togRPCError` (every handler, U1-U4)

`togRPCError.spec` (`Spec/.../v3rpc/togRPCError.lean:36-38`) takes `context.isCtxErr err ∨
((isCtxErr err -∗ False) ∗ ((∃ e, ⌜srvErrOf err e⌝) ∨ (∃ m, errMsg err m ∗ ⌜∀ e, ¬ srvErrOf err
e⌝)))`. The code needs this. It tests `errors.Is` against the context errors, hashes `err` as a map
key, and calls `err.Error()` (`api/v3rpc/util.go`, `togRPCError`). What 2c's posts give:

- outcome 1, `srvReply`'s `.err e`: `⌜srvErrOf err e⌝` only. Nothing says the error is not a
  context error. `srvErrOf` is opaque and pure, and no law gives `srvErrOf err e ⊢ (isCtxErr err -∗
  False)`. `isCtxErr` is a resource (Perennial's `context/Base.lean`), so the handler cannot case
  split on it.
- outcomes 2 and 3: `⌜srvUnfired err⌝` / `⌜srvIndef err⌝`, pure. These include raw context errors
  (`s.r.Propose(cctx, data)` returns `ctx.Err()`, `v3_server.go:1114` with `raft/node.go:520-546`;
  `LinearizableReadNotify`'s context case) and unmapped errors (`lease.ErrNotPrimary`, raft's
  `ErrStopped`, bcrypt's, `proto.Marshal`'s). There is no `isCtxErr`, no `errMsg`, and no
  comparability.

So `kvServer.*`, `LeaseServer.*`, `AuthServer.*` and `maintenanceServer.Alarm` cannot establish
`togRPCError`'s pre on any error path. 2a asked for this (`## from 2a`, item 3). `batch-2c.md`'s
answer 3 ("Done … stated over 2a's `Grpc.errMsg`") does not close it: the fact has to come out of
2c's posts, because only 2c knows where the error values come from. Two snippets depend on the same
missing fact and are unprovable as written:
- `ReqReadErrIndef` (`read.go:40`) panics unless `errors.Is` matches one of six concrete values,
  but `Read.readErr` is opaque with no law naming them.
- `ReqRefusalNotApplied` (`kv.go`, last function) needs "`errors.Is(err, ErrTooManyRequests)` ⇒
  not outcome 3", which needs `srvErrOf` tied to the values.

**Fix.** Add a resource to `ApiReq.lean`, `srvErrShape err := context.isCtxErr err ∨ ((isCtxErr err
-∗ False) ∗ ((∃ e, ⌜srvErrOf err e⌝) ∨ (∃ m, Grpc.errMsg err m ∗ ⌜∀ e, ¬ srvErrOf err e⌝)))`.
Conjoin it to every error disjunct of `SrvCallTriple`, `srvReply`, `LeaseRenew.spec`,
`RangeStream.spec`, `Alarm.spec`, `raftRequest.spec` and `processInternalRaftRequestOnce.spec`.
Give `Read.LinearizableReadNotify.spec` the same for `readErr`. If importing `Grpc.errMsg` into 2c
is the obstacle, define the shape in 2a's module and have 2c's posts produce its components:
`isCtxErr`, a law `srvErrOf_notCtx`, and an `errMsg`-like `srvErrMsg` of 2c's that 2a maps.

### F2. `srvErrOf` has no law tying it to the Go error values (U2, U6, snippets)

The lease handlers branch on `errors.Is(err, lease.ErrLeaseNotFound)`:
- `LeaseServer.LeaseTimeToLive` (`api/v3rpc/lease.go:64-73`) answers `TTL: -1` (2a's `ansOutcome`
  needs `Q` with `.err .leaseNotFound`);
- `leaseKeepAlive` (`lease.go:128-131`) answers `ttl = 0`.

To prove these, the handler needs `srvErrOf err .leaseNotFound` ⇒ `errors.Is` is true, and every
other outcome (another `e`, outcome 2, outcome 3) ⇒ it is false. Otherwise it sends a success reply
without `Q`. With `srvErrOf` opaque and no law, neither direction is provable. Same for the
compactors' `errors.Is(err, mvcc.ErrCompacted)` (harmless there: logging only) and the snippets in
F1.

**Fix.** A law per mapped value, or one general law: `srvErrOf err e ↔ err = srvErrVal e` for a
function `srvErrVal : EtcdErr → GoInterface` fixed by the error packages' initialization (a law
`srvErrVal_init` over `isPkgInit` of `etcdserver/errors`, `lease`, `mvcc`, `auth`). Then
`srvUnfired`/`srvIndef` errors that are not `srvErrVal e` need "not `errors.Is` any mapped value"
(no wrapping), part of F1's shape.

### F3. `reqPrin` has no introduction law: no caller can establish it (every user)

`reqPrin ctx who` is in the pre of every request-path spec. `ApiReq.lean` states only
`reqPrin_persistent`, and nothing in `Spec/` introduces it. `grep -rn reqPrin Spec` finds no law
outside `ApiReq.lean:272-274`. The callers' contexts:

- U1-U4: grpc's incoming context. 2a asks for `reqPrin_of_md` (`## from 2a`, item 2). 2c answers
  that it belongs to 2a or 3d (import cycle, `batch-2c.md` answer 2) and asks 2a for `srvCtxPrin ⊢
  reqPrin` (2c's `req/…api_v3rpc.md`, item 2). The two requests point at each other, and nobody
  states it.
- U5: a context derived from the outer RPC's (`WithCancel`, `WithValue`, `WithTimeout`, the
  client's outgoing-metadata wrappers: `WithRequireLeader`). This needs preservation laws (the
  incoming metadata survives derivation).
- U6, U8: `context.WithCancel(Background())`, `s.ctx`, `WithTimeout(s.ctx, …)`. This needs
  `reqPrin ctx none` for a context with no incoming metadata.
- U7, U9: `authStore.WithRoot(ctx)`, whose principal depends on the auth mode at the call
  (`auth/store.go:1175-1178` returns `ctx` unchanged when auth is off). So the law is `∃ who ∈
  {none, some root}`, not `some root` (the `ReqExpiryRevoke` header says root).

**Fix.** State the laws as obligations in `ApiReq.lean` (they are about 2c's predicate; 3d proves
them through the realization):
- `reqPrin_noMeta` (from `Context.ctxNoMeta` or Perennial's `Background`/`WithCancel` specs);
- `reqPrin_child` (`WithCancel`/`WithValue`/`WithTimeout` children keep it);
- `reqPrin_withRoot` (the mode-dependent disjunction);
- the bridge to 2b's `srvCtxPrin` (or one predicate).

`reqPrin_of_md` can live in 2a's `Api.lean` as 2a's obligation, but one of the two batches has to
write it. Put it in `batches.md`'s open list if neither will.

### F4. `Authenticate.spec` takes a persistent update that its one caller does not have (U3)

`EtcdServer.Authenticate.spec` instantiates `SrvCallTriple … (.authenticate name pw) true …`
(`EtcdServer__Authenticate.lean`). The handler `AuthServer.Authenticate` (`api/v3rpc/auth.go:60`)
holds the contract's `callAU γ who rq rep Q` with `rep` the client's (`etcdUnary`,
`v3rpc/Api.lean:185`, forces `rep` only for `Req.isRead`, which `.authenticate` is not,
`Model.lean:767-770`). Every client sends `reqRetryRep (.authenticate ..) = false`
(`client/v3/ApiClient.lean:170-174`). So the pre is unestablishable at the only call site, and K4's
`examples/etcd/auth` token refresh goes through it. The author records this (decision 2, `req/…
api_v3.md`). It stays first-tier until W0 or the user decides. Options: W0 makes `.authenticate`
persistent at the client; or the spec fires the one-shot update at the final `Revision()` read,
which needs the cluster's auth state to be unchanged since `kp`. That holds only if the registry
gives it, so this option probably fails.

### F5. `Range`'s `rm.key ≠ []` excludes the health checks (U9)

`etcdhttp/health.go:224` (`checkAPI`) and `:435` (`readCheck`) call `srv.Range(ctx,
&pb.RangeRequest{KeysOnly: true, Limit: 1, Serializable: …})` with no key. They are etcd's
`/health` and `/livez`/`/readyz` probes, run on every member. The code does not need the premise:
`txn.Range` reads the single key `""` (`txn/range.go:47-71`) and returns an empty answer. The premise
exists only because W0's `kvStep` answers an empty key with the gRPC layer's `ErrEmptyKey`, which
the server does not compute (`EtcdServer__Range.lean`, Changes). The callers use only `err != nil`
and the error's text.

**Fix.** Drop the premise. Add a server-level case to `srvStep`: `rq = .range r ∧ r.key = [] ∧ σ' =
σ ∧ ∃ rev, res = .ok (.range rev [])` or the permission refusal, mirroring the race disjunct. Or
give `Range.spec` a second precondition shape for `key = []` taking no update (W0's `idUpd`-like),
as a case split on the input, not a disjunction of specs. The health checks also need F3's
`reqPrin_withRoot`.

### F6. `Compact`'s `rev ≠ 0` has no source at the gRPC handler (U1)

`kvServer.Compact` (`api/v3rpc/key.go:144`) passes the client's revision as decoded. Nothing in 2a's
`etcdUnary` (`v3rpc/Api.lean:183-190`) or `reqModels` excludes `.compact 0 _`, so a gRPC client can
send revision `0` and the handler cannot discharge `⌜rev ≠ W64 0⌝`. The premise is needed: at a
never-compacted store `compactMainRev = -1`, so a compaction at `0` runs, while W0's `kvStep` says
`ErrCompacted` (`Model.lean:933`; `issues/etcd-restore-scheduled-compact-zero.md`). The compactors
(U6) meet it (`revision.go:82` skips `rev <= 0`; periodic's `revs` are `Rev()` values ≥ 1).

**Fix.** Choose one:
- put the scope restriction where the request enters: 2a's contract (`reqModels` of
  `/etcdserverpb.KV/Compact` requires revision ≠ 0) or W0's (the client contract already has it,
  `KV.CompactTriple`), recorded as the same scope restriction;
- or make W0's `kvStep` say what the code does at `0` (compaction at `0` when `compacted = 0`).

Today neither 2a's spec nor 2c's names the gap.

### F7. `wait.list.IsRegistered`'s answer is unspecified, but the apply thread relies on it (U12)

`list.IsRegistered.spec`'s Users field says "None in the request path; the server's tests", which
is wrong. `apply.Apply` (`apply/apply.go:40-48`) calls `w.IsRegistered(id)`:
- `false` ⇒ `SkipRangeExecution` for a `Txn`, whose result then lacks the range responses;
- `false` ⇒ no result at all for a `Range`/`AuthUserGet`/`AuthRoleGet`/`AuthStatus` entry.

`applyEntryNormal` then calls `s.w.Trigger(id, ar)` (`server.go:2007`). `Trigger.spec` needs `P id
ar ∨ waitRecv`, and a skipped-range result does not satisfy the server's `P`. With
`IsRegistered`'s post `threadTok` only, 2d's `applyEntryNormal` proof cannot discharge `Trigger`'s
pre on the skip path.

**Fix.** Make the answer meaningful:
- `b = false` gives a persistent `waitGone γw id`: `id` is not registered, and if it ever was, it
  has been triggered;
- or `b = false ∗ waitTokUsed γw id` (the client knows it registered `id`) gives `waitDone γw id`;
- `Trigger.spec` accepts `waitDone γw id` as a third way (no value owed).

The server's invariant knows each own id was registered before its proposal (`waitToks`), which
turns "not registered now" into "done". Add a snippet: register, give up, `IsRegistered == false`,
`Trigger` with a junk value never panics, and a live registration is never reported `false`.

### F8. 2b's needs (U11) are not met

`## from 2b` asks for:
- `s.Watchable()` delivering the cluster's history (item 3);
- `AuthInfoFromCtx` for a context with `srvCtxPrin ctx who` (item 5);
- everything over 2b's handle `watchMemberAt s γ` (`ApiWatch.lean:208,230`).

2c gives:
- `Watchable.spec` over `isServer s γ` returning `srvWatchable s γ w`, opaque and provisional with
  no law (`ApiReq.lean`), so nothing connects it to mvcc's watch predicates or to `etcdLb`;
- `AuthInfoFromCtx.spec` over `isServer` and `reqPrin`.

There is no `watchMemberAt ⊢ isServer` (2e's) and no `srvCtxPrin ⊢ reqPrin` (F3). So
`NewWatchServer.spec` and `serverWatchStream.isWatchPermitted.spec` cannot call 2c's specs.

**Fix.** Laws `srvWatchable_mvcc` (to 3f's watchable-store predicate at the member's applied history
of `γ`) and `srvWatchable_persistent` in `ApiReq.lean` (provisional), plus F3's bridge. Ask 2e for
`watchMemberAt ⊢ isServer` (or have 2b take `isServer`).

### F9. `srvStep ≠ Step`: the handlers' updates cannot be passed on (U1, U2)

These are recorded as the user's decisions (`batch-2c.md` decisions 1, 3; `## from 2a` item 1). For
completeness: until they are closed, `kvServer.Range`, a read-only `kvServer.Txn`,
`kvServer.RangeStream` (the race disjunct) and `LeaseServer.leaseKeepAlive` (the keep-alive
permission disjunct, which W0's `leaseStep` still lacks, `Model.lean`'s `.leaseKeepAlive` case)
cannot supply the update 2c's specs take. Keep them in `batches.md`'s open questions. They are not
new findings.

## Second tier

### F10. `RangeStream.spec`'s error post does not meet 2a's `rsSink_out`, and a candidate code issue

`RangeStream.spec`'s third disjunct allows `fin = false ∧ srvErrOf err .compacted` with `ms = []`
and no `Q`. `V3rpc.rsSink_out.spec` (`v3rpc/Api.lean:346-352`) accepts a compaction error only with
`ms ≠ []`. The code reaches this case:
- the first page succeeded, `done` holds with `resp.More` (client limit ≤ 10);
- `txn.Count(…, r.Revision = headerRev)` (`v3_server.go:255`) fails with `ErrCompacted` because a
  write plus a compaction past `headerRev` came between the two reads;
- the stream then ends with `ErrCompacted` and no chunk sent, for a request at revision `0`.

A client asking for the current revision gets "required revision has been compacted". This is a
code-reading candidate, not reproduced. It is not in `issues/` or `nonissues/`
(`nonissues/etcd-rangestream-negative-revision-unpinned.md` is the neighbouring one). It should be
recorded, as a `nonissues/` entry at least, with a failpoint test as `rangeStream`'s
`beforeRangeStreamChunk` allows.

For the spec: state the case (`ms = [] ∧ compacted` after the first page's success) and have
2a/W0's stream contract admit it, or require `ms ≠ []` and make the case an outcome-3 error. Also:
`RangeStream`'s own `reqPrin` comes from `rs.Context()`, but `rsSink` has no context law and no
send law. 2c says they are 2a's to state (`batch-2c.md` answer 6), and 2a's
`kvServer__RangeStream.lean:13` says `rsSink_of_srvSend` was "asked by 2c". Nobody states them.

### F11. Cited snippets that do not exist; uncovered patterns

The specs cite these snippets, which are absent from `examples/specreq/`:
- `ReqPutTypeAssert` (`Put.spec`);
- `ReqCompactPhysical` (`Compact.spec`);
- `ReqRangeStream` in `etcdserverreq/kv.go` (`RangeStream.spec`; only `v3rpc/kv.go:108` has one,
  through the gRPC client);
- `ReqPrincipal` (`AuthInfoFromCtx.spec`);
- `ReqIdNonZero` (`idutil/Api.lean`; `ReqIdsDistinct` covers it).

Patterns with no snippet:
- the handlers' error classification (F1), and `errors.Is(err, lease.ErrLeaseNotFound)` (F2);
  `ReqKeepAlive`/`ReqTimeToLive` do not test it;
- `Range` with an empty key and a `WithRoot` context (F5);
- the internal no-update requests (U8: `raftRequest` with `.noop`/`.publish`/`.alarmActivate`, and
  the `Alarm` ACTIVATE from the quota alarmer). `raftRequest` is unexported, so this needs a
  `//go:build ignore` file in package `etcdserver`;
- `IsRegistered` (F7);
- the in-process client's derived context (U5);
- `configure`'s use of the same registry with `*confChangeResponse` values (`server.go:1781-1793`,
  a `lg.Panic` on `nil`). Covered in principle by `ReqRegisterTrigger`, but see F13.

### F12. `ReqReadAfterWrite` rests on a spec that does not exist

`EtcdServer.LinearizableReadNotify` (`interface.go:46-48`; also the corruption checker's hasher,
`corrupt.go:187`) has no spec in 2c or 2e (`batch-2c.md` leaves `interface.go` to 2e, item 7 of its
`req/`). The snippet, and U10's `MemberList`/corruption-checker users, need its post in server
terms (`srvApplied s γ`, so that `s.KV().Rev()` is at least an acknowledged write's revision). Until
2e writes it, the snippet is unprovable. Mark it as depending on 2e.

### F13. The wait registry's answer predicate covers only `*apply.Result`

`ApiReq.lean`'s intended realization says `P id x` := `x` is an `*apply.Result` for the entry of
request `id`. The same registry `s.w` carries `*confChangeResponse` for conf-change ids
(`server.go:1955`), and `configure` panics on `nil` (`server.go:1793`) and type-asserts. State `P`
for both kinds of id (a non-nil `*apply.Result` for a normal entry's id, a non-nil
`*confChangeResponse` for a conf change's). `processInternalRaftRequestOnce`'s `x.(*apply2.Result)`
(`v3_server.go:1124`) also needs non-nil, which `applyResult` gives.

### F14. `raftRequest` of `.publish` gives its caller nothing, and takes nothing the invariant needs

`publishV3` closes `readych` on `nil` (`server.go:1849-1852`), and 1c's `memberServes` law (`## from
1c`, item 1) says a published member's client URLs serve `γ`. For the invariant to prove that at the
publication's commit, the commit must carry `servesAt γ u` for each URL. `raftRequest.spec`'s
`.publish` case takes no such resource and returns `True`. Ask 2e whether `memberServes` is proved
some other way (`servesAt` from the bound listener, independent of publication). If it is not, the
`.publish` pre must carry the URLs' `servesAt`.

### F15. `AuthInfoFromCtx`'s nil case is weaker than its docstring

The docstring says nil means `who = none` or auth disabled, but the post is only `⌜err = nil ∧ ai =
null⌝`. Today's callers fire `ErrUserEmpty`, a refusal at any `who`, so nothing breaks. 2b's
`isWatchPermitted`, though, admits a watch on a nil `AuthInfo` only when auth is off at its check.
Either state the docstring's fact or correct the docstring.

### F16. Minor

- `Alarm.spec` for a client's `ACTIVATE` through `maintenanceServer.Alarm` (an administrator may
  send one): W0's `Req` has no client alarm activation. Check that 2a's `reqModels` excludes it, or
  the handler has a client update with no `Req`. Uncertain; I did not trace 3h's `reqModels`.
- `Notifier.Notify.spec` takes `notifyLb γ k₀` only to return `k₀ ≤ k`. Fine, but every caller
  passes `k₀ = 0`. The membership package (`cluster.go:620`) must keep `notifyLb γ 0` beside the
  stored notifier; say so in `notify/Api.lean`'s users.
- `LeaseRevoke`'s users line says principal `root` for the lessor's context; F3 (mode-dependent).

## Establishability and sufficiency at one real call site per pattern

| Call site | Pre establishable? | Post sufficient? |
|---|---|---|
| `kvServer.Range` (`key.go:53`) | `isServer` (2a's `kvServerAt`), `ctxOk`, owned message (3h), `key ≠ [] ∧ validSort` (`checkRangeRequest`): yes. `reqPrin`: **no** (F3). Persistent update over `srvStep`: **no** (F9) | reply: yes (`getReply`'s `hdr = some`, so `fill` is safe). Errors: **no** (F1) |
| `kvServer.Txn` (`key.go:130`) | `txnChecked`, depth: yes, through 2a's `txnCheck_checked` and 2e's `MaxTxnOps ≤ 4999` slot (`ApiBoot.lean:279`). `reqPrin`: no | errors: no (F1) |
| `kvServer.Compact` (`key.go:144`) | `rev ≠ 0`: **no** (F6) | `compactReply` has the response; errors no (F1) |
| `LeaseServer.LeaseTimeToLive` (`lease.go:63`) | as `Range` minus F9 | **no**: `ErrLeaseNotFound` (F2) |
| `leaseKeepAlive` (`lease.go:136`) | update over `srvStep`: no (F9, keep-alive denial) | `ErrLeaseNotFound` → `ttl = 0`: no (F2) |
| `AuthServer.Authenticate` (`auth.go:60`) | persistent update: **no** (F4) | `authReply`'s `tokenUser`: yes |
| `maintenanceServer.Alarm` (`maintenance.go:259`) | `alarmReqOwn` (3h), `reqPrin` no | nil `Header` handled by the handler; errors no (F1) |
| quota alarmer (`quota.go:48`) | no update needed (`fires = false`): yes; `reqPrin` no | ignores: yes |
| compactor (`periodic.go:142`) | `rev ≥ 1`: yes (from `Rev()`, 3e). Update from `envUpd`: yes (`EnvStep.compact` matches `kvStep`'s success; identity otherwise). `reqPrin pc.ctx none`: **no** (F3) | logging only: yes |
| lessor (`server.go:882`) | update from `envUpd` (`leaseExpire`): yes; `reqPrin` of `WithRoot`: no (F3) | ignores: yes |
| `publishV3` (`server.go:1848`) | `.publish`, no update: yes; `reqPrin`: no | `nil` ⇒ published: not given (F14) |
| health `checkAPI` (`health.go:224`) | `key ≠ []`: **no** (F5); `reqPrin`: no | `err != nil` only: yes once the pre holds |
| `processInternalRaftRequestOnce` → `Register`/`Trigger` (`v3_server.go:1107-1129`) | `waitTok` from `idFresh` + `waitToks_take`: yes | `waitRecv_recv` gives `P id x`: yes |
| `apply.Apply` (`apply.go:40`) | `listAt`, `threadTok`: yes | **no** (F7) |
| `configure` (`server.go:1781`) | yes | yes, if `P` covers it (F13) |
| read loop's `ApplyWait` (`read.go:135`), `waitAppliedIndex` (`server.go:630`) | `timeListAt` with the applied-index `P`: yes | `□ P d`: yes |
| `NewGenerator` (`server.go:327`) | `idPrefix` of `uint16(nodeID)` (2e's, from `idSpace_alloc`'s distinct prefixes, a recorded scope premise): yes | `idFresh`: yes |
| notifiers (`server.go:786,1985`; `read.go`) | `notifierAt`, `notifyLb γ 0`: yes | `notifyChan_recv`: yes |
| `Read.LinearizableReadNotify` from `ensureLeadership` (`server.go:924`) | `committedLb rγ l0`: any lower bound, `[]` (uncertain: R1's law for the empty log not checked) | nothing relied on: yes |

## Per target: what is good

- **`ApiReq.lean`**. The three outcomes (`SrvCallTriple`) are the right shape for what the handlers
  do: give back, fire, or lose the update. `IrrBody.fires` handles the update-free internal
  requesters (U4, U6-U8) cleanly. `applyResult` and `irrReply` make the type assertions after
  `raftRequest` provable. The `authOff` race disjunct is honest.
- **Client-facing specs** (`Range`, `Put`, `Txn`, `Compact`, the lease, auth and admin methods) are
  one spec per function over the general state, with no lease, auth or compaction restrictions.
  The persistent/one-shot choice follows `Req.isRead`, as 2a's contract does, except `Authenticate`
  (F4).
- **`read/`**. A small API over R1's vocabulary. `LinearizableReadNotify`'s post, a covering
  committed log plus `A l.length`, is what every barrier user (U10) needs, in raft terms. `readEnv`
  given once is a clean boundary with 2e.
- **`wait/`, `idutil/`, `notify/`**. Generic and small. `waitTok`, `idFresh` and `notifyChan` match
  how their users use them (register-before-propose, GC-wait, deadline waits, epoch notifications),
  and the snippets cover those patterns, except `IsRegistered` (F7).

## Ranking by need of revision

1. **`ApiReq.lean`** (and with it every `EtcdServer__*` spec's error disjuncts): F1, F2, F3, F8.
2. **`pkg/v3/wait`** (`list__IsRegistered`, `list__Trigger`): F7.
3. **`EtcdServer__Range`**: F5. **`EtcdServer__Compact`**: F6, with 2a/W0.
   **`EtcdServer__Authenticate`**: F4, a decision.
4. **`EtcdServer__RangeStream`**: F10. **`EtcdServer__raftRequest`**: F14.
   **`EtcdServer__AuthInfoFromCtx`**: F15. **`EtcdServer__Watchable`**: F8.
5. **Snippets**: F11, F12.
6. **`read/`, `idutil/`, `notify/`**: no change needed beyond F1's error shape for `readErr`, and
   F16's note.

## Verdict

Not complete. The vocabulary leaves three things unstated that every handler and internal requester
needs, and that no batch states today:
- what a returned error is, for `togRPCError` and for `errors.Is` (F1, F2);
- how a caller gets `reqPrin` for the context it actually passes (F3);
- what `IsRegistered == false` means for the apply thread (F7).

Three preconditions cannot be met at a real caller: `Range`'s empty key (F5), `Compact`'s `rev ≠ 0`
at the gRPC handler (F6), and `Authenticate`'s persistent update (F4, a recorded decision). 2b's
bridge (F8) is missing. A second round is needed after the repairs.
