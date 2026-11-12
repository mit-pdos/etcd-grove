# Batch 1c, provability review, round 1

Reviewer: provability (soundness, snippets), independent of the author. Read: `ApiClient.lean`,
`ApiLease.lean`, the specs of `lessor.*`, `keepAlive.close`, `NewLease*`, `retry*Client.*`,
`authClient.*`, `cluster.*`, `maintenance.*`, `New`, `newClient`, `NewFromURL`, the `Client.*` specs
(dial chain, interceptors, token, `Sync`/`autoSync`, `Close`, `Endpoints`, `SetEndpoints`),
`isSafeRetry*`, `waitRetryBackoff`, `kubernetes/`, `credentials/`, `client/pkg/v3/{verify,types}`;
the snippets `examples/specreq/{clientv3lease,clientv3client}/`; the `## from 1c` sections of `req/`;
W0's `Api.lean`, `Model.lean`, `top.md`. Go: `.lake/src/client/{lease,client,auth,cluster,
maintenance,retry,retry_interceptor}.go`, `credentials/credentials.go`, the server's
`etcdserver/v3_server.go`, `api/v3rpc/interceptor.go`, `api/v3rpc/rpctypes/error.go`. I read
`batch-1c.md` only after writing the findings below; where the author already knew a point, I say
so.

## What is good

* **The retry interceptor's contract has the right shape.** `AttemptTriple` (fired / fired with a
  definite error / given back unfired / lost) and `uiOk_call` (never a case 3 left over) follow
  `retry_interceptor.go:41-106` closely, including the fork's write-at-most-once fix
  (`:81-85`: a context error on a non-repeatable call is returned, not resent). I checked each
  resend path: token refusals (`:89-100`, `shouldRefreshToken`, `:157-171`) are refusals with no
  effect at the server (`ErrInvalidAuthToken` before the proposal, `v3_server.go:1071-1081`;
  `ErrAuthOldRevision`/`ErrUserEmpty` at apply, no change); the learner refusal comes from the
  server's interceptor before the handler (`v3rpc/interceptor.go:53-54`); the mutable check
  (`retry.go:85-94`) resends only on grpc's "no address/connection available" strings, which
  grpc-go v1.85 never produces (no match in its source), so in practice a non-repeatable call is
  never resent after `Unavailable`. The refusal the interceptor fires itself is a legal `Step`
  (every `errRetryAuth` error and `notSupportedForLearner` is `EtcdErr.refusal`). The refresh's
  failures are covered: `Authenticate`'s definite answers are `authNotEnabled` (handled, `client.go:
  299-301`), `authFailed` and refusals (`Model.lean` `authStep`, `.authenticate`), all refusals.
  There is no refresh recursion: the server skips the token check for `Authenticate`
  (`v3_server.go:1071-1072`), and the proof has no circularity as long as `authAt` is a stored
  bundle (the interceptor uses it as a hypothesis).
* **The repeatable-write finding (question b) is true**, and `reqRetryRep` matches `retry.go`
  exactly (lease grant/revoke/keep-alive/TTL/leases, user/role get and list, member list, alarm,
  range; not `AuthStatus`, not `Authenticate`). An attempt that returned `Unavailable` may well
  have been applied: `ErrGRPCTimeout` ("request timed out", after the proposal) is
  `codes.Unavailable` (`rpctypes/error.go:82`), `isSafeRetryImmutableRPC` resends it
  (`retry.go:54-75`), and the server chooses a fresh lease id per attempt (`v3_server.go:434-439`),
  so a `Grant` can grant two leases. It does not contradict W0's KV specs (the only repeatable KV
  RPC is `Range`, a read) nor K4 (per RPC attempt). The persistent update stays useful: the caller
  gets the last firing's `Q` (the lease id it was answered, live and fresh at that state), the
  invariant can mint a token per granted id inside the update, and orphaned leases have no keys.
* **`kaChan` is right and minimal**: only `recvKeepAlive` sends, only for `TTL > 0`, only on the
  channels registered under the map key it looked up (`lease.go:536-564`), so "about `id`, positive
  TTL" holds whatever the server sends. The close discipline holds: every closer
  (`keepAliveCtxCloser`, `closeRequireLeader`, `recvKeepAlive`, `deadlineLoop`, the receive loop's
  cleanup) removes the channel from the entry under `l.mu` before or as it closes it, so no channel
  is closed twice; `donec`'s close token is the `Once`'s (`Close` or the receive loop).
* `lessor.Close` (idempotent, waits for `donec`), `Client.Close` over `isClient` (every piece
  idempotent), the `verifyOff` premise of auto-sync (`client.go:199` asserts a non-empty list) and
  of `Sync`, `NewLeaseFromLeaseClient`'s exclusion of a `nil` client, and `CheckedCallTriple` for
  `MemberAdd`/`MemberUpdate` (`types.NewURLs` before anything is sent) are all justified by the code.
* **(e) The nil-logger panic is real**: with `c == nil`, `l.lg` stays `nil` (`lease.go:213-216`);
  `recvKeepAliveLoop` calls `l.lg.Warn` on a `resetRecv` error *before* testing
  `canceledByCaller` (`:469-476`), and `sendKeepAliveLoop` on a `Send` error (`:608-611`); zap's
  `(*Logger).Warn` reads `log.core`. Reachable: a lessor made with `nil`, a keep-alive started, then
  the server unreachable (with a `nil` client the call options are `nil`, so no wait-for-ready and
  the stream open fails fast) or `Close` racing the reopen. No etcd caller passes `nil`
  (`v3client.go:37` and the tests' proxy pass a client), so a `nonissues/` entry.

## First-tier findings

### F1. `AttemptTriple`'s indefinite case admits a not-sent error with the update lost (`ApiClient.lean:381-394`)

Case 4 is `indefCall err ∗ unaryArgs …`, and `indefCall err = ∃ k, callErr err k ∗ ⌜k.indefinite⌝`
includes `k = .notSent` (`CallErr.indefinite .notSent = true`, `Api.lean:425-428`). On such an
error the update is gone, yet `isSafeRetry` returns true for `.notSent` whatever the policy
(`isSafeRetry.spec`'s post; code `retry.go:85-94`), so the interceptor resends a non-repeatable call
(`retry_interceptor.go:101-104`, loop) and must pass `callAU` to the next `AttemptTriple`, which it no
longer has. `uiOk_call` is unprovable from `AttemptTriple` as stated, and the at-most-once argument
has a hole exactly where it claims "resent only after an attempt that applied nothing".
Fix: case 4 is `∃ k, callErr err k ∗ ⌜k.indefinite = true ∧ k ≠ .notSent⌝` (with `callErr_agree`,
the interceptor then knows a `.notSent` error came with the update back), in `AttemptTriple` and in
the `req/google_golang_org_grpc.md` item 1 text.

### F2. `uiOk_call` says nothing of the connection `cc`, which the interceptor dereferences (`ApiClient.lean:406-418`)

With a non-zero limit (always: `withMax(defaultUnaryMaxRetries)`, `client.go:247-270`) the loop
evaluates `cc.Target()` before every attempt and after every failure (`retry_interceptor.go:58-63,
68-75, 92-96`; Go evaluates the `zap.String` arguments whatever the log level). `uiOk_call`
quantifies over every `cc : Loc` with no premise, so at `cc = null` it claims a call that panics;
`□ Pinv` is opaque to the interceptor's proof and cannot supply it. Fix: a grpc slot
(`grpcConnAt cc`, persistent; 2a), in `uiOk_call`'s pre (and `AttemptTriple`'s, where grpc's
`Invoke` passes the same `cc`). Same for the peer holder (F-S2 below).

### F3. `siOk_call` has no premise on the call options (`ApiClient.lean:423-436`)

The stream interceptor runs `filterCallOptions(opts)` (reads the slice and type-asserts each
element) and `reuseOrNewWithCallOptions` (`retry_interceptor.go:128-129`); with a per-call
`withMax(n > 0)` it reads `desc.ClientStreams` and returns either an `Unimplemented` error or a
`serverStreamingRetryingStream` (`:134-151`), which is not what `Φ` describes. `siOk_call`
quantifies over every `opts` with no ownership and no constraint, so it is false (and its proof
cannot read the slice). The limit-`0` argument the header gives rests on `callOptsOk_append`, which
the law never mentions. Fix: add `callOptsOk opts rep` (or grpc's combined-options slot, as
`uiOk_call` has) to `siOk_call`'s pre; `Client.streamClientInterceptor.spec`'s premise on `fs` then
gives the limit `0`.

### F4. The readiness gap makes the interceptor specs unprovable as stated (`Client__unaryClientInterceptor.lean`, `Client__streamClientInterceptor.lean`, `Client__dialSetupOpts.lean`; author's open question 1)

Confirmed, and it is not only `clientConnOk`: `Client.unaryClientInterceptor.spec` produces `uiOk`
from `clientPre` alone, but `uiOk_call`'s refresh path reads `c.Auth` and calls
`c.Auth.Authenticate` (`retry_interceptor.go:90` → `refreshToken` → `client.go:297`), which
`clientPre` does not give and which is `nil` until `client.go:461`; with a user name and password a
refresh through a `nil` `Auth` panics. Separately, `Client.dialSetupOpts.spec` (pre `clientPre`)
calls `streamClientInterceptor`, whose spec takes `clientCore` (`clientCore ⊢ clientPre`, not the
converse): the sketch cites a callee whose pre it cannot meet. I see no realization of `uiOk` that
avoids it (the interceptor's caller holds nothing that excludes the window). Either W0 adopts the
author's `clientReady c` proposal (`req/go_etcd_io_etcd_client_v3.md`, from 1c, item 1: the bundle
introductions `kvHandle_kvAt`, `lessorHandle_leaseAt`, … take it, `uiOk_call`/`siOk_call` take it or
`uiOk`'s realization holds it via an invariant that `newClient` fills), or the fork sets `c.Auth`
before the dial's members are built. Until decided, `uiOk_call`, `siOk_call` and the specs over them
are not provable; this blocks W0's at-most-once too.

### F5. `Client.dial` reads `c.endpoints[0]` without `epMu` and with no emptiness check (Go bug; `Client__dial.lean`, `Client__Dial.lean`, `maintenance__Status.lean`)

`dial` builds the target from `authority(c.endpoints[0])` (`client.go:327`) without the lock that
`SetEndpoints` writes under (`client.go:177-183`). `Client.Dial` (hence every `maintenance.Status`,
`client.go:277-283`, `maintenance.go:117-118, 204-205`) runs it at any time, so:

* with auto-sync on (`cfgOk` allows it), or a user's `SetEndpoints`, `Status` races the write: a Go
  data race, and in GooseLang a racing non-atomic load is stuck, so `Client.dial.spec`/`Dial.spec`
  over a persistent `clientPre` and `Client.SetEndpoints.spec` cannot both be realized;
* with the endpoints empty (`SetEndpoints()` with no argument, which `Client.SetEndpoints.spec`
  admits; or `Sync` with no published voter under `verifyOff`, which `Client.Sync.spec`'s margin
  says it sets "as is"), `c.endpoints[0]` panics (index out of range).

Snippet `clientv3client/lifecycle.go` `ReqEndpoints` (an arbitrary client: auto-sync possible)
is therefore not provable. Fix options: the fork reads under the lock and guards emptiness
(`eps := c.Endpoints(); if len(eps) == 0 { return nil, ErrNoAvailableEndpoints }`), the honest fix;
or a premise that excludes concurrent `SetEndpoints`/auto-sync and empty lists at every `Status`
caller (no caller can establish the first while auto-sync runs). Record it (not in `issues/` or
`nonissues/` yet): a test with `SetEndpoints()` then `Maintenance.Status` panics; the race shows
under `-race` with auto-sync and `Status` in a loop. `checkVersion`'s `Status` calls are safe (before
`go autoSync()`, `client.go:478-485`).

### F6. `cfgPrincipal_user` is false with a client certificate under `--client-cert-auth` (`ApiClient.lean:603-605`)

The law gives the principal `some Username` for any configuration with a user name and password and
no token, TLS included. If auth is off when `New` runs, `getToken` stores the token `""`
(`client.go:299-301`), and the bundle then attaches no metadata (`credentials.go:69-76`). Once auth
is enabled, the server, finding no token, takes the principal from the TLS certificate if it runs
with `--client-cert-auth` (`v3_server.go:1206-1215`): the request is executed as the certificate's
common name, not `Username`, and no `ErrUserEmpty` comes back to trigger a refresh. (Without a
certificate the same request gets `ErrUserEmpty`, a refusal the interceptor refreshes on, so the
law is fine there.) Fix: premise `cfg.TLS' = null ∨ tlsPrincipal γ cfg.TLS' none` (or the
certificate's principal equal to `some Username`). `etcdctl --user … --cert …` is such a
configuration.

### F7. Lease and alarm snippets need integer ranges the model does not give (`clientv3lease/grant.go`, `reads.go`; `clientv3client/maint.go`)

`leaseGrantReply` writes `ID' := W64 id, TTL' := W64 ttl` from `Int`s; `leaseStep` gives only
`id' ≠ 0` and `ttl ≤ ttl'`, no upper bound (`Model.lean:932-939`). So:

* `ReqGrantTTL`: `resp.ID == NoLease` (`W64 id' = 0` at `id' = 2^64`) and `resp.TTL < ttl` (`ttl'`
  wrapping) are not excluded.
* `ReqLeasesNoDup`: `ids.Nodup` is over `Int`; two granted ids `2^64` apart give equal `W64`s.
* `ReqAlarmDisarm`: alarm member ids are `Nat`s; an alarm of member `m + 2^64` survives the disarm
  and lists as `m`.

The code's facts: the server's ids are positive `int64`s (`v3_server.go:436-439`), the granted TTL
is `max(ttl, minLeaseTTL)` (an `int64`), member ids are `uint64`. Fix (W0's model, by `req/`):
`0 < id' < 2^63` for a server-chosen id and `ttl' < 2^63` in `leaseStep`, granted ids within
`int64`, `Alarm.memberId < 2^64` (or `w64`); then each snippet follows from the reply laws.

### F8. `ReqTimeToLiveAbout`'s second panic is reachable in the model (`clientv3lease/reads.go`)

For a known lease `leaseStep`'s `.leaseTimeToLive` answer leaves `ttl` and `gttl` free
(`Model.lean:947-954`), so `TTL = -1, GrantedTTL = 0` with attached keys is a legal answer and the
snippet's "unknown lease with keys" panic is not excluded. The code gives `GrantedTTL = le.TTL() ≥
minLeaseTTL > 0` for a found lease (`v3_server.go:650`), `TTL` may be `-1` (an expired lease not yet
revoked). The author noted the model gap (req to W0, item 6) but wrote a snippet that depends on it.
Fix: `0 < gttl` in the model's found-lease answer (W0), or drop the panic.

### F9. `ReqNewNoEndpoints` is not provable from `New.spec` (`New.lean`, `clientv3client/lifecycle.go`)

`New.spec`'s post allows `err = nil ∗ clientMut c γ who` for an empty endpoint list (nothing in
`cfgOk` or the post distinguishes it), so the snippet's `if err == nil || cli != nil { panic }` is
not discharged, although the code returns `ErrNoAvailableEndpoints` (`client.go:87-89`). Fix: a
conjunct `⌜eps = [] → c = null ∧ err ≠ nil⌝` in the post (with `eps` the configured list, bound in
the pre), or a separate case. (The snippet should also state "lg a logger or nil": `cfgOk` needs
`isLogger lg` when it is not `nil`.)

## Second-tier findings

* **S1. `kaRecvAt_recv` gives an arbitrary id** (`ApiLease.lean`), but `lessor.keepAliveOnce.spec`
  promises a response about the requested `id`, and its sketch rests on "2a's keep-alive handler
  copies `req.ID`" (`req/..._api_v3rpc.md`, from 1c, item 4), which no stated slot carries. Make
  the stream halves track the ids sent (`kaRecvAt sc q`, `kaSendAt` appending to `q`, `Recv`
  answering about the head), or a law tying them. `ReqKeepAliveOnce` is provable from the spec;
  the spec is not provable from its callees as stated.
* **S2. The peer holder** (`var p peer.Peer`, `grpc.Peer(&p)`, `retry_interceptor.go:46-47`; read
  by `p.String()` at `:71`): grpc writes `p` after the attempt, and `AttemptTriple` neither takes
  nor returns `p ↦ _` (`grpcCallOptsOk` is persistent). Either `AttemptTriple` takes and returns the
  peer holder, or `grpcCallOptsOk`'s realization keeps `p` in an invariant (only if grpc's write is
  one atomic store in the model: uncertain).
* **S3. Documentation of the repeatable writes.** `top.md` §1 ("fired once (a write)") and W0's
  `Api.lean` header overclaim for lease grant/revoke and alarm disarm; ask W0 to say "at most once
  per attempt; a repeatable RPC's update, write or not, persistent". `ApiLease.lean`'s "a lease
  granted by an abandoned attempt … expires" is false under `cfg.leaseExpiry = false` (K2): it lives
  for the run, with no keys.
* **S4. Go findings not filed** (CLAUDE.md asks for them at once; the author noted one as "outside
  my paths"): the nil-logger panic (above, `nonissues/`); the double grant/revoke (documentation:
  `Lease.Grant` may grant a second, orphaned lease, `Revoke` may answer `ErrLeaseNotFound` for a
  lease it revoked; `nonissues/` unless a test reaches it through etcd's server, e.g. a proposal
  timeout); F5's race and index panic (a test is easy: `issues/` candidate); and a liveness bug:
  `KeepAlive` racing `Close` (`lease.go:283-321` vs `:341-346`): if `Close`'s `Once` wins after
  `KeepAlive` registered its entry, the loops never start, the context closer returns at once on
  the closed `donec` (`:353`), and the channel is never closed, contrary to the doc (`:130-131`,
  "closes if … ctx is canceled"). Liveness only (no spec change), `nonissues/`.
* **S5. Small things.** `Maint.methods`' `Status` post: the second disjunct is subsumed by the
  third. `Auth.Triple`, `Cluster.methods`, `Maint.methods` conjoin `ctxPrin ctx who` twice.
  `ApiLease.lean`'s snippet list names `once.go` (it is in `reads.go`). `ReqRefreshAtMostOnce`'s
  reliance is stated as "a panic in the invariant's proof": it checks nothing in Go, so it does not
  drive completeness the way the README asks; say it is a ghost assertion or drop it.

## Snippets (question f)

| Snippet | Provable? | Proof sketch / obstacle |
|---|---|---|
| `ReqGrantTTL` | no (F7) | `Lease.methods` Grant with a persistent update; `leaseGrantReply` gives `W64 id'`, `W64 ttl'` with only `id' ≠ 0`, `ttl ≤ ttl'` |
| `ReqGrantThenPut` | yes | `Q` of the grant's last firing: lease `id` live at `σ₁`; Put (W0) with `WithLease`: `PutReq.check`; Get fires at a state reachable from the put's (`etcdLb_reach`); the owner's invariant (no other writer of `k`) leaves `k` with lease `id` or deleted by a revoke/expiry |
| `ReqTimeToLiveAbout` | no (F8) | first panic: `leaseTTLReply`'s `ID' = W64 (sint.Z id) = id` in both arms; second: model admits `gttl = 0, ttl = -1` with keys |
| `ReqLeasesNoDup` | no (F7) | `Nodup` of `Int`s, not of their `W64`s |
| `ReqKeepAliveOnce` | yes from `KeepAliveOnce.spec` (S1 for the spec itself) | three disjuncts give `r.ID = id`, the TTL sign, `nil` on error |
| `ReqSessionLifecycle` | yes | no `panic`; `kaChan_recv` in the goroutine; `ctxPrin_background` for the revoke; the wait on `donec` is liveness |
| `ReqKeepAliveValues` | yes | `kaChan_recv`: `kaRespAt v id` (read-only, `ID = id`, `0 < TTL`) |
| `ReqNewWrapClose` | yes | `New.spec`: `clientMut` or `(null, err)`; `clientMut_KV` to write `KV` (the wrapper's `kvAt` its own); `clientMut_freeze`; `Client.Close.spec`; Put's post either way |
| `ReqNewNoEndpoints` | no (F9) | |
| `ReqEndpoints` | no (F5) | `Status` races auto-sync's `SetEndpoints` on an arbitrary client |
| `ReqCtxPut` | yes | `Client.Ctx.spec`, `Context.WithCancel` keeps `ctxPrin` (`ctxPrin_child`) |
| `ReqNewFromURL` | yes | |
| `ReqAdminSetUp` | yes | each call non-repeatable (exclusive update, fired at most once); with the owner's exclusive view of auth and auth off, `authStep` excludes each panicked error at the firing state (root absent before `UserAdd`; `UserGrantRole` to the built-in `root` role; role `r` present; root with the root role before `AuthEnable`) |
| `ReqUserClient`, `ReqRefreshAtMostOnce` | yes (no Go panic) | the second's claim is a ghost one (S5); it depends on F1 and F4 |
| `ReqMemberAddThenList` | yes, given 3h's unfold laws | `MemberAdd` exclusive; `MemberList` with no option is `.memberList true` (`l.Perm σ.members`) at a state after the add's; no remover (the invariant) |
| `ReqSync` | yes | `Client.Sync.spec` (post `True`), `verifyOff` assumed |
| `ReqStatus` | yes, given 3h's `statusRespOwn` unfold (but `Status.spec` itself: F5) | |
| `ReqAlarmDisarm` | no (F7) | otherwise: disarm (persistent update, last firing removes the alarm), list at a later state, no `EnvStep.alarm` by assumption |
| `ReqKubeNew`, `ReqKubeCAS`, `ReqKubeList` | yes (sketched, W0's txn and range models) | CAS: Get linearizable, mod revision `0` for an absent key, no other writer, no lease; `txnReply`'s failure branch gives the key's record of revision `p.Revision` |

## Question (c): `KeepAlive`, its goroutines, `Close`

The guarantee (values about `id` with a positive TTL; nothing about liveness) is what the code
gives, and enough for its users (sessions only drain the channel). `KeepAlive` forks without a
thread token, which Perennial's fork rule allows (`wp_fork_tok` hands the forker a token,
`BoundedLang.lean`). `lessor.Close` stops the loops and waits for the receive loop's cleanup
(channels closed under `l.mu` right after `donec`, as the margin says), gives nothing back (the
loops hold nothing a caller gave), and outstanding unary calls are untouched by it; `Client.Close`
then closes the connection, so they fail with an indefinite error. The one gap is S4's race, which
is liveness.

## Question (d): `New`'s configuration

TLS (`tlsCfgOk`, cloned by `NewTransportCredential`), token (`cfgPrincipal_token`: the token is
always sent, so its user is the principal), user/password (F6 for the TLS case), auto-sync (only
with `verifyOff`: needed; F5 for what it does to `Status`), `RejectOldCluster` (`checkVersion`:
`minSupportedVersion`'s panic is unreachable, `version.go:29,51` lists 3.8), `MaxCallSendMsgSize >
MaxCallRecvMsgSize` (an error) are handled. The readiness gap is real (F4).

## Targets ranked by need of revision

1. `ApiClient.lean`'s interceptor contracts (`AttemptTriple`, `uiOk_call`, `siOk_call`) and the
   specs producing them (`Client.unaryClientInterceptor`, `Client.streamClientInterceptor`,
   `Client.dialSetupOpts`): F1, F2, F3, F4, S2.
2. The dial chain and `Status` (`Client.dial`, `Client.Dial`, `maintenance.Status`,
   `Client.SetEndpoints`, `Client.Sync`): F5 (a fork fix is the clean way).
3. `cfgPrincipal_user`: F6.
4. The lease and alarm snippets with their model requests to W0: F7, F8; `ApiLease.lean`'s
   `kaRecvAt` slot: S1.
5. `New.spec`'s post: F9.
6. `lessor.*`, `retry*Client.*`, `authClient.*`, `cluster.*`, `kubernetes/`, `credentials/`,
   `internal/`, `client/pkg/v3/`: sound as far as I checked; S3-S5 only.

## Verdict

Not done. The design (persistent updates exactly for the repeatable RPCs, the attempt/interceptor
split, `kaChan`, `idUpd`) is sound and the repeatable-write finding is correct and consistent with
W0's KV specs and K4. But the at-most-once law is not provable as stated (F1, F2, F4), `siOk_call` is
false (F3), the dial chain has a Go data race and index panic that the specs ignore (F5),
`cfgPrincipal_user` is false with client certificates (F6), and five snippets are not provable
(F7-F9). F1-F3, F6 and F9 are local edits; F7-F8 are requests to W0's model; F4 and F5 need a
decision (W0's `clientReady` or a fork change; a fork fix of `dial`). A second round is warranted.
