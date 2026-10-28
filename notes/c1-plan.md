# Plan: C1, a user client's attempts carry its user's token (spec-first)

Status: phase 0 decided (2026-10-28, the user's: 1 (a), 2 yes, 3 no: the anonymous client is a later stage). Phase 1 drafted
(2026-10-28, "Phase 1: the statements" below); next: the spec-review round (phase 1b), then the
proofs. Not to be merged into `lean` before the proofs: phase 1's `sorry`s sit under `New` and the
retry interceptor, so nearly every client result rests on them meanwhile. The auth plan's item 2
(`notes/decisions.md`, "E3zb of the auth plan", "What is left"; E2b's contract C1), run as a
spec-first stage (`notes/spec-first-plan.md`).

## What `Work` needs (the top-level statement)

`Work(cli, who)` for `u` and `v` runs on a client `newUserClient(who, pw)` built. Each successful
reply of the auth-on member carries the server's fact at the token of some attempt's metadata
(E3zc, `client/v3/ResultsOn.lean`): `∃ md, ⌜clientAttemptMd conn ctx md⌝ ∗ writeGrantOn … (auth.mdTokenOf
md) …` (`rangeAuthed`, `txnAuthOn` for reads). To turn a grant into "`who` was permitted", `Work`
needs that token to be none (no principal: refused with auth on) or one issued to `who`. Drafted:

```lean
/-- C1: the client `cl` was built with the user name `u`: every attempt on its connection, with a
context carrying no outgoing token, carries no token or one issued to `u` at the member's names. -/
def userClient (cl conn : Loc) (γa : auth.AuthNames) (u : GoString) : IProp GF :=
  □ ∀ ctx md, ⌜metadata.mdVals (metadata.outgoingOf ctx) "token" = []⌝ -∗
    attemptMd conn ctx md -∗ userTokOk γa u (auth.mdTokenOf md)
-- userTokOk γa u tok := ⌜tok = none⌝ ∨ ∃ t, ⌜tok = some t⌝ ∗ auth.tokIssued γa t u   (E2f's C1)
```

`newUserClient`'s post (through `clientv3.New` with a user name) gives `userClient cl conn γa
who` with `conn` the client's connection, the one its `*kv` uses (`kvObjAtC api conn`), which
ties `isNewClient`'s two connections (the `*Client` wrappers E3zc deferred).

## The layers (the statements to draft in phase 1)

1. **grpc, the attempt's metadata** (trust boundary, generic). Today `grpcAttemptMd conn ctx md`
   is an opaque pure relation with no facts. In grpc-go an attempt sends the per-RPC credentials'
   metadata (`GetRequestMetadata`, called for each attempt) and then the context's outgoing
   metadata (`http2_client.createHeaderFields`), so the handler's `token` values are the
   credentials' first (to check against grpc v1.84's source in phase 2: no grpc source is in
   `.lake/go-src`). The token is the bundle's at the attempt, a ghost fact (`tokIssued`), so
   the attempt's metadata becomes an Iris fact: `attemptMd conn ctx md := ∃ cm, credsMd conn cm ∗
   ⌜md = mdMerge cm (outgoingOf ctx)⌝`, with `credsMd conn cm` (persistent) "the connection's
   per-RPC credentials returned `cm` to an attempt"; a connection dialed with no credentials has
   `cm = none`, one dialed with `WithPerRPCCredentials(pc)` the `Q cm` of `pc`'s
   `GetRequestMetadata` contract `Q`. The invoker contract (`grpcInvokerOk`) and `attemptPre`
   take `attemptMd` in place of `⌜grpcAttemptMd⌝` (the E3zc stack threads it unchanged).
2. **etcd's credentials** (`client/v3/credentials`, translated, proved). The bundle's token cell
   under its lock with an invariant over its content (`""` or a token `P t`, here
   `tokIssued γa t u`); `UpdateAuthToken(t)` given `P t`; `GetRequestMetadata` returns `none` for
   `""` (Go: `if rc.authToken == "" { return nil, nil }`) or `{"token": [t]}` with `P t`.
3. **`getToken`** (today an axiom saying only `nil` or a client error): proved, from
   `c.Auth.Authenticate(ctx, c.Username, c.Password)`'s reply token (the Auth stub at etcd's
   `Authenticate` spec: the reply's token `tokIssued γa t name`, S5's server side) and
   `UpdateAuthToken`. The retry interceptor's refresh (`refreshToken` on an invalid token) calls
   it again: the bundle's invariant covers every token it ever holds.
4. **`Authenticate` served with auth on**: the handler's spec (`etcdAuthenticateSpec`) from S5's
   `Authenticate`, registered with the Auth methods (`etcd_kv_auth_served_on`).
5. **`clientv3.New` with a user name**: its post `userClient cl conn γa u` at the member's names
   (needs the member's `Authenticate` registration at the endpoint, a premise of `New`).

## Phase 0 decisions (the user's)

1. **Where C1's trust sits.** (a) The faithful chain above: grpc's attempt from the credentials (one
   generic trust-boundary statement), the credentials package proved, `getToken` proved over the
   served `Authenticate`. (b) C1 as a trust-boundary fact of `clientv3.New` with a user name (an
   axiom on its post, `userClient`): cheap, but it states what the server issues as a client-side
   axiom. Recommended: (a).
2. **The refresh path in scope** (the interceptor's `refreshToken` after `ErrInvalidAuthToken` /
   `ErrAuthOldRevision`): recommended yes; it costs nothing beyond (a)'s invariant.
3. **The anonymous client (C2/C4) in the same stage** (decided: no, a later stage): with no credentials, `cm = none` and the
   attempt's token values are the context's (`deliversOutgoing`, E2f's C2/C4, follows from layer
   1). Recommended yes. Not in it: that `reqCtx`'s timeout context carries no outgoing token
   (Perennial's context model does not describe values at other keys), which `Work` needs for the
   anonymous principal; recorded, a `Work` premise for now.

## Phase 1 (after the decisions)

Draft every statement of the layers (specs, the grpc axiom's new form, `New`'s post), the stubs
`sorry`, then the glue: `Work`'s grant-to-permission step for `u` and `v` from `userClient`, and
the E3zc stack threading `attemptMd`; then a fresh spec-review round before any proof.

## Phase 1, in progress (2026-10-28)

**Layer 1 drafted** (uncommitted, callers not yet adjusted): `grpcAttemptMd` a definition over an
opaque `credsYield conn cm` (the credentials' values, then the context's outgoing ones, on every
key grpc does not set itself: grpc adds `:authority`, `user-agent`, ..., so equality on all keys
would be false); the credentials' contract `perRPCCredsOk pc Q` (`GetRequestMetadata`'s map, as
metadata, meets `□ Q`); the dial descriptor `.perRPCCreds pc` names the credentials; and
`grpc.NewClient` takes the credentials' contract and gives `connCredsOk conn pcs Q` (what they
returned to the attempts meets `Q`). Not a free-standing law "every `cm` the credentials yielded
meets `Q`": a `Q` established after some attempt would make it false; at the dial no attempt exists.

**Finding: `getToken` reads `c.Auth`, which is set after the dial** (decided 2026-10-28, the user's: (A)). `newClient` dials (the retry
interceptor installed, its contract `etcdInterceptorOk` fixed then, with `retryClientOk c`), and
only then sets `client.Auth = NewAuth(client)` and calls `getToken`. The interceptor's refresh
path (`refreshToken` on an auth error) calls `getToken`, which calls `c.Auth.Authenticate`: a
`nil` `c.Auth` panics. In Go no call is made between the dial and `client.Auth = ...` (the
constructors in between issue no RPC), so it never happens, but the interceptor's contract is
stated at the dial, before `c.Auth` exists. Today's `getToken` axiom already assumes it away (its
pre is `retryClientOk c`, no `c.Auth`). Proving `getToken` (decision 1 (a)) needs one of:
- **(A) a readiness gate**: the connection's interceptor contract conditioned on a persistent
  `clientReady c` (`c.Auth` set, `↦□`, with the Auth object's facts), minted by `newClient` after
  `client.Auth = NewAuth(client)`; the calls through the client carry it (`isNewClient`'s
  `isEtcdConn`), the constructors before it (`NewKV`, ...) take the ungated form. Faithful; changes
  `isEtcdConn`'s users' statements (about 20 files) or adds a second form of it.
- **(B) `getToken` stays an axiom, restated**: with a user name, the token it stores is one the
  registered `Authenticate` spec's reply gives for `c.Username` (the registration and the bundle's
  invariant are both available before the dial), or `""`; the `c.Auth` ordering stays assumed, as
  today. Client-code trust only (no claim about the server: the server's fact is the registered
  spec's), and `NewAuth`, `authClient.Authenticate`, `retryAuthClient.Authenticate` stay
  untranslated.

**(A)'s design** (phase 1's statements, 2026-10-28):
- `clientReady c` (persistent): `c.Auth ↦□` an `*authClient` over `c`'s connection, its structure
  only (`authObjS`: its `remote` a `*retryAuthClient` on `conn`, its call options), no interceptor
  fact. Minted by `newClient` right after `client.Auth = NewAuth(client)`.
- The dial's post is gated: `isEtcdConnG c conn eps := ∃ ic, grpcConn conn eps [ic] [] ∗
  □ (clientReady c -∗ etcdInterceptorOk ic ∗ etcdInterceptorOkW ic)` (and the credentials'
  `connCredsOk`); `isEtcdConnG c conn eps ∗ clientReady c ⊢ isEtcdConn conn eps`. `isEtcdConn`'s
  definition and its users do not change.
- The interceptor's spec gives `□ (clientReady c -∗ etcdInterceptorOkM md ic)`, proved by Löb
  induction: the refresh path calls `getToken`, whose `Authenticate` goes through the same
  interceptor (the induction hypothesis, under the step the call takes).
- `getToken.spec`'s pre: `retryClientOk c` (now with the bundle's invariant at `P` and the
  `Authenticate` registration at `c`'s endpoints whose reply token meets `P` for `c.Username`),
  `clientReady c`, `isEtcdConn conn eps`; its post unchanged. Proved: `c.Token` (`□ P c.Token`, a
  premise of `New` with a token), `Authenticate` through `c.Auth` (`authClient.Authenticate`,
  `retryAuthClient.Authenticate`, translated with specs as the admin ones), `UpdateAuthToken`.
- The objects built between the dial and `client.Auth` (`NewKV`, `NewLease`, `NewWatcher`; and
  `clientKVAt`, which they take) have their structure split from the connection fact: each
  constructor's post the structure with the connection named (`kvObjAtC`'s shape without
  `isEtcdConn`), and `newClient` attaches `isEtcdConn` (from `isEtcdConnG` and `clientReady`) when
  it builds `isNewClient`. `isNewClient`, `kvObjAt`, `lessorAt`, `authObjAt` keep their meaning, so
  their users do not change.
- `isNewClient` gains `userClientAt cl conn γa u` for a client with a user name and names the
  `*kv`'s connection as the client's (the E3zc wrappers).

**Finding 2: the credentials' read lock needs a reader token** (decided 2026-10-28, the user's: (1)). `GetRequestMetadata` reads the token
under `authTokenMu.RLock()`. Perennial's `RLock` takes a reader token (`ownRLockToken`; a lock has
`actualMaxReaders`, 2^30 - 1, the bound below which Go's reader counter does not overflow), or a
thread token through the thread pool (`RWMutexThreads.lean`). grpc calls it for every attempt, in
the calling goroutine, and the credentials' contract must be persistent (any number of attempts,
concurrently); no client call spec carries the caller's thread token. Options:
- **(1)** `perRPCCredential.GetRequestMetadata` and `UpdateAuthToken` stay untranslated, a
  trust-boundary axiom each in this repository over the bundle's token invariant (its token
  `""` or one meeting `P`), which assumes fewer than 2^30 concurrent readers (Go's own limit on
  `RWMutex`); `NewPerRPCCredentialBundle` and `PerRPCCredentials` stay proved.
- **(2)** thread tokens through the attempt contract: `grpcInvokerOk`'s pre and every client
  call's spec take the caller's `threadTok` (and give it back), grpc passing it to the
  credentials' call. Faithful, but every call spec of the client changes.

## Phase 1: the statements (drafted 2026-10-28)

Vocabulary (`Proof/go_etcd_io/etcd/client/v3/InvClientAuth.lean`): `Authenticate`'s messages
(`pbAuthenticateRequest`, `pbAuthenticateResponse`: the token) and outcome (`authnCallOut`);
`authTokReg eps u pw P` (the method registered at `eps` with a spec whose reply to `(u, pw)` meets
`P`); `clientAuthAt c eps P` (what `getToken` reads and relies on); `clientReady c conn eps`;
`etcdInterceptorOkG c ic`, `isEtcdConnG c conn eps`, `isEtcdConnG_ready`; `connTokOk conn P`; the
structural forms `clientKVAtS`, `kvObjS`, `lessorAtS`, `authObjS` with `*_of` attaching
`isEtcdConn`; `clientAuthPre cfg eps P` (`New`'s premise), `clientTokAt cl eps P` (`New`'s new
post). `tokenBundleOk` is gone (`tokenBundleInv` in its place).

Specs changed: `grpc.NewClient` (the credentials' contract `Q`), `WithPerRPCCredentials`, the
credentials' (`NewPerRPCCredentialBundle`, `PerRPCCredentials`, new: the bundle's and the cell's
`UpdateAuthToken`, the cell's `GetRequestMetadata`), `Client.unaryClientInterceptor` and
`dialSetupOpts` (gated, `etcdInterceptorOkG`), `Client.dial`/`dialWithBalancer` (`P`; post
`isEtcdConnG` and `connTokOk`), `getToken`/`refreshToken` (pre `clientReady`, `▷ isEtcdConn`,
`ctxErrClient`), `NewKV`/`NewLease`/`NewLeaseFromLeaseClient`/`NewAuth` (structural),
`newClient`/`clientv3.New`/`kubernetes.New` (`P`, `clientAuthPre`; `New`'s post `clientTokAt`).
New specs: `authClient.Authenticate`, `retryAuthClient.Authenticate`, the generated stub's
`Authenticate`.

Glue (proved): `ClientUser.lean`'s `userClientAt` (C1), `clientAttempt_tok`, `userClientAt_of`,
`clientTokAt_user`; `AuthnServedOn.lean`'s `etcdAuthenticateSpec γa` (the server's spec: a reply's
token is issued to the user named) and `authTokReg_of` (`New`'s premise from it). So: a member
serving `Authenticate` with auth on (`etcd_kv_auth_served_onA`) gives `authTokReg [addr] u pw
(tokIssued γa · u)`; `New` at that `P` gives `clientTokAt`; `clientTokAt_user` gives `KV`'s
connection with `userClientAt conn γa u`.

Proved in phase 1 (the statements' consequences only): `dial`, `dialWithBalancer`, `dialSetupOpts`,
`refreshToken`, `NewKV`/`NewLease`/`NewLeaseFromLeaseClient`/`NewAuth`, `newClient` (but one
hole), `New`, `kubernetes.New`, the interceptor (Löb induction on the gate; but one hole),
`NewPerRPCCredentialBundle`, `PerRPCCredentials`.

The `sorry`s (phase 2): `getToken` (was an axiom); `authClient.Authenticate`,
`retryAuthClient.Authenticate`, the stub's `Authenticate` (to translate: `client/v3`'s
`authClient.Authenticate`, `retryAuthClient.Authenticate`, `etcdserverpb`'s
`authClient.Authenticate`, and `credentials`' `perRPCCredentialBundle.UpdateAuthToken`, in the
Goose configurations); the bundle's `UpdateAuthToken` (not translated yet);
`etcd_kv_auth_served_onA` (the handler: `EtcdServer.Authenticate` has no spec yet; then it
replaces `etcd_kv_auth_served_on`); and finding 3's two holes. Axioms: +2 (the cell's
`GetRequestMetadata`, `UpdateAuthToken`, finding 2), −1 (`getToken`).

**Finding 3: the refresh path needs `ctxErrClient`** (open, for the review). `authClient.Authenticate`
passes its error through `ContextError(ctx, err)`, which needs the context's `Err()` to give client
errors (`ctxErrClient`, as every KV call's spec takes). `getToken` is called (a) by the retry
interceptor's refresh, on the call's context (`withVersion`'s child of the caller's), and the
interceptor's contract (`etcdInterceptorOk`) has `ctxOk` only; (b) by `newClient`, on its own
`WithTimeout` context. Both are `sorry` holes (`Client__unaryClientInterceptor.lean`,
`newClient.lean`). Options: add `ctxErrClient ctx cd` to the interceptor's contract (its callers,
the retry clients, then take it: their callers, `kv.Put`, ..., have it), with `withVersion`
keeping it; and derive (b) from the `ContextErrsClient` class (`context.Canceled`,
`DeadlineExceeded` are client errors), a premise `newClient` would take.

**An obligation for `Work`: the `"Bearer "` prefix.** The server reads a token trimmed of
`"Bearer "` (`auth.mdTokenOf`), so C1 states the handler's token as `trimPrefix t "Bearer "` of an
issued `t`. `tokShape` (`<prefix>.<index>`) leaves the prefix unconstrained, so the trimming is not
the identity in general; `Work`'s grant-to-permission step needs it to be (the simple provider's
prefix is random letters, never `"Bearer "`), or a statement of the grants at the trimmed token.

## Phase 1b: the spec review (2026-10-28)

A fresh `spec-reviewer` round on commit `b6bc7e2a56`: `notes/c1-review-1b.md` (the report as
written). Five statements false or unprovable as written, checked against the source:
- **F1** `pbAuthenticateRequest` reads the request read-only, but `EtcdServer.Authenticate` clears
  `r.Password` in a `defer` (CVE-2021-28235's fix; `v3_server.go`): `Password` goes to `recvOwn`.
- **F2** `grpcAttemptMd` makes a key the context carries with no values visible to the handler as
  `some []`; grpc sends no header for it (as `issues/etcd-auth-token-md-empty.md` relies on):
  compare value lists up to empty ones.
- **F3** grpc lowercases the credentials' keys: `credsMapIs` with lower-case keys.
- **F4** `NewClient` calls the credentials' `RequireTransportSecurity()` on an insecure
  connection: its triple in `perRPCCredsOk` (etcd's `return false`, translated). To check against
  grpc's source in phase 2.
- **F5** finding 3 is a falsity, not only a missing proof: Perennial's `isContext` lets `Err()`
  return any typed error, which the refresh path returns: `ctxErrClient` in the interceptor's
  contract.
Quality: Q1 `New`'s post at the attempt level (`attemptTokOk`), Q2 the `"Bearer "` trim discharged
by a law (neither provider makes such a token), Q3 `kubernetes.New`'s post with `clientTokAt`, Q4
laws instead of unfolding (`clientAuthPre_anon`, `credsOfDial` lemmas, `PerRPCCredentials` over
`tokenBundleInv`), Q5 dead names (`tokenBundleAt`, `tokenBundleInv_at`), stale docstrings, Q6 the
2^30-reader bound as a premise, Q7 the caller-chosen `P` recorded as a knowing departure from
TaDa-style specs, Q8-Q10 minor.

### The revisions (2026-10-28)

- **F1** `pbAuthenticateRequest`: `Name` read-only (`recv`), `Password` the handler's own (`recvOwn`).
- **F2, F3** `grpcAttemptMd` (InvGrpc) compares value lists (`metadata.mdVals`) on the keys grpc
  does not reserve, and has no key with no values (`mdGet md k ≠ some []`); `credsMapIs` lowercases
  the keys; `mdMergeAt` is gone.
- **F4** `perRPCCredsOk` adds `RequireTransportSecurity()`'s triple; etcd's
  (`credentials.perRPCCredential.RequireTransportSecurity`, `false`) has a spec, its proof a sorry
  until phase 2 translates it, and `PerRPCCredentials` gives both. Still to check against grpc's
  `NewClient` in phase 2.
- **F5** kept as stated: `ctxErrClient` is not in the interceptor's statement, since phase 2 derives
  it for every `isContext` context from `ctxErrClientAllW_of` (`ErrorsNewOk.lean`; classes
  `ContextReadErrs`, `ContextErrsClient`; `ctxQuiet`'s case needs a lemma). The two holes
  (interceptor, `newClient`'s `getToken`) are where it goes.
- **Q1** `New`'s post at the attempt level: `clientTokAt` ends in `attemptTokOk conn P` (an attempt's
  token, as the server reads it, meets `P` or is the context's own as grpc delivers it,
  `metadata.mdNorm`), derived from the credentials' `connTokOk` by `attemptTokOk_of`; C1
  (`userClientAt`, ClientUser) is `attemptTokOk` at the tokens issued to the user.
- **Q2** deferred to phase 2 (the `"Bearer "` trim law touches the server's token shape).
- **Q3** `kubernetes.New`'s post has `clientTokAt`.
- **Q4** `clientAuthPre_anon`; `credsOfDial_nil`/`_cons`/`_append`. `PerRPCCredentials`' pre stays
  over its receiver's `rc` and `credTokInv` (what the method reads; `dial` unpacks
  `tokenBundleInv`).
- **Q5** `tokenBundleAt`, `tokenBundleInv_at` removed; the stale docstrings fixed.
- **Q6** the reader bound is stated: `credTokInv` holds `threadBound GF ≤ 2^30`,
  `NewPerRPCCredentialBundle` takes it, and `clientAuthPre`'s user branch gives it (only a user
  client makes credentials; anonymous clients and the examples keep `New`'s `2^31`).
- **Q7** a knowing departure: `P` is the caller's, fixed once per bundle (the client does not know
  the server's ghost names; a ghost set of stored tokens would need the same invariant).
- **Q8** left (internal redundancy). **Q9** (a user client of an auth-off member) is for when the
  handler is proved: one registration for every mode. **Q10** (the watch path's `getToken` outside
  the gate) is recorded: the `ClientConn.NewStream` axiom's truth relies on whatever is stored being
  an `Authenticate` reply.

## Phase 2: the proofs (2026-10-28)

The client side is proved; C1's chain rests on no `sorry` but the served `Authenticate`.

- Translated (`Code/**/*.toml`): `Client.getToken`, `authClient.Authenticate`,
  `retryAuthClient.Authenticate`, the stub's `authClient.Authenticate` (and
  `Auth_Authenticate_FullMethodName`), the bundle's `UpdateAuthToken`, the credentials'
  `RequireTransportSecurity`; each proved. The credentials' `GetRequestMetadata` and
  `UpdateAuthToken` stay the two trust-boundary axioms (finding 2).
- `getToken` compares `Authenticate`'s error with `rpctypes.ErrAuthNotEnabled` (`errors.Is`, by the
  status-error spec): rpctypes' facts gain it (`rpctypesInit`'s last conjunct, an `EtcdError`; the
  trust-boundary axiom `ErrAuthNotEnabled_init` on its untranslated initializer, as `ErrNoLeader`'s).
- **F5, revised**: `ctxErrClient` left `getToken`'s and `refreshToken`'s preconditions instead of
  entering the interceptor's contract. Only a user client calls `Authenticate`, so `clientAuthPre`'s
  and `clientAuthAt`'s user branches carry `client.ctxErrClientAll` (a top-level result discharges
  it by `ctxErrClientAllW_of`, as `authkv`'s `Main` premises allow); `getToken` derives the call's
  `ctxErrClient` from `ctxOk`: an `isContext` by it, a quiet context at a fresh descriptor of its
  own (`quiet_ctx`, `InvClientAuth`). The interceptor's and `newClient`'s holes are gone.
- Left: `etcd_kv_auth_served_onA` (`AuthnServedOn.lean`), a server-side stage of its own:
  `EtcdServer.Authenticate` (translated, unproved: `CheckPassword`, the raft request, the retry on
  `ErrAuthOldRevision`), the Authenticate request admitted by `reqPropOkOn` (as `adminPropOk`'s),
  the apply path's `authStore.Authenticate` (`authenticated`) tied to `auth.tokIssued`,
  `AuthServer.Authenticate` and the handler in `authRegs`. Then Q9 (one registration for every
  mode) and Q2.

## The served `Authenticate`: the stage plan (2026-10-28)

`etcd_kv_auth_served_onA` needs the server's whole `Authenticate` path in the mode `on γa`, none of
which a result reaches today. What exists: `authStore.Authenticate` (`authenticated M hs u resp err`,
whose success gives `tokOk M tok u`, in `on γa` `tokIssued γa tok u`), its premise `authnCtx M ctx`
(the context's index and prefix, and the right to issue `simpleTok pre idx`, `freshOk`), the
provider's contract (`TokenSimple`), `CheckPassword`, `Revision`, `LinearizableReadNotify`,
`applierV3backend.Authenticate` (applyErrIs only: the response is dropped), `AuthServer.Authenticate`
(through `authInnerOk`). What is missing, in order:

- **A1. The right to issue, at apply** (design below, "A1's design").
- **A2. Admission.** `rqOk`'s `.authenticate` is `False` (D22, 2026-10-23), the dispatch's case
  refutes it (`uberApplier__dispatch`, `DispatchKVL`). Admit it in the mode `on` (`adminKindOk`'s
  second clause, or a third of `rqOkM`: it needs no admin permission and writes no auth or KV state,
  so `kvEntryOn_nonwrite` keeps the model), prove the dispatch's case, and `applierV3backend.
  Authenticate`'s post carries `authenticated`'s outcome to the waiter.
- **A3. The result to the requester.** The wait registry's result for the entry carries the
  response's token with `tokIssued γa tok name` (persistent), as `adminOutOn` carries an admin's;
  `reqPropOkOn` gains the clause for the request (its `Qr`).
- **A4. `EtcdServer.Authenticate`'s spec and proof**: `LinearizableReadNotify`, `CheckPassword`,
  `GenTokenPrefix` (no spec yet: random bytes, `simpleTokenPrefix`), the `raftRequest`, the revision
  loop (a retry keeps the earlier token's issue: harmless, the response is the last one), the
  `defer` clearing `Password`. Specs in the mode `on` as `UserAdd.specOn`.
- **A5. The handler**: `authInnerOk` for `Authenticate` from A4, the registration in `authRegs`
  (Q9: one registration for every mode), then `etcd_kv_auth_served_onA`'s proof and its swap for
  `etcd_kv_auth_served_on`.

Effort, by analogy with E3n/E3w (the admin entries, each several sessions): A1 and A2 are the
largest (the apply thread's resources and the dispatch); A4 is one long proof; A3 and A5 are glue.

### A1's design (2026-10-28)

**What Go does.** `applierV3backend.Authenticate` puts in the context not the entry's index but
`ConsistentIndex()`: `authStore.Authenticate` takes no batch lock inside apply, so the post-lock hook
does not run and the value is the consistent index before the entry (`< e.Index`; the spec of
`applyEntryNormal` has it: `ciEff γ st.k < m.index`). Each applied entry's `defer` then raises the
consistent index to at least its index. So the index of the tokens issued is strictly increasing
from one `Authenticate` entry to the next, whatever the prefix (`GenTokenPrefix`'s random letters,
not provably distinct): `<prefix>.<index>` is issued once. (Not a Go bug: `isValidSimpleToken`
waits for an applied index at least the token's, and a smaller one is applied already.)

**The ghost** (`Tokens.lean`, done): `freshBelow γf n`, the rights' authority whose minted tokens
are of an index below `n` (`simpleTok_idx_inj`: a token's index is determined by the token, the
decimal having no `.`); `freshBelow_mint` mints `<pre>.<x>` for any `x ≥ n`, moving the bound to
`x + 1`; `freshBelow_init` from `NewTokenProvider`'s empty authority (`ghostMapAuth γf 1 ∅`, which
`authSrvTP_on` drops today).

**The plumbing.**
- The bound against the consistent index, threaded by the apply loop: `srvTokRights E k` (in the
  mode `on γa`, `∃ n, freshBelow γa.fresh n ∗ ⌜n ≤ k⌝`; else `True`), monotone in `k`, carried in
  the mode-`on` specs at `k = ciEff γ st.k` (`applyEntryNormal`, `apply`, `applyAll`, the run loop):
  their posts already make `ciEff` monotone (`apply`: `max`; `applyAll`: equal or `max`), and a v3
  entry ends at `k = m.index`. It starts from `freshBelow_init` (the authority routed from
  `authSrvTP_on` with the auth row, `authApplyResPre`).
- The mint at the server: an `Authenticate` entry decodes to its prefix `pre` (the request's
  `SimpleToken`), and `applyEntryNormal` knows `x = ciEff γ st.k` with `n ≤ x < m.index`: it mints
  `tokFresh γa (simpleTok pre x)` and ends with the bound `x + 1 ≤ m.index`.
- The applier: `applierV3backend.Authenticate`'s mode-`on` triple does not use the generic
  `isConsistentIndexer` contract (whose triple says nothing of the value) but its own premise: from
  `Pre` and the right `R`, a split `C` with `E.ciC C`, the value `x` that `ConsistentIndex()`
  returns from `C`, and `freshOk M (simpleTok pre x)`. The server proves it from `wp_ci_get` (the
  value `ciEff γ st.k`, `Pre` being `applyThread γ st ∗ …`). Only this proof calls the contract, so
  nothing else changes. `R` travels with the request through the admin-on chain (`applierAdmin`,
  `applierAdmL`), with A2.

**A1 done (2026-10-28): the plumbing.** `srvTokRights` and `authFreshInit` are in
`AuthApplyRes.lean` (below `StartOn`, which needs them), with `srvTokRights_mono`, `_congr` and
`_init` (`authFreshInit E.authMode ⊢ srvTokRights E k`). The authority's route: `authSrvTP_on`
keeps `NewTokenProvider`'s `ghostMapAuth γf 1 ∅`, `authStoreKit_on` takes it into its resource and
its post's `authApplyResPre` (mode `on`), `authApplyResB_of_pre` hands it back as `authFreshInit M`,
and `NewServer`'s construction (generic in the mode) turns it into `srvTokRights` at the boot's
consistent index, the last conjunct of `applyBuiltNAOn`, `applyBuiltOn` and `applyStartOn`
(`applyResOn`: before its pure facts). Threaded through `applyEntryNormal.specOn` (post: at
`m.index` on a v3 entry, else unchanged), `apply`, `applyEntries`, `applyAll` (pre and post at
`ciEff γ st.k`) and `run`'s job bodies. Nothing mints yet (A2). No axiom or `sorry` changed.

## A2, spec-first (2026-10-28)

The user's instruction: as C1, the statements first (phase 1: drafted, glued, stubs `sorry`, the
build green), a fresh spec review (phase 1b), the proofs after (phase 2).

**The path.** An `Authenticate` entry, with auth on, goes the admitted admin requests' way:
`applyEntryNormal` → `adminEntryOn` (server) → `apply.Apply.adminSpecL` → `uberApplier.Apply`
(`adminSpecL`) → `dispatch.adminSpec` → the chain's admin triples (`adminTriples`, promoted through
the wrappers: none overrides `Authenticate`) → the backend's `fuelSpecX`/`stepSpecX` →
`isAuthStepsX` → the store (`authStore.Authenticate`). `needAdminPermission` is false for it, so the
auth applier's check passes (`adminPassL_of_not_need`).

**The phase-1 statements** (as drafted; the items as planned changed in two places, below).
1. **The consistent index's value** (vocabulary): `AEnv.ciC : IProp GF → w64 → Prop` (the resource
   `C` under which `ConsistentIndex()` returns `x`); `isConsistentIndexer`'s triple returns that `x`
   (`{{ C }} ConsistentIndex() {{ RET #x; C }}` for `ciC C x`), `ciSplit` gives `C` with its value,
   `ciSplitAt E Pre x` at a known `x`; the server's `srvCiC γ ci C x` adds `x = ciEff γ st.k`
   (`wp_ci_get`'s value). Stronger, true, and what lets the apply layer name the token's index.
2. **The store** (`auth`): `authStore.Authenticate.specTB`, `Authenticate.spec` at the tie's
   resources (`authWRxB`, as the five admin steps' `specTB`), with a reader slot of `enabledMu`
   (`enabledRd`: `IsAuthEnabled` read-locks it), and its error `ErrAuthNotEnabled`'s or
   `ErrAuthFailed`'s (`authErrOf`; the NOSPACE branch needs the error to be an auth one).
3. **`isAuthStepsX`** gains `Authenticate` and a parameter `RD`, the reader slot it lends: from
   `RD`, `authnCtx`, the authority, `X hs` and `W`, all back, with `authenticated`. *Changed:* no
   `enabledRd` slot in the server's `W`; `RD` is the kit's `E.RD` (in the mode on `authRd = enabledRd
   ∗ cacheRd ∗ beRd ∗ R`), which `kvOwn` holds and lends (`kvOwn_rd`). `authApplyResB`,
   `authStepsAtHook`, `authApplyResPre` take it (`E.RD`; the construction's `authRd stp R`).
4. **The backend**: `applierV3backend.Authenticate.specX`: `authenticateIs r am`, `ciSplitAt E Pre
   x` and the right `tokFresh γa (simpleTok am.simpleToken x)`; post: the authority, `X`, `W` back,
   `authnOut γa am.name resp err` (an auth error and no response, or a response whose token is
   issued to `am.name`, `tokIssued`, read-only).
5. **The chain** (`AdminChain`): `AdminReq.authenticate name pre`, its `respTy`, its
   `extraPre E γa Pre` (`∃ x, ciSplitAt E Pre x ∗ tokFresh …`; `True` for the other five), its
   `result` at the response `resp` (`Own γa hs ∗ authnOut`; the five ignore `resp`); `adminTriples`'
   pre adds `ar.extraPre E γa Pre`. *Changed:* the plan had a frame `C` beside `Pre`; but `C`
   (`applyThread ∗ applyBackend`) is inside the critical section's `Pre` (the hook needs it), so the
   method borrows it from `Pre` as the KV methods do (`ciSplit`), at the index the right is for.
6. **Dispatch and `Apply`**: `adminReqOf` maps `authenticate`; `adminExtra E γa rq Pre`
   (`adminExtra_of_ne`: free for the other kinds); `dispatch.adminSpec`,
   `uberApplier.Apply.adminSpec(L)`, `apply.Apply.adminSpec(L)`: pre `if v3 then adminExtra … else
   True`; `adminDone` with the response pointer (`Resp = mkOk (respTy) resp`).
7. **Admission**: `adminKindOk`'s `.authenticate => needAdminPermission rq = false` (no name
   bound: `GetUser` only reads; review 1: a request with an admin field beside `Authenticate` would
   pass the admin check and dispatch `Authenticate`, whose `adminTieAr` is then false; the server
   proposes it alone, so A3 can give it); `adminKindOk_needAdmin` takes `kind ≠ authenticate`.
8. **The server**: `adminEntryOn.spec` without `needAdminPermission rq = true`, with
   `if v3 then adminExtra … else True`; its post adds `adminAuthnAr γa ar rq out` (with `v3`: unless
   not an `Authenticate` or not dispatched, `ar ↦□ v` with `Resp` the response and `authnOut`, for
   A3). `adminStateR` is `st' = st` for `Authenticate` already. `applyEntryNormal`'s statement does
   not change: its proof mints (`freshBelow_mint` at `x = ciEff γ st.k`) and gives `ciSplitAt` at
   its `Pre`.

**Phase-1 stubs** (`sorry`, to prove in phase 2; the proofs at `2040bccc8a` are the start):
`auth.authStore.Authenticate.wp_tieB`; `isAuthStepsX_of_authInvT`/`TB`'s `Authenticate` clause;
`applierV3backend.Authenticate.wp_specX`; `applierAdmin_backendX`'s `authenticate` case;
`dispatch.wp_admin`; `uberApplier.Apply.wp_admin`/`wp_adminL`; `apply.Apply.wp_admin`/`wp_adminL`;
`adminOut_model`'s `authenticate` case (`ApplyTieOn`); `apply_admin_entry_on`; `applyEntryNormal`'s
`Authenticate` branch (the mint, and A3's response).

**Phase 1b, the reviews** (two fresh `spec-reviewer` rounds, 2026-10-28). Review 1's four defects,
repaired: (1) the store's error: `assign` passes its error through, which the provider contract
left unconstrained; `tokenProviderOk(A)`'s `assign` now returns `(nil ∗ tokOk) ∨ (≠ nil ∗
authErrOf)` (the simple and no-op providers meet it; JWT, out of scope, does not), and the store's
`specTB` and `isAuthStepsX`'s clause say `nil ∨ authErrOf`; (2) `isAuthStepsX`'s clause carried no
error fact; (3) `adminKindOk` (item 7); (4) `authnOut` split the response into persistent fields,
which the gRPC reply (`pbAuthenticateResponse.send`, `resp ↦ v`) cannot be rebuilt from: now
`∃ v, resp ↦ v ∗ tokIssued γa v.Token' name`. Laws added: `ciSplit_of_at`,
`adminExtra_authenticate`. Review 2 (on the repaired drafts), left open:
- **`specX` needs `context.WithValue`'s `Value`** (a trust-boundary axiom of this repository,
  `Spec/context/WithValue.lean`): the store's `authnCtx` needs `ctx.Value(AuthenticateParamIndex{})`
  to return the index, and the axiom says nothing of `Value`. Strengthening it is a change to a
  trusted statement: the user's to approve.
- The consumers do not yet take the new specs as premises (`applierAdmin_backendX` the backend's
  `specX`, `isAuthStepsX_of_authInvTB` the store's `specTB`; `isAuthStepsX_of_authInvT`, used by
  `Results.apply_auth_steps_tie`, would need an any-mode `specT`): phase 2's gluing.
- `adminOut_model` still takes `needAdminPermission rq = true`; for `Authenticate` it gives
  `hs' = hs`, `st' = st` (phase 2).
- Restore the proofs at `2040bccc8a` (`dispatch.wp_admin`, the four `Apply` admin proofs,
  `apply_admin_entry_on`) with the `sorry` confined to the `Authenticate` case, as
  `applierAdmin_backendX` has it.
- A3 will want a law from `adminAuthnAr` without its "not dispatched" case (an `Authenticate` with
  `v3` is dispatched) and one from `authnOut` to `pbAuthenticateResponse.send` with `tokIssued`.
