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
