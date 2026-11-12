# Repair: group `lease-auth` (2026-11-09)

Files: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/{lease,lease/leasehttp,auth}/`, `SpecPlan/Spec/golang_org/x/crypto/bcrypt/`,
`examples/specreq/{lease,auth}`. Reports: A9 completeness and provability, parts 3c and 3d.

## Findings

### A9-completeness

- **F1 (read denial at one auth state)**: no change needed here. 3d's `checkPost`/`checkDenied` was
  already the three-view form. client-core has meanwhile restated W0's `State.deniedSince` over three
  views (`Model.lean:895`) and filed `nonissues/etcd-auth-read-denied-across-views.md`. I had filed a
  duplicate and removed it; the indexes are regenerated. New snippet `auth/check.go` `ReqDenied`: if
  auth stays off, or the user stays root, from the lower bound on, the reader is never denied (from
  `checkDenied`'s `af.enabled` and `¬ ax.isRoot u`).
- **F2 (`ckptOk` unmeetable)**: fixed.
  - `Lease.ckptOk cp R` is now at `context.Background()`, the lessor's only context
    (`lessor.go:437,679`), and takes and returns a `threadTok`. It no longer takes a free `ctx` with
    `ctxOk`.
  - `lessor.Renew.spec` takes the caller's `threadTok` and returns it.
  - `NewLessor.spec` takes a `threadTok` for the run loop, which calls the checkpointer. The run loop
    is a goroutine of the program, so adequacy counts it. `lessor.Stop.spec` gives the token back,
    because it waits on `doneC`.
  - The header realization and the `SetCheckpointer` notes are updated.
  - In snippet `ReqPromoteCheckpointer`, the checkpointer now panics on a context other than
    `Background()` and forks a goroutine, which needs a thread token.
- **F3 (`clusterOk` has no introduction)**: fixed differently. `clusterOk` is now transparent: the
  `Version()` triple through the `cluster` interface, `□ {{True}} cl.Version() {{v, v = nil ∨ ∃ sv, v
  ↦□ sv}}`. Each client proves it for its own type: `noCluster` from its body, and 2e for
  `*RaftCluster` (request below). No law is needed.
- **F4 (`authBackendAt`, `authHook`, `authnCtx` have no introduction)**: fixed.
  - `authnCtx` is transparent and is now over the cluster `γ` instead of `γa`. It is defined over a
    new transparent `ctxValIs ctx key v`, a WP of `ctx.Value(key)` in the style of
    `Context.ctxNoMeta`. It holds the index (as `uint64`), the prefix (a string without `.`), and
    `tokenUser γ (simpleTok p idx) name`.
  - `simpleTok` moved from `Internal` to `Api`. The internal opaques `tpAuthn` and `simpleAuthn`
    had no introduction either; they are removed, and `tp_assign`/`tokenSimple.assign` take
    `authnCtx`.
  - `authHook` now has an introduction, `authHook_intro`:
    `authBeCur γa be ∗ authBeHook be Pre Q ⊢ authBeCur γa be ∗ authHook γa Pre Q`. It needs two new
    predicates. `authBeCur γa be` is exclusive: the store's current backend, the writer's. It comes
    from `NewAuthStore`, and `Recover` moves it from `be0` to `be` and now gives back
    `authBackendAt be0 _`, the backend it names. `authBeHook be Pre Q` is opaque, over the
    `AuthBackend` value, like `Lease.beHookRun`.
  - The introductions of `authBeHook` and `authBackendAt` belong to 4a/4b, as their
    `LeaseBackend.lean` does for the lessor (request below).
  - The admin specs are unchanged: they still take `authHook γa Pre Q`.
- **F5 (context predicates are not grpc's)**: fixed.
  - `Auth.ctxInMD`, `ctxCertUser` and `ctxPeerCN` are now `abbrev`s of `Grpc.ctxInMD`,
    `Grpc.ctxCertUser` and `Grpc.ctxPeerCN`. The local `MD` and `mdGet` are dropped in favour of
    `Grpc.MD` and `.get`.
  - The old opaque `ctxInMD` also meant "every key has a value", which grpc's predicate does not
    say. That is now the premise `tokKeysOk md` inside `ctxToken`. A run's context gets it from
    `Grpc.rpcCtx_vals`, and `WithRoot`'s context from `metadata.New`.
  - The `ctxInMD`/`ctxCertUser` persistence laws are dropped; grpc's own laws cover them.
- **F7 (`waiterOk` false at `NewServer`)**: fixed.
  - `waiterOk iw R` is gated: each call needs `R`.
  - `R` is carried as follows. `tokenProviderAt tp γ R rt` holds it. `NewAuthStore` turns it into a
    new persistent `authGate γa R`. `AuthInfoFromCtx` and `authInfoFromToken` take
    `authGate γa R ∗ □ R`.
  - Internally, `tpOpen tp γ R`, `simpleAt t γ R`, and `tp_info`, `tokenSimple.info` and
    `isValidSimpleToken` take `□ R`. The no-op and JWT providers work at any `R`.
  - The server uses `R := srvStarted`.
  - In snippet `ReqBoot`, the waiter panics before `started` is set, and a token check runs after
    the start.
- **F8 (bcrypt's error unconstrained)**: fixed.
  - New `Bcrypt.errIs` and `Bcrypt.init.spec`: the three package variables, each `errors.newVar`
    of its message, distinct.
  - `GenerateFromPassword.spec`: when `72 < len`, the error is `errIs ErrPasswordTooLong err` (the
    length test comes first). Otherwise an error only when the cost is above 31.
  - New snippet `auth/admin.go` `ReqLongPassword`.
- **F9 (`RenewHTTP`'s post)**: fixed. The post is now one of:
  - `err = nil`;
  - `Lease.errIs ErrLeaseNotFound err`;
  - `∃ t, Lease.errIs ErrLeaseNotFound t ∗ errIsNot err t`.

  `errIsNot` is a new transparent predicate in `leasehttp/Api`: Perennial's `errorWalkTree`,
  `TreeTyped` and every `IsWalk` answering `false`. That is what `errors.Is` needs to be safe and
  false. The "why true" text lists each error the code returns. New snippet `lease/lessor.go`
  `ReqRenewForward`.
- **Second tier, `authLb` for readers outside the read slot**: fixed with a new law,
  `authStoreAt_lb : authStoreAt st γ γa ⊢ authLb γa 0`.
- **Second tier, `AuthReach` for `Recover`**: not fixed. It needs a law turning W0's `Reach` into
  `AuthReach`. That is W0's (client-core's) or 3a's; I left it as recorded.

### A9-provability

- **Snippet `ReqGrantHook` cites the stale `Mvcc.hookRun`**: fixed. It now cites `Lease.beHook`
  and `Lease.beHookRun`.
- **F3 (hook contracts have no slot in 3a)**: my half is fixed (`authHook_intro`, the `authBeCur` of
  F4). The slot in `optsOk` belongs to apply-txn (request below).

### Brief item 3 (sentinel errors)

- **Lease**: `init.spec` was already existential. It now also gives `errors.newVar` (the
  `*errorString` type and the message) of each error, needed for `errors.Is` with them as targets.
  `errIs` is listed as persistent.
- **Auth**: the opaque Lean function `errOf` cannot be realized, so it is removed. The new pieces:
  - `AuthErr.global` and `AuthErr.msg`;
  - `errIs ae v := globalAddr ae.global ↦□ v` (persistent);
  - `init.spec : ∃ ev, (□ ∀ ae, errIs ae (ev ae) ∗ errors.newVar ae.global ae.msg) ∗ ⌜ev injective,
    non-nil⌝`.

  Every post that named `errOf ae` now says `errIs ae err`, with the pure disjunctions restated as
  `∗`/`∨`. The affected definitions are `admReply`, `checkPost`, `adminPost`, `AuthEnable`,
  `CheckPassword`, `Authenticate`, `AuthInfoFromCtx`, `NewTokenProvider`, `decomposeOpts` and
  `tokenNop.assign`. `errOf_ne_nil` and `errOf_inj` are gone; `init` gives them. `errOf_srvErrVal`
  is removed (request to server-core below). With it goes auth's import of `etcdserver/errors`,
  replaced by `grpc.Api`, `context.Api` and Perennial's `errors.NewVar`.
- **Bcrypt**: see F8.

### Coordinator's requests from backend-schema

1. **`lease/Api.lean`, `beTxHeld`'s realization text**: done. It now reads
   `∃ m, beSess γb q' (mvccFpM m) S` and `Sess.sameOn (mvccFpM m)`, and says the lease bucket is
   disjoint from either footprint.
2. **`beTurn`**: done in the realizations. Auth's batch locks are taken and released within one
   method, so the turn never crosses a call and no auth statement changes. This is said in the
   realization of `Internal.lean`'s `wrStep`/`wrRec` (they carry `Backend.beTurn γb` with the
   session, from 4b's `btLockIn`/`btUnlock`) and in `Api.lean`'s `authCur`.

## Requests to server-core

1. **`etcdserver/errors/Api.lean`**: state the tie of the auth and lease sentinels to the server's
   mapping, in whatever sentinel encoding you choose.
   - Auth: for each `ae` with `ae.etcd = some e`,
     `isPkgInit auth ∗ Auth.errIs ae v ⊢ (v is the server error of e; srvErrOf v e ∧ leaf)`.
     `Auth.errOf_srvErrVal` is gone; it equated an unrealizable constant with `srvErrVal`.
   - Lease: the same for `ErrLeaseNotFound`/`.leaseNotFound`, `ErrLeaseExists`/`.leaseExist` and
     `ErrLeaseTTLTooLarge`/`.leaseTTLTooLarge`, plus "unmapped" for `ErrNotPrimary`. Lease gives
     `errIs` and `errors.newVar` of each from `init`.
   - Bcrypt's `ErrPasswordTooLong` is unmapped. `Bcrypt.init` gives its message for `srvErrShape`.

   Your file may now import `auth/Api` and `lease/Api`: auth no longer imports `errors/Api`.
2. **`NewServer`**:
   - `lessor.NewLessor` now takes a `threadTok`, which `Stop` gives back.
   - The checkpointer closure's obligation `ckptOk cp R` is now at `context.Background()` with a
     `threadTok`. Discharge it with `reqCtxOk`/`reqPrin` from `ctxNoIncoming_background` and
     `reqPrin_noIncoming`.
   - `NewTokenProvider` takes `waiterOk iw R` at `R := srvStarted`. `NewAuthStore`'s post gives
     `authGate γa R` and `authBeCur γa be`; keep both in the server's state.
   - `clusterOk (iface cluster)`: prove it from `RaftCluster.Version`'s spec, or ask 2e (server-boot)
     for one.
3. **`EtcdServer.AuthInfoFromCtx`**: supply `authGate γa R ∗ □ srvStarted`. `ctxToken` now needs
   `tokKeysOk md`, which a run's context gives by `Grpc.rpcCtx_vals`.
4. **`EtcdServer.LeaseRenew`**: on the leader, pass the `threadTok` to `lessor.Renew`. On the
   forwarding path, use `RenewHTTP`'s new post: `errIs` gives `ErrLeaseNotFound`, and `errIsNot`
   makes `errors.Is` false, so that error is retried. A snippet of the forwarding path in
   `etcdserverreq` (`ReqKeepAlive` on a follower) is still owed. `lease/lessor.go`'s
   `ReqRenewForward` covers `RenewHTTP` alone.
5. **`applySnapshot`**: `authStore.Recover` now takes `authBeCur γa be0` and returns
   `authBeCur γa be` together with `authBackendAt be0 _`.

## Requests to backend-schema

1. **Add an `AuthBackend.lean`, as `LeaseBackend.lean` does for the lessor**, with these laws:
   - `authBackendAt_intro`: from `abe ↦□ authBackend.mk (beIface b) lg`, `NewAuthBackend`'s post,
     and 4a's parts of `auth`, `authUsers` and `authRoles` holding `a`, to
     `Auth.authBackendAt (iface abe) a`;
   - `authBackendAt_elim`: the reverse, for a backend's close;
   - `authBeHook_intro`: from `abe ↦□ authBackend.mk (beIface b) lg ∗ isBackend γ b p Pk ∗
     beHook γ DFrac.discard f ∗ (∀ q, hookRun γ q Pk f Pre Q)` to `Auth.authBeHook (iface abe) Pre Q`.

   4b declined to own the vocabulary earlier. These are introduction laws only, as for the lessor.

## Requests to apply-txn

1. **`apply/Api.lean`**: add slots in `optsOk`/`optsSt` (A9-provability F3, A9-completeness F6) for:
   - `Auth.authBeCur γa be` in `authSt`;
   - a `□` producer of `Auth.authBeHook be Pre Q` under `R` (from 2d's hook), which
     `Auth.authHook_intro` turns into each admin method's `authHook`.
2. **`applierV3backend__Authenticate.lean:7` and `apply/Api.lean:762`**: the sketches say
   `Auth.authnCtx γa ctx name idx`. It is now `Auth.authnCtx γ ctx name idx`, transparent. Build it
   from `context.WithValue` twice, given client-core's value law below, and from `authnIdx`'s
   `tokenUser γ (simpleTok p idx) name`.

## Requests to client-core

1. **`SpecPlan/Spec/context/Api.lean`**: `WithValue.spec`'s post should say what `Value` returns. Either:
   - `ctxValueAt parent ctx key` carries the value, with a law giving
     `□ ∀ Φ, ▷ Φ #v -∗ WP ctx.Value(key) {{Φ}}` (and pass-through for another key's `Value`); or
   - a transparent `Context.ctxValIs ctx key v` in that shape.

   `Auth.ctxValIs` is defined in that shape, so it would become an abbreviation of yours.
   `authnCtx`'s producer needs this.
2. **`AuthReach` from W0's `Reach`** (A9 second tier, for `authStore.Recover`'s premise): a law in W0
   that a reached later state's auth table follows by admin steps. Optional.

## Requests to server-boot

1. **`membership`**: a spec of `RaftCluster.Version` (any goroutine; `nil` or a readable
   `*semver.Version`), from which `Lease.clusterOk` for `*RaftCluster` is proved. `clusterOk` is now
   transparent.

## New decisions

- **The run loop's thread token.** `NewLessor` now takes a `threadTok` and `Stop` returns it. The
  lessor's run loop is untranslated, but it is a goroutine of the program, and it calls the
  checkpointer. With the server's closure, the checkpointer calls `raftRequest`, which needs a
  thread token. Without the token, the trusted `NewLessor` would hand a counted resource to a thread
  that did not take one.
- **The token provider's gate.** The waiter is gated on a persistent `R`, the same way as the
  checkpointer. `R` is threaded through `tokenProviderAt` (a new argument) and `authGate γa R` (a
  new predicate). The alternative, a gate token as `SetCheckpointer` has, has no Go call to hang
  on: the provider never learns that the server started.
- **The auth store's backend as writer state.** `authBeCur γa be` is a new exclusive token, so that
  the hook contract can be stated over the backend value, as the lessor's is, while the admin specs
  keep `authHook γa`. Folding the backend into `authCur` would have changed `authCur`'s arity and
  so every apply statement.
- **The sentinel tie moved out of auth.** The tie of auth's errors to the server's sentinels belongs
  to the owner of the mapping (`togRPCError`'s map), in its own encoding.

## Build

- `etc/specs-build.sh --dir SpecPlan/Spec/golang_org/x/crypto/bcrypt SpecPlan/Spec/go_etcd_io/etcd/server/v3/auth
  SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease/leasehttp`: **OK (128
  modules)**.
- A check build of `etcdserver/apply`, `etcdserver` and `storage/backend` failed, but in other
  groups' files that are being edited concurrently: `client/v3/Api.lean:371` and
  `bbolt/Api.lean:396,531`. No error was in, or caused by, my files. Outside my directories, the
  names I changed appear only in comments (`grep`).
- Snippets: `go vet ./specreq/lease/ ./specreq/auth/` passes, and `gofmt -l` prints nothing.
- `etc/issues-status.py --check`: OK.

## Second pass (coordinator's list, `second-pass.md`)

- **`AuthReach` law (client-core)**: done. New `authReach_of_reach.spec : ∀ σ σ', Reach σ σ' →
  AuthReach σ.auth σ'.auth` in `auth/Api.lean`, a pure obligation over W0's model. A `Step`
  changes `σ.auth` only through `authStep` of a permitted admin request, which is `admStep`. Refusals,
  denials, errors, other kinds' steps and environment steps leave it unchanged. 2d gets
  `authStore.Recover`'s `AuthReach a a'` from this law.
- **`WithRoot`'s value-child (server-core)**: done. The token disjunct also gives
  `Context.ctxValueAt ctx ctx' mdIncomingKey{}`. `ctx'` is `metadata.NewIncomingContext(ctx, md)`,
  a `WithValue` of the caller's `ctx` itself. The index and prefix values go only to the provider's
  context.
- **`TimeToLiveHTTP`'s header (server-core)**: done. New `leasehttp/TimeToLiveHTTP.lean`, a trusted
  spec. It has a premise `⌜leasePeerURL url⌝`, a new opaque `Prop`: the deployment premise that the
  URL is an etcd member's lease endpoint, which 2c's `leaseTimeToLive` already assumes. Without it,
  a malformed `200` reply panics (`issues/etcd-leasehttp-timetolive-nil-{response,header}-panic.md`).
  The post is one of:
  - `Proto.msgAt LeaseInternalResponse resp (own 1) c ∗ ⌜norm c = c ∧ ltlReply c id⌝`, where
    `ltlReply` is a new opaque relation: the inner response of lease `id` with its `Header` set;
  - `ErrLeaseNotFound`, the global's value;
  - an error on which `errors.Is` is false (`errIsNot`).

  **Request to server-core:** turning `ltlReply` into `replyHdrOwn` and the fields needs 3h's
  field vocabulary. Add that law next to `replyHdrOwn`, or say if you want it stated here.
- **`Auth.ctxValIs`**: it fits. It is now `abbrev ctxValIs := Context.ctxValueIs`.
  `WithValue.spec`'s post gives it, and `ctxValueIs_wp` is the old WP form, so `authnCtx` is
  introduced directly from the applier's two `WithValue`s.
- **`srvErrOf`/`srvErrVal`**: none of my files uses them; the first pass removed `errOf_srvErrVal`.
  The header now points to server-core's `authErr_srv`. Its `leaseErr_srv` and `bcryptErr_shape`
  are stated over my `Lease.errIs` and `Bcrypt.errIs`, and they match my `init`s.
- **`Proto.norm` survival**: the one new pure relation over `Proto.Content`, `ltlReply`, has
  `ltlReply_norm`. It reads only message-field presence and an integer. The other message relations
  need nothing:
  - auth's `authReqAt`/`authRespAt`/`authnRespAt` are opaque heap predicates over pointers. Their
    intended realizations go through 3h's `reqHolds`/`bodyHolds`, which grpc-v3rpc's `holds_norm`
    covers.
  - `Lease.ckptOk` quantifies over every content.
- **Build**: `etc/specs-build.sh --dir` over the four directories is OK (129 modules).
  `go vet ./specreq/lease/ ./specreq/auth/` passes.

### Second pass, extra item: a source for `leasePeerURL`

I did not derive it: it stays a stated deployment premise. The cluster's vocabulary for a peer
address is rafthttp's `peerAddr ν a`, `Http.protoAt a P ∗ ⌜raftCompat ν P⌝`. `raftCompat` fixes `P`
only under `/raft`, and outside it only *allows* `404`/`301`. It does not forbid a `200` with an
arbitrary body on `/leases/internal`, and forbidding that is exactly what `leasePeerURL` says. So
no law from `srvNet`/`peerAddr` and `urlsHosts` can conclude it.

The premise is true of every etcd member: embed's peer port serves `NewHandler`, and this
repository's starters serve only rafthttp's mux, which answers `404`. `TimeToLiveHTTP.lean`'s
docstring now says this, and names the carrier: `EtcdServer.leaseTimeToLive.spec` (server-core's
assumed contract, "the leader's peer URLs are etcd members'"), and through it the server's
top-level specs that reach a forwarded `LeaseTimeToLive`.

**Request to server-boot**, which would make it derivable:
- Strengthen the peer port's protocol so that on `/leases/internal` it either is leasehttp's
  encoding (a new `leaseCompat P`) or answers only the mux's `404`/`301`.
- Then a law in `leasehttp/Api.lean`, `peerAddr ν a ∗ ⌜urlsHosts [u] = some [a]⌝ ⊢
  ⌜leasePeerURL (u ++ LeaseInternalPrefix)⌝`, could replace the premise. I would add it once
  `leaseCompat` exists.

**Request to server-core:** keep `leasePeerURL (u ++ LeaseInternalPrefix)` for the members' peer
URLs as an explicit premise (or a premise inside the boot contract), not a sketch-only
assumption.

Build: `leasehttp` OK (3 modules).

## Re-review (`R-A9-apply-txn-lease-auth.md`)

- **N1 (first tier, a stale `authHook` survives `Recover`)**: fixed as the reviewer proposed.
  - The store-indexed `authHook` and `authHook_intro` are removed.
  - `hookOut` is now over the backend: `hookOut be Pre Q := Q ∨ (Pre ∗ authBeHook be Pre Q)`.
  - New `AdminTriple` shape: binder `(be : GoInterface)` before `Pre Q`; pre `… ∗ authBeCur γa be
    ∗ Pre ∗ authBeHook be Pre Q`; post `P ∗ authBeCur γa be ∗ hookOut be Pre Q ∗ ∃ res, …`.
  - `AuthEnable`, `AuthDisable` and `HasRole` have the same change (`HasRole`'s post
    `authCur ∗ authBeCur γa be ∗ Q ∗ …`).
  - An unused hook now comes back as the backend's `authBeHook be`. After `Recover` the store's
    `authBeCur` names the new backend, so an old backend's hook can no longer be used against it
    (`authBeCur_excl`).
- **S3**: `lessor__Renew.lean`'s Users note now says that the leasehttp handler (`http.go:91`) must
  get a `threadTok` for `Renew` if it is ever specified. It is out of scope today: there is no
  `NewHandler` spec.
- **S4**: the `Assumes:` lines of `lease/ReqPromoteCheckpointer` and `auth/ReqBoot` now mention the
  caller's thread token.
- **Request to apply-txn:** the eleven admin sketches and `apply/Api.lean:139,736,801` still cite
  `Auth.authHook`/`authHook_intro`.
  - Replace them with: `authSt`'s `Auth.authBeCur γa be` plus `hooksOk`'s `Auth.authBeHook be R Q`,
    passed straight to the `AdminTriple`, with `authBeCur` given back.
  - `hookOut be R Q` is `Q`, or `R` with the backend's unused hook.

  Only comments refer to it, so nothing breaks the build.
- Build: `auth`, `lease` OK (123 modules). `go vet` passes.
