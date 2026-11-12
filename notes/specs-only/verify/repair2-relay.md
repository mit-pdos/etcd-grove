# Relay repairs: lease-auth and grpc-v3rpc (server-core's RR requests)

2026-11-09. The requests to **lease-auth** and **grpc-v3rpc** in `repair2-server-core.md` (with
`repair2-client.md`'s `soleMember`/`leaseFact` background). Go checked against `.lake/src/server`.

## lease-auth

### 1. `auth.NewTokenProvider`'s thread token: **fixed differently** (no token at all)

- Go: `enable` starts the TTL keeper with `go t.simpleTokenKeeper.run()` (`simple_token.go:188`).
  The constructors only allocate: `newTokenProviderSimple` (`:248`), `newTokenProviderJWT`
  (`jwt.go:127`), `newTokenProviderNop`. Perennial's `wp_fork` gives the forked goroutine a fresh
  token of its own (`Lifting.lean`, `wp_fork_tok*`), so no token of the caller's is ever needed.
- The request asked to return the caller's token on success. I dropped the `threadTok` premise
  instead, from `NewTokenProvider.spec` and `newTokenProviderSimple.spec`. The error branch gives none
  back either. For the caller this is strictly stronger (it keeps its token throughout) and has no
  unneeded premise.
- I removed the "provider's reserved `threadTok`" design from the internal vocabulary to match:
  - `Internal.lean`: in `simpleAt`'s keeper field, `nil` no longer holds a token. `keeperRun` no
    longer carries one, and `donec`'s close carries none.
  - `simpleTokenTTLKeeper.stop.spec` now posts `True` (it was `threadTok`).
  - Sketches of `tokenSimple.enable` (`wp_fork`, the goroutine on its fork's token), `run` and
    `disable`.
  - `stop`'s only user is `disable`, which already posted `True`, so no statement depends on the
    removed token.
- Every changed file has a Changes line `verify-round (server-core's RR4 request)`.
- The caller's sketch: `etcdserver/NewServer.lean`'s RR4 Changes paragraph now says
  `NewTokenProvider` takes no token, so `NewServer`'s returned token is provable on every path
  (this replaces "not provable on the success path"). The statement is unchanged.
- The snippet `examples/specreq/auth/boot.go` needed no change: it never mentioned the provider's
  token.

### 2. The `leasehttp` handler contract gives the serving member's lessor view: **fixed**

- New in `lease/leasehttp/Api.lean`:
  - `leaseURLOf γ ep url` (opaque, persistent): the lease endpoint `url` is `NewHandler`'s, over
    the lessor of the member serving `ep`.
  - `ltlView url id found` (a definition, persistent):
    `□ ∀ γ ep i, leaseURLOf γ ep url -∗ leaseViewLb γ ep i -∗ ∃ j σ₀ t, ⌜i ≤ j ∧ σ₀.leaseTables[j]? = some t ∧ (t id).isSome = found⌝ ∗ etcdLb γ σ₀ ∗ leaseViewLb γ ep j`.
  - The module now imports `api/v3/State` (read only, no cycle).
- `TimeToLiveHTTP.spec`: the `200` reply also gives `ltlView url id true`, and the
  `ErrLeaseNotFound` reply gives `ltlView url id false`. Nothing new is needed in the premise: a
  caller without `leaseURLOf` gets nothing from the view.
- True of the handler (`http.go:109-160`):
  - it waits for `h.waitch()` (the server's `ApplyWait`), then `h.l.Lookup(id)` on its lessor's
    current table, which only moves forward, so the table is at or past any view the member gave
    before;
  - an absent lease gives `404`;
  - a demoted lease gives `500` (another error);
  - otherwise it answers `200`.
- With this, 2c's forwarded `TimeToLive` under `soleMember` closes `srvLeaseFact`'s row:
  - from `leaseURLOf` for the leader's (its own) URL, `etcdLb_reach` takes `σ₀`'s table `j` to the
    update's state;
  - `id' = id` comes from `ltlReply`.
- `leaseURLOf`'s source is a request to server-boot (below). Its use in 2c's assumed
  `leaseTimeToLive.spec` sketch is a request to server-core.

## grpc-v3rpc

### 1. `leaseFact` = `srvLeaseFact`: **fixed** (one definition)

- `v3rpc/Api.lean`: `leaseFact` is now an `abbrev` for `EtcdServer.srvLeaseFact`. The two bodies
  were identical, so no row changed. The docstring keeps the Go citations.
- `etcdUnary`'s optional bound is now written `srvLeaseLbOpt γ ep vi`, which is the same match as
  before.
- The header's round-1 bullet records both identifications.

### 2. `Server.spec` and the lease handlers only for the served endpoint: **fixed**; introduction requested

- `Server.spec`:
  - `ep` is now a binder, and the premise adds `srvAt s γ ep`;
  - the post is `∀ gq, regsOk B (etcdContract γ ep) (srvGate s gq)` (was `∀ ep gq`).
- The lease handlers take `srvAt s γ ep` in their handler premise `P`: `LeaseServer.{LeaseGrant,
  LeaseLeases, LeaseTimeToLive}` and `quotaLeaseServer.{…}`. It is persistent, and `Server`'s proof
  frames it into each registration.
- Their sketches:
  - they call 2c's lease spec at `srvAt`;
  - the contract's bound is passed as `srvLeaseLbOpt`, and 2c's `srvLeaseFact` comes back as the
    contract's `leaseFact`.
- The other handlers keep `∀ ep` and are instantiated at the served one.
- Snippet `examples/specreq/v3rpc/serve.go`: its Assumes now name `srvAt s γ ep`.
- **Introduction of `srvAt`**: the serving start must provide it, and I did not add a law. It needs
  an exclusive per-endpoint resource, and none of grpc's or net/http's fits:
  - `addrAt` is persistent;
  - `listenerAt` can be rebound;
  - `Http.addrFree` is spent once ever, by `Http.reserve`.

  A restart also complicates it: `s` is a fresh location in the new generation. Requested of
  server-boot below.

### 3. `KV()` sketches and `Config`: **fixed**

- `newHeader`, `header.fill` and `header.fillWithoutRevision` now go through `isServer_kv` (the
  persistent `s.kv ↦□ w` with `srvWatchable`), then `EtcdServer.KV.spec` at that points-to, then
  `w.Rev()`.
- `maintenanceServer.Status` notes that `Config.spec` is over `isServer`, which `maintAt` holds.
- Each of these files has a Changes line.
- No other v3rpc, api/v3 pb or grpc file cites `KV()` or `Config()`.

## Requests to server-boot

1. **Introduce `EtcdServer.srvAt s γ ep` at the serving start** (`etcdstart`'s `Serve`, embed's
   `serveClients`), before `v3rpc.Server`. `srvAt_agree` needs one member per endpoint, so the
   introduction must consume an exclusive per-endpoint right. A suggested shape, in `ApiBoot.lean`:
   `srvAt_reserve : Http.addrFree ep ∗ srvFields s γ id ⊢ |==> Http.protoAt ep P ∗ srvAt s γ ep`.
   Two variants would also work:
   - fold it into the reservation of the client URL;
   - a dedicated fractional right per endpoint.

   **Restarts:** a restarted member is a new `s` at the same `ep`, so `srvAt` must be
   per-generation (no `_gen` law) or keyed by the member id. That is for the crash-law agent to
   settle, together with whether W0's `leaseViewLb γ ep` survives a crash: after a crash, the
   backend's lessor may restart behind what was applied before it.
2. **Introduce `Leasehttp.leaseURLOf γ ep (u ++ "/leases/internal")`** for each of `s`'s own peer
   URLs `u`, from `srvAt s γ ep`, where embed's peer handler serves `leasehttp.NewHandler(s.lessor,
   s.ApplyWait)`.

## Requests to server-core

1. `EtcdServer__leaseTimeToLive.lean` (the assumed contract) and `EtcdServer.LeaseTimeToLive`'s
   sketch: the forwarding path, under `soleMember γ`, gets `srvLeaseFact`'s gated row from
   `TimeToLiveHTTP`'s new `ltlView`. It needs `leaseURLOf γ ep url` for the leader's URL (its own,
   under `soleMember`; server-boot's request 2) and `etcdLb_reach`. The assumed contract's post
   should carry that row (or a per-member view the gated row comes from), if it does not already.

## New decisions

- **No token for the token provider.** `NewTokenProvider` takes no `threadTok`, where the request
  asked for one returned on success. The keeper goroutine runs on its fork's own token (Perennial's
  `wp_fork`), so the provider's "reserved token" design (stored in the keeper field, given back
  through `donec`) was never needed and is removed. `keeper.stop` returns nothing.
- **The handler's view is gated on `leaseURLOf`, not a premise.** `TimeToLiveHTTP` stays usable
  with any URL. Only a caller that knows the URL is the serving member's own handler gets the
  lessor view. This keeps the trusted spec's assumption to what `leasePeerURL` already assumes.
- **`Server.spec` is per endpoint**, with `srvAt` as a premise and no introduction law yet. The
  alternative of keeping `∀ ep` was unsound for the lease rows.

## Build

- `etc/specs-build.sh --dir` on `api/v3rpc`, `etcdserver` (top level), `lease/leasehttp` and `auth`:
  **OK (370 modules)**, `Build completed successfully (2827 jobs)`, no errors. An earlier run of
  `auth` and `leasehttp` alone was OK (80 modules).
- `go vet ./specreq/v3rpc/ ./specreq/auth/` passes, and `gofmt -l` prints nothing.
