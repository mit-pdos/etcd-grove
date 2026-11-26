# F7 dist-axiom-diff review: the seven UNEXPLAINED premise drops (2026-11-26)

Reviewed read-only at `/shared/etcd-grove-f7`, branch `etcd-safe-f7` @ `9087d6d9ff`. Go: the pinned fork,
checked out at `/shared/tmp/coord-03/f7-s5-gotest/etcd`, toolchain go1.27.3.
Test: `/shared/tmp/coord-03/f7-distdiff-gotest/f7distdiff_lease_md_test.go` (a copy sits in the fork's
`tests/integration/`); output in `test-output.txt` beside it: PASS.

**Verdict: all seven SOUND.** In each case the dropped premise follows from premises the dist axiom
keeps, so the axiom claims nothing more in Lean. The one question about real etcd is whether the fixed,
metadata-free service specs hold for every context's metadata. They do: on these paths, metadata can
only produce an error.

## 1-6. The lease axioms: `metadata.outMD ctx om` and the binder `om` dropped

Affected: `Lease_Grant_dist`, `Lease_GrantLive_dist`, `Lease_LeasesGranted_dist`, `Lease_LeasesLive_dist`,
`Client_LeaseLeases_dist`, `Client_LeaseTimeToLive_dist`.

**Lean: the premise follows from what is kept.** Each dist axiom keeps `ctxOk ctx cd`, and
`ctxOk := (isContext ∨ ctxQuiet ∨ ctxErrs) ∗ metadata.outgoingCtxOkC ctx`
(`Proof/google_golang_org/grpc/InvGrpc.lean:443`). Also,
`outgoingCtxOkC ctx := ∃ md, metadata.outMD ctx md` (`Proof/context/LibKeysChain.lean`). So some `om`
with `outMD ctx om` always exists. In-process, `om` was used only by `attemptPre conn om Spec`, and that
went with the registration. No dist post mentions `om`. Dropping the binder and the premise is
therefore just eliminating the existential.

**Go: metadata cannot change a successful reply.** The dist posts use the metadata-free service specs
`etcdLeaseGrantSpecW`, `…LiveW`, `etcdLeaseLeasesSpecAnyW` and `etcdLeaseTTLSpecW`. Each error arm
claims only `err ≠ nil ∧ resp = null` (from `lessor.Grant/Leases/TimeToLive`, `client/v3/lease.go:222-272`:
`return nil, ContextError(ctx, err)`). So any error that metadata causes is allowed. Every place in the
fork that reads metadata on these paths was checked:

- **Server unary interceptor** (`server/etcdserver/api/v3rpc/interceptor.go:57-72`):
  - A non-UTF-8 `client-api-version` gives `ErrGRPCInvalidClientAPIVersion`, an error. The client's
    `withVersion` (`client/v3/ctx.go:40`) overwrites that key anyway, so a caller cannot set it.
  - `hasleader` with no leader gives `ErrGRPCNoLeader`, an error.
  - Nothing else in the interceptor reads metadata.
- **`token`/`authorization` keys**:
  - `AuthInfoFromCtx` (`server/auth/store.go:1076`) and `requireAuthInfo` (`v3_server.go:1278`) return
    nil/nil when auth is off.
  - `checkLeaseLeases` (`v3_server.go:752`) returns early when auth is off.
  - When auth is on (the axioms have no `Γ.auth = false` premise), these keys can only add
    `ErrInvalidAuthToken`, `ErrUserEmpty` or permission errors.
  - The reply's content (a non-zero id granted or live at member `mid`'s lessor, a list without
    duplicates, `ID = req.ID`) never depends on who called.
- **`LeaseTimeToLive` forwarded by a follower** (`v3_server.go:672`): the follower forwards over peer
  HTTP without the caller's metadata. The leader's reply sets `ID: r.ID`.
- **The client** reads outgoing metadata only in `WithRequireLeader`/`withVersion` (`ctx.go`), in watch
  (`watch.go:1103`) and in `KeepAlive` (`lease.go:390`). None of these is on the `Grant`/`Leases`/
  `TimeToLive` path.
- **The transport**: metadata does not change where the request goes. The connection is to `ep`,
  which `etcdAddrAt` ties to `mid`, with no proxy (`clientNoProxy`). grpc-go skips reserved headers;
  invalid keys or oversize headers give a grpc error, which falls in the error arm.

**Test** (3 members, auth off, each member in turn). Contexts tried: no metadata, `token: garbage`,
`authorization: Bearer garbage`, `WithRequireLeader`, `client-api-version: "\xff\xfe"`, and
`x-anything`.

- Every call succeeded:
  - `Grant` returned a non-zero id;
  - `Leases` listed that id with no duplicates;
  - `TimeToLive` returned the same id.
- With two members stopped, `WithRequireLeader` gave errors: `Leases` returned
  `etcdserver: no leader`, and `Grant` returned `context deadline exceeded`.

**Allow-file reason (one line):** `metadata.outMD ctx om` follows from the kept `ctxOk` (its
`outgoingCtxOkC` is `∃ md, outMD ctx md`), and `om` served only `attemptPre`, gone with the
registration. On the lease paths, metadata (`hasleader`, `token`/`authorization`, `client-api-version`)
only produces errors (the error arm claims nothing); reviewed SOUND in `f7-distdiff-review.md`, Go test.

## 7. `New_user_dist`: `clientAuthPre`'s `client.ctxErrClientAll` dropped

**What it guarantees in-process.** `ctxErrClientAll` says that for every `isContext` context, `Err()`
satisfies `ctxErrClient`: it returns nil or a client error (`clientErr`, `statusErrOk`, the context-error
shape). `New` needs it for `getToken`'s `Authenticate`, which calls `ContextError(ctx, err)` on the
client's own contexts. Those are `Background()`, because `clientCfgOk` forces `cfg.Context' = nil`, and
its `WithCancel`/`WithTimeout` children.

**Lean: a theorem, not an assumption.** `client.ctxErrClientAllW_of`
(`Proof/go_etcd_io/etcd/client/v3/ErrorsNewOk.lean:293`) derives it from three things:

- `isPkgInit pkg_id.context`, which follows from the kept `isPkgInit pkg_id.go_etcd_io.etcd.client.v3`
  by `iPkgInit`, as `dist/client/reqCtx.lean:39` does;
- `context.ErrAny.wp_proof`, a proved theorem (`Proof/context/ErrAny.lean:59`);
- `errors.AsTarget rpctypes.EtcdError.ty`, proved (`EtcdGrove.rpctypesEtcdError_asTarget`,
  `Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Init.lean:66`).

The auth examples already discharge it this way (`examples/etcd/auth/Run.lean:232`,
`authlease/run.lean:627`). So the dist `New` claims nothing more. The premise is true in every Go run,
because Go's contexts return `context.Canceled` (an `errors.New` error) or `DeadlineExceeded`, both
client errors. The dist `New` does not need it as a premise. A proof of `New_user_dist` from the
in-process `New` (#24's S2) gets it from `ctxErrClientAllW_of`.

**Allow-file reason (one line):** `client.ctxErrClientAll` is a theorem
(`client.ctxErrClientAllW_of`, from the kept `isPkgInit` of clientv3, which gives `context`'s, the proved
`context.ErrAny` and `rpctypesEtcdError_asTarget`): Go's contexts' `Err()` returns
`Canceled`/`DeadlineExceeded`, both client errors. Reviewed SOUND in `f7-distdiff-review.md`.

## Not tried / caveats

- Custom `Context` implementations whose `Value` misbehaves: `ctxOk`'s `outgoingCtxOkC` excludes them,
  in both the in-process and the dist axioms.
- With auth on, I tested only the auth-off case. The auth-on argument (metadata yields only errors)
  rests on reading the code and on the earlier `f7-s5` test (`TestF7S5LeaseAuth`, bad/anonymous tokens
  refused).
