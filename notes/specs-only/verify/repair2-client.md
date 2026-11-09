# Repairs after the second re-review: client-core (RR-1, RR1, RR2)

Group `client-core`, 2026-11-09. Findings from `verify/RR-client.md` (RR-1) and
`verify/RR-grpc-auth.md` (RR1, RR2). Part of the work (RR1 entirely, the `who' = who ∨ none`
restriction of RR2, and a first `soleMember γ ep` draft of RR-1 with no source) was already in the
WIP commit `41c6c3a39f`; this pass checked it, completed it and gave `soleMember` its source.

## Per finding

### RR-1 (1c): `examples/etcd/leaseexpiry` had no proof — **fixed** (as suggested: a gated row on a persistent single-member fact)

- **W0** (`api/v3/State.lean`):
  - `soleMember γ` is persistent and means "the cluster never has a member but its one initial
    member". It replaces the draft's `soleMember γ ep`: `ep` adds nothing, since if there is only
    one member ever, it is the one serving `ep`.
  - New `urlsReserve γ q` (fractional, `urlsReserve_fractional`): the right to reserve new
    peer-URL sets.
- **Source** (`etcdserver/ApiBoot.lean`): one law appended, `soleMember_intro`:
  `memberBoot γ [m] m ∗ urlsReserve γ 1 ⊢ |={E}=> memberBoot γ [m] m ∗ soleMember γ`, for a voter `m`.
- **Why no reconfiguration falsifies it while held:**
  - Every member addition (`MemberAdd`, `MemberAddAsLearner`, and so every promotion) takes a
    `urlsRight`. Only `urls_reserve` mints one.
  - With `urlsReserve γ 1` given up, no URL set was reserved before and none can be reserved after.
  - The intended realization is an invariant holding the whole share.
  - Removing the only member leaves no voter: raft refuses or panics
    (`nonissues/raft-remove-last-voter-panic.md`). So it removes answers; it adds none.
- **The gated row**, `soleMember γ -∗ ∃ j, ⌜i ≤ j ∧ leaseAnsAt j⌝ ∗ leaseViewLb γ ep j`. It is in
  both places:
  - 1c's `viaFact` (`client/v3/ApiClient.lean`);
  - 2a's `leaseFact` (`v3rpc/Api.lean`), as a new `.leaseTimeToLive` row.

  2a's `Leases` row also got the `⌜¬ leaseAnsRes res⌝ ∨` disjunct the client side already had. A
  fired `checkLeaseLeases` permission error has no `leaseAnsAt`.
- **Checked against the Go.** On a member that is the only member ever:
  - as leader, it answers from its own lessor after `waitAppliedIndex` (`v3_server.go:636-669`);
  - otherwise `waitLeader` returns itself, and it forwards to its own peer URLs. The `leasehttp`
    handler there looks the lease up in the same lessor (`:671-676`, `leasehttp/http.go:109-160`).
  - `Demoted` and the HTTP errors are not `leaseAnsRes`.
  - A found lease has `GrantedTTL > 0` (`leaseStep`'s `0 < gttl`). So the snippet's
    `GrantedTTL == 0` means not found.
- **The snippet** `clientv3lease/member.go` `ReqTTLGoneNotListedSole` closes, from:
  1. `TimeToLive`'s gated row at `ep`'s table `j ≥ 0` where the lease is absent;
  2. `Leases` at `j' ≥ j`;
  3. its Assumes (no re-grant).
- **Users.** `examples/etcd/leaseexpiry` gets `soleMember` from the `etcdstart.StartServer` boot
  (one member, `types.URLsMap{name: peer}`, no URL set reserved).
- **Docs updated:** `lessor__TimeToLive.lean`, `ApiLease.lean` and `LeaseServer__LeaseTimeToLive.lean`.
- **Two things still need other groups.** They are in the requests below:
  - `cluster_alloc` must give `urlsReserve γ 1`, and `urls_reserve` must spend a share;
  - 2c's lease specs give no per-member view at all, so `leaseFact` has no 2c source, for `Grant`
    and `Leases` either.

### RR1 (2a): `ReqMetadataOut` did not close — **fixed** (already in `41c6c3a39f`; checked)

- `FromOutgoingContext.spec` has the gated row `Context.ctxNoMeta ctx -∗ ⌜ok = false⌝`.
- **True of grpc** (`metadata.go:331-335` at the pinned grpc): the lookup `ctx.Value(mdOutgoingKey{})`
  gives `nil`, the type assertion fails, and the result is `nil, false`. I corrected the cited line
  numbers.
- `ctxNoMeta` is `□` (persistent), so the snippet keeps it for `outMD_noMeta`.
- With `mdAtN true` (`m = null`, `md = []`), the snippet's `ok || md != nil` check closes.

### RR2 (2a/W0): the widened `adminDenied` was vacuous in `who'` — **fixed** (as suggested, with `tls` threaded at 2a, not at W0)

- **W0** (`api/v3/Model.lean`):
  - `State.adminDeniedAs σ who' e`: the denial as the principal the check read.
  - `State.adminDenied σ who e := adminDeniedAs who e ∨ adminDeniedAs none e`. The compact step is
    unchanged in text.
  - The `none` case gives only `ErrUserEmpty`, and only when some table has auth on: the
    `AuthEnable` race. It is still admissible whenever auth was ever enabled, because a lagging
    member may apply the enable between the two reads. The docstring says so.
  - The certificate's name adds nothing at W0: the scope (`ctxPrin`, one identity per client)
    makes it `who`'s or none.
- **2a** (`v3rpc/Api.lean`):
  - `adminDenied σ who tls e := σ.adminDenied who e ∨ σ.adminDeniedAs tls e`;
  - new law `adminDenied_of`: `tls = none ∨ tls = who → adminDenied σ who tls e → σ.adminDenied who e`
    (the shape of 2c's `srvStep_step`).
- **`AuthAdmin.isPermitted.spec`** now returns `adminDenied σ who tls e`. That is true of the code:
  - `EtcdServer.AuthInfoFromCtx` gives the token's user when it reads auth on (`store.go:1072-1097`);
  - otherwise, or when there is no token, it falls back to `AuthInfoFromTLS` only under
    `--client-cert-auth` (`v3_server.go:1206-1215`). 2c's `tls` is none without the flag.
  - `IsAdminPermitted` then denies that principal (`store.go:915-936`).
- **`kvServer.Compact`**:
  - its sketch converts the denial with `adminDenied_of`, using `reqPrin_of_md`'s `tls = none ∨ tls = who`;
  - its Margin now states exactly what the model admits.
- **No other user** of `adminDenied` (the maintenance wrappers' sketches do not name it).
- `nonissues/etcd-admin-check-authenable-race.md`'s "Proof" section still says "any certificate
  user". That is a request below.

## Requests to server-boot (2e, `etcdserver/ApiBoot.lean`)

1. **`cluster_alloc.spec`**: add `urlsReserve γ 1` to the post, next to `srvNet γ ν`.
2. **`urls_reserve.spec`**: take a share, `urlsReserve γ q ∗ srvNet γ ν ∗ …`, and do not give it
   back (it is spent into the minted `urlsRight`).

Why: W0's `soleMember γ` (RR-1) is sound only if every `urlsRight` comes from a share of
`urlsReserve`. Then holding the whole share means none was or will be minted. A program that
reserves splits off a fraction; that costs nothing.

The appended `soleMember_intro` (at the end of the file, inside `section vocab`) needs these two
changes to have a source.

## Requests to server-core (2c)

1. **`EtcdServer.LeaseGrant` / `LeaseLeases` / `LeaseTimeToLive` give no per-member lease view.**
   2a's `leaseFact`, the source of 1c's `viaFact`, needs `leaseViewLb γ ep j` of the member's
   table:
   - for a grant, the table after it;
   - for `Leases`, the table the answer was read from, at or above the caller's `i`;
   - for `TimeToLive` under `soleMember γ`, the same.

   These specs are plain `SrvCallTriple`s whose `Q` does not carry it. A gated `TimeToLive` row is
   needed as well (`soleMember γ -∗ …`).

   This gap predates RR-1: `Grant`'s and `Leases`' rows had no 2c source either. Suggested fix:
   - a per-member variant of the success reply: `srvMember s γ id` with `servesAt`'s `ep`;
   - the lessor's applied table index, from 2d's view.

## Requests to the coordinator

- **`open-questions.md` A4**: record that the single-member alternative is now in place, as a gated
  row (`soleMember γ`, from `soleMember_intro`, with `urlsReserve`). The general per-member
  `TimeToLive` stays dropped.
- **`nonissues/etcd-admin-check-authenable-race.md`, "Proof"**: replace "no user or any certificate
  user" with "no user (`ErrUserEmpty`), or, at 2a only, the certificate's name `tls`, which W0's
  scope makes the principal's or none (`adminDenied_of`)".

## New decisions

**A single-member mode, introduced by giving up URL reservations (RR-1, A4).** To keep
`leaseexpiry`'s guarantee, `TimeToLive`'s per-member clause is restored as a gated row on a new
persistent W0 fact, `soleMember γ`. It is introduced by a new fractional W0 token, `urlsReserve γ`,
the right to reserve peer-URL sets, which 2e's `urls_reserve` is asked to spend.

- **Why this is the user's decision.** This is new client-visible ghost state. A program that
  reserves a URL set (to add a member) now needs a share of `urlsReserve`. The token is otherwise
  free.
- **The alternatives:**
  - a membership history in W0's model, which W0 declined for A4/A6;
  - dropping `leaseexpiry` from the Users lists, so that its final check is unproved.
- **Why simpler gates were rejected:**
  - A gate on the answer state's `members` is false. A removed leader keeps leading with
    `StepDownOnRemoval` off, so it can answer a forwarded `TimeToLive` from a lessor behind `ep`'s
    while `σ.members` is `[m]`.
  - A gate without a token has no source.

**The admin denial's principal (RR2).**
- W0's denial admits two readings:
  - the request's principal;
  - no principal, which gives `ErrUserEmpty` and only that. It is admissible whenever auth has
    ever been enabled, because a lagging member may apply the `AuthEnable` between the check's two
    reads.
- A root compactor can therefore be refused with `ErrUserEmpty`. It is never refused as another
  user.
- The certificate's principal (`--client-cert-auth`, the flag read off) is kept only at 2a, where
  `tls` is in scope. W0's scope (one identity per client) makes it the request's principal or
  none, so W0 does not need a `tls` argument.

## Build

`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/api/v3 Spec/go_etcd_io/etcd/client/v3
Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc Spec/google_golang_org/grpc/metadata
Spec/go_etcd_io/etcd/server/v3/etcdserver`: **OK (650 modules)**, no errors. The first run's final
check said FAILED only because a file changed while it was building (my edit of a comment's line
numbers); the rerun is clean.

The snippets are clean: `go vet ./specreq/{grpc,clientv3lease,clientv3kv,clientv3client}/` passes,
and `gofmt -l` prints nothing.
