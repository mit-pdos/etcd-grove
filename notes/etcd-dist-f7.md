# F7: auth and authLease across machines (design, 2026-11-26)

Stage F7 of `etcd_safe_nocrash` (#50; the lead's posts 2026-11-26T01:14:37Z/01:14:58Z): the auth-on split, the
auth interim axioms, then the `auth` and `authLease` workloads. Base `etcd-safe-m1-top/2026-11-25` @ `e2d102d97b`;
branch `etcd-safe-f7`. Design and drafts only: the drafts are `.spec` definitions in
`Proof/.../etcd/dist/AuthViewDist.lean` (imported by nothing, no axiom); nothing else changed.
Background: `notes/etcd-dist-plan.md` §18 (O1 option B, N2's drafts, §18.8 items 4–5), the single-process auth
proofs (`examples/etcd/{auth,authN,authlease}`, `client/v3/ResultsOn.lean`).

## The view

What the auth-on statements read, and where it lives (as §18.3's option B: Lean values fixed by the start):

- **The auth history `Γ.kv.hist`**: one name for the whole cluster, not per member. With auth on every member's
  `ρ.rd.kv.hist` is the head member's (`etcdstart.memberGOkOn`), and the history is the admin entries along the
  cluster's requested log `Γ.kv.rlog` (`histAu`, `admStates`). It's already a field of `KVNames`, so it joins
  `Γ` through `Γ.kv`, with no new field. `kvCongr` (what `Serve_dist` and restarts keep) leaves `hist` out, so the
  server side needs `kvCongr ρ.rd.kv Γ.kv ∧ ρ.rd.kv.hist = Γ.kv.hist` with auth on (`kvCongrOn`).
- **Per-member auth names `Γ.au : w64 → auth.AuthNames`** (new `DistView` field, a constant in `ofKV`), as
  `Γ.ls` for the lessor. Only the member-local facts read it: the member's published auth index
  (`auth.authPubLbM (.on (Γ.au mid)) n`, which a barrier gives and which a member-local lease check needs). It
  needs the Prove item **P-A1**: `NewServer.specG`/`specR` take `γa` from the caller (allocated by the start, as
  `allocNOn` does in one process today), with `E.authMode = .on γa` in the post in place of `∃ γa`. This is P-L1's
  pattern, and P-L1 and P-A1 should be done together.
- **The principal is the client's user name, not a token.** A token is the member's (the simple provider is
  per member, `<prefix>.<index>`), and a client may hold tokens of several members over its life. The contracts
  say only who a granted request was bound to: `userOk P hm.username` (the empty user, or the configured name
  `principalOf cfg`, read from `New`'s `cfg` field). So no token or `tokIssued` appears in any statement.
  At retirement the proof gets `userOk` from `tokIssued γa t name` (`Authenticate`'s password check) and the
  connection's `attemptTokOk`. A context that carries `token` metadata of its own is admitted only on an
  anonymous client, and only with values the simple provider never issues (`outTokOk`: authLease's `badtoken`).
- `T` (the TLS fallback, `srvTLSId`) is `False` here (`ClientCertAuthEnabled` false in `deployment`'s
  configuration), so it's dropped from every dist form. This is §18.8 item 5.
- `Γ.auth : Bool` stays the cluster's mode. Every auth-on draft takes `Γ.auth = true`.

## Auth-on writes: the persistent update

With auth on, clientv3's retry interceptor refreshes the token and resends a request that failed with
`ErrInvalidAuthToken`/`ErrAuthOldRevision` (`shouldRefreshToken`, `Client.unaryClientInterceptor`), mutable
ones included. A multi-endpoint user client also gets that error from every member but the one that issued
its token. So a write can reach raft more than once, and the update is offered to every attempt:
`□ kvAu1G Γ.kv (kvOpStep op) (opGrantD Γ.kv P op L₀) Q` (`writeAuD`). It still fires at most once
(`srvPropAu1`: one entry per attempt, each told its own grant), so `Q` is not persistent; the caller's
invariants must take any number of offers. That is the single-process proof's `□ clientOpAuOn`, and authlease's
cell uses only monotone authorities for this reason. `opGrantD` is `v3rpc.opGrantT` with `hdrBoundT T E.authMode
tok` replaced by `userOk P`: the stamped request is granted after a committed prefix `L ⊒ L₀` whose state is
the one the update fires at (`writeGrantG` verbatim).

## The axioms (drafts; each `X.wp_proof : X.spec` after a fresh `axiom` review, then a route-table row and the packet)

Each is a proved single-process client spec (column 3), with the member's registration replaced by the address
facts at `Γ` (`kvClientAt`/`authClientAt`). The member's own facts (`E`, `ρ`, the floor `F`, `pubAfterM`, the
token) are dropped, and the error arm claims nothing (`err ≠ nil ∧ resp = null`). The reason each is an axiom
is §18.4's, word for word (the cross-machine proof needs #24's S2 client side).

| Draft | Go signature | Mirrors | State |
|---|---|---|---|
| `New_user_dist` | `clientv3.New(cfg Config) (*Client, error)`, `cfg.Username`/`Password` set (`New` calls `Auth.Authenticate`) | `clientv3.New.spec`, `clientAuthPre`'s registration → `membersAt eps Γ`; post without `clientTokAt` | drafted (`AuthViewDist.lean`) |
| `KV_PutOn_dist` | `(*kv).Put(ctx, key, val string, opts ...OpOption) (*PutResponse, error)` | `client_put_on` (`etcdPutSpecOn`); lease `0` or revocable mode (authLease's `WithLease`) | drafted |
| `KV_GetOn_dist` | `(*kv).Get(ctx, key string, opts ...OpOption) (*GetResponse, error)` | `client_range_on`; linearizable only; check `readAuthedD` above the caller's `L₀` | drafted |
| `KV_DeleteOn_dist` | `(*kv).Delete(ctx, key string, opts ...OpOption) (*DeleteResponse, error)` | `client_delete_on` | drafted (S1) |
| `Txn_CommitOn_dist` | `(*txn).Commit() (*TxnResponse, error)` | `client_txn_on`; the grant of `irrTxn` (nested ops included) | drafted (S1) |
| `Auth_UserAdd_dist` | `(*authClient).UserAdd(ctx, name, password string) (*AuthUserAddResponse, error)` | `authClient.UserAdd.spec` at `etcdUserAddSpecW`; `histAu` at `Γ.kv`, `adminRepliedD` | drafted |
| `Auth_UserGrantRole_dist` | `(*authClient).UserGrantRole(ctx, user, role string) (*AuthUserGrantRoleResponse, error)` | as UserAdd | drafted (S1) |
| `Auth_RoleAdd_dist` | `(*authClient).RoleAdd(ctx, name string) (*AuthRoleAddResponse, error)` | as UserAdd | drafted (S1) |
| `Auth_RoleGrantPermission_dist` | `(*authClient).RoleGrantPermission(ctx, name, key, rangeEnd string, permType PermissionType) (*AuthRoleGrantPermissionResponse, error)` | as UserAdd | drafted (S1) |
| `Auth_AuthEnable_dist` | `(*authClient).AuthEnable(ctx) (*AuthEnableResponse, error)` | `authClient.AuthEnable.spec` | drafted |
| `Lease_GrantOn_dist` | `(*lessor).Grant(ctx, ttl int64) (*LeaseGrantResponse, error)` | `client_lease_grant_on`; `Γ.ls mid` (P-L1) | drafted (S1) |
| `Lease_RevokeOn_dist` | `(*lessor).Revoke(ctx, id LeaseID) (*LeaseRevokeResponse, error)` | `client_lease_revoke_on` (a write: `writeAuD`) | drafted (S1) |
| `Lease_TimeToLiveOn_dist`, `Lease_LeasesOn_dist` | `(*lessor).TimeToLive(ctx, id, opts ...LeaseOption)`, `(*lessor).Leases(ctx)` | the auth-on lease reads (`ServerLeaseRead`): member-local checks at `Γ.au mid`'s published index and `Γ.ls mid` | drafted (S1, `Lease_TimeToLiveKeysOn_dist`, `Lease_LeasesOn_dist`) |

**The refused calls get no axiom of their own.** Every auth-on success arm carries its check (a write's grant,
a read's `readAuthedD`, a lease check). A caller that holds the frozen history refutes it: after the set-up the
driver keeps the client's half of `authHistView Γ.kv hs`, as `akAuthFixed` does, so no admin entry commits
afterwards. So the success arm is `False` and `err ≠ nil` follows, as in `authlease/Refusals.lean`. The one
refusal outside this pattern is the refused `Watch` (a stream): it rides on F4's `Watch_dist`, auth-on form.

`KV_GetOn_dist` still needs, for a one-endpoint client of member `mid`, the barrier's floor (`auth.authPubLbM
(.on (Γ.au mid)) n` at the read's index) before authLease's member-local lease checks can be refuted. That is
added with `Γ.au` (step S2 below).

## S1 (2026-11-26): the drafts done, the lead's condition built in

All rows above are drafted in `AuthViewDist.lean`; the proposed `Serve_dist`/`NewServer_dist` texts are in
`AuthServeProposed.lean`; the review list is `notes/etcd-dist-f7-reviews.md`. Changes from the design above:
every success arm names the serving member (`servedBy eps Γ mid`) and its check (`writeCheckedD`,
`readCheckedD`, `leaseCheckD`, `adminRepliedD`, `New`'s `passwordChecked`); `writeAuD` takes `L₀` as a
parameter (the caller's `srvReqLogLb γR L₀` a separate premise); the client facts carry `cfg.Token' = []`;
`KV_GetOn_dist`'s floor is `authFloorD` (member `mid`'s published index, its state the history's after
`L ⊒ L₀`). **Correction to "The view":** a simple token is not only its issuing member's. The prefix is drawn
at the receiving member and proposed through raft, and every member's apply assigns the token to the same
user (`tokenSimple.assign`); only expiry (the TTL keeper) is per member. Stating the user, not the token,
is unaffected.

## Lifting `Hauth` and `Serve_dist`'s `Γ.auth = false`

- **`Serve_dist.spec`** (trusted text: re-review, in this batch): the pure premise `kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth =
  false` becomes `kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ (ρ.rd.kv.hist = Γ.kv.hist ∧ E.authMode = .on (Γ.au
  mid)))`, and `etcdstart.memberUp` becomes `if Γ.auth then memberUpOn … (Γ.au mid) Γ.kv.lm else memberUp …`.
  `etcdSvc`'s intended interpretation then says auth-on entries are the `etcd*SpecOn` handlers at `T := False`.
- **`NewServer_dist.spec`** (trusted text: re-review): P-A1's `γa` binder and `E.authMode = .on γa`. Its `on` is
  already a parameter (`on = true → cfg.AuthToken' = "simple" …`).
- **`member_boot_dist`** (N5, proof only): `Hauth` dropped. `MainLogger`'s `memberCfg_off` rewrite splits on
  `d.cfg.auth`. With auth on, `serverConfig` sets `AuthToken = "simple"` (`dist/server/server.go:131`, TTL 300 s),
  which `NewServer_dist` at `on = true` admits. `memberShareD` gains `Γ.au mid`'s fresh authorities (the start's
  `clusterAllocN` allocates them per member, with the cluster's `hist`, as `allocNOn`), and `kvCongrOn` from
  `memberBoot_of_slice`.
- **The top-level scope** (`kvremote/TopLevelRobustness`'s `d.cfg.auth = false`) is M1's statement and stays.
  `etcd_safe_nocrash` (F8) has no such conjunct, and the dispatch proves auth-on deployments through this lift.

## How the workloads link

- **`RunAuth`** (`dist/client/auth.go`): the orchestrator's share holds the client half of `etcdKV Γ.kv` and of
  `authHistView Γ.kv`, from the start, as putget's `putGetInvK`. `auth.SetUp` goes through the anonymous client
  `cli`: its Puts through `KV_PutOn_dist` (granted to anyone while disabled), its admin calls through `Auth_*_dist`
  with `akHist_setupAu`/`SetupInv` at `Γ.kv`. `barriers` is `New_user_dist` + `KV_GetOn_dist` per member. Then
  `akHistInv Γ.kv` and `akAuthFixed` (cluster-level now) go to the principals' machines (`remotePrincipals`,
  N7-kv's `NodeMain` dispatch); `auth.Work` is re-proved over the `On_dist` forms. Its pure checks
  (`Permitted`, `checkKVs`, `CheckHistory`, `Hist.lean`) are reused unchanged. Root's and u's `Watch`, and the
  refused watch, need F4's `Watch_dist` with auth on.
- **`RunAuthLease`** (orchestrator only): the same set-up and barriers, then `grantPut` (`Lease_GrantOn_dist`,
  `KV_PutOn_dist` with `WithLease`), the leased `Txn`, `noAuth`/`foreign` (refusals derived as above), `absent`
  (`KV_GetOn_dist`), and u's `Revoke`. authlease's cell (`Cell.lean`, `Holds.lean`) moves to `Γ.kv` and to
  `Γ.ls mid` through the per-member lessor law (`lessor_keys_of_read`), which needs P-L1.

## Order of work

1. **S1 (next session):** finish the drafts (Delete, Txn, the three admin calls; the lease-on four with F2's
   texts), and draft the `Serve_dist`/`NewServer_dist` edits. Fresh `axiom`-skill reviews of all of them in one
   batch, then route-table rows and the packet list on #50.
2. **S2:** P-A1 with P-L1 (`NewServer` takes `γa` and the lessor name). `DistView.au`, `kvCongrOn`, the start's
   per-member allocation; the `Serve_dist`/`NewServer_dist` edits as axioms once reviewed; `member_boot_dist`
   without `Hauth`; a full build. Nothing linked yet.
3. **S3:** `RunAuth` linked over the reviewed axioms (as hypotheses until adopted), after F4's auth-on `Watch_dist`.
4. **S4:** `RunAuthLease` linked, after F2's lease axioms and P-L1.
5. **S5:** both workloads into F8's dispatch.

## Risks

- **Watch dependency.** auth's two checks are watches, so S3 waits on F3/F4. authLease has no watch, so it can go
  first if F4 is late.
- **Size.** The single-process auth proofs are about 9k lines (`auth/`) plus authlease's. The port changes their
  names (`E`, `ρ`, `γa` → `Γ`), not their arguments, but `Work.lean`/`WorkCalls.lean` are long.
- **Principal by name.** This is sound only while no TLS identity binds a request (`T = False`), and only for
  contexts `outTokOk` admits. A deployment with `ClientCertAuthEnabled` would need `T` back.
- **The history outside `kvCongr`.** A restarted member must keep `hist`: this is a crash-line item (D6's
  analogue), not needed for `etcd_safe_nocrash`.
- **Trust growth.** About 14 new interim axioms, plus re-reviews of `Serve_dist` and `NewServer_dist`. Each
  axiom stays narrow: linearizable reads only, the workloads' call shapes, nothing claimed of an error.

## Open questions for the lead

1. Is it OK that `γa` joins `Γ` (`Γ.au`) but only the member-local reads read it, with principals stated by user
   name and no token in any statement?
2. Is it OK that the refused calls get no axioms (refutation of the success arm's check)? The refused `Watch` stays
   with F4.
3. The lease-on forms (Grant, Revoke, TimeToLive with keys, Leases) belong to F2's or F7's batch? Proposed: drafted
   in F2's vocabulary, reviewed in one batch with F7's.
4. Who writes `Watch_dist`'s auth-on form (refusal, and u's permitted-keys check): F4 (yours) or F7?
5. Should P-A1 be done together with P-L1 (one `NewServer` change, one re-review of `NewServer_dist`)?

## Handoff (S1, 2026-11-26, second part: drafts compiled)

- **Build**: `AuthViewDist` and `AuthServeProposed` compile at `5cb43bae2f` (fk-lean2, `~/eg/wt/etcd-safe-f7`,
  log `~/eg/logs/f7-build.log`: no error in either module).
- **Distinct names**: every draft that reads per-member names (`New_user_dist`, `Txn_CommitOn_dist`,
  `KV_GetOn_dist`, the four `Lease_*On_dist`, `Serve_dist_proposed`) takes `∀ a b : w64, A a = A b → a = b`,
  and the three lease drafts that read `Γ.ls` also `∀ a b : w64, Γ.ls a = Γ.ls b → a = b`
  (`Lease_RevokeOn_dist` reads no `Γ.ls`). That is the lease review's form (`rev-f2-report.md`, "The fix").
  F2 had not pushed its premise (`etcd-safe-f2` @ `00544657aa` has no `Γ.ls a = Γ.ls b`). The form is over
  every `w64`, not a member set, because `DistView` has none. The start can meet it by completing its
  per-member allocation with names it never owns. Align with F2's form once F2 lands it.
- **`authNamesFreshD`** (`AuthServeProposed.lean:58`) is complete: one fresh authority per `auth.AuthNames`
  field, at the values the server's boot allocates today (`authHist_alloc`, `authBoot_alloc`, `tokAlloc`,
  `srvTpInv_alloc`). It does not cover the provider's keeper map `γk` (not an `AuthNames` field) or the
  backend's names.
- **Review list** (`notes/etcd-dist-f7-reviews.md`): line numbers updated, plus a "Distinct names" check.
  It is ready for the batch of fresh `axiom`-skill reviews.

## Reviews applied (2026-11-26; `notes/axiom-review/f7-{a,b,c}.md`, ledger entries of 2026-11-26)

Three independent `axiom`-skill reviews of the S1 drafts (groups A: client KV calls, B: admin calls, C: lease
calls and the proposed `NewServer`/`Serve`). The coordinator decided the fixes, and they are applied:

- **Free auth names (A, C F1: unsound).** The binder `A` is dropped. `DistView` gains `au : w64 → auth.AuthNames`
  (`S2Interim.lean`), and `ofKV` sets it to a constant until P-A1's start (it fails the distinct-names premises,
  so no draft applies to an `ofKV` view). Every draft reads `Γ.au mid`. `Serve_dist_proposed` (no `A` parameter
  now) requires, with auth on, `etcdstart.memberUpOnL … (Γ.au mid) Γ.kv.lm (Γ.ls mid)`, whose exclusive member
  resources tie `Γ.au mid` to the real member. The distinct-names premises are kept, over `Γ.au`. They are now
  redundant but harmless.
- **The lessor (C F2).** `Serve_dist_proposed` requires the member's lessor at `Γ.ls mid` at the lease mode
  `Γ.kv.lm` in both modes. With auth on that is `memberUpOnL` (`AuthServeProposed.lean`: `memberUpOn`'s body
  plus `mvccLeases E.γ = γl`). With auth off it is F2's `memberUpL`: `MemberLessor.lean` is copied verbatim from
  `etcd-safe-f2` (`54fa3c9780`) and will merge cleanly. F2's `Serve_dist.spec_proposed` has the same lessor part,
  so the two are reviewed together. `Lease_TimeToLiveKeysOn_dist` gains `Γ.kv.lm = .revocable`.
- **`Auth_UserAdd_dist` (B).** `name.length ≤ backend.maxKeySize` is added to its pure precondition, and the update
  is `□ (∀ um, ⌜…⌝ → histAu …)`. The over-long-name `lg.Fatal` is `issues/etcd-auth-useradd-long-name-fatal.md`.

## Handoff for S2 (2026-11-26)

- **P-A1 must thread `γa`'s names into the provider and readiness proofs** (review C's note):
  `AuthSrvLinked.lean:131` today allocates the token names (`tok`, `fresh`) and the readiness cell (`rdy`) inside
  `NewServer`. With P-A1 they come from `authNamesFreshD γa`, so the simple provider's construction
  (`newTokenProviderSimple`, `tokAlloc`) and `srvTpInv_alloc` must take them as parameters. Do this with P-L1.
- **Re-review `authFloorD`'s alignment** (review A): `authStateAt (Γ.au mid) i` (the member's history index)
  vs `srvAuthAtLog Γ.kv srvAuthSt0 L` (over the requested log, no raft fillers).
- **The starts** (`ClusterNames.view`, putgetk's `ofKV`) must allocate `Γ.au` per member, completing the map
  off the members with names they never own, before any auth-on draft becomes an axiom.
- `Auth_UserAdd_dist`'s `um` premise is still `um.name = name ∧ um.noPassword = false` (no `um.pwSure`, which the
  mirror `etcdUserAddSpecW` has). That asks more of the caller, which is sound. Relax it to the mirror's only if
  a caller needs it (`SetupInv`'s `hj` takes `pwSure`).
- **Build (2026-11-26): green.** Built on fk-lean2 at `b16ade2108` (`~/eg/wt/etcd-safe-f7`; client log
  `/shared/tmp/f7-build2.log`): `lake build` exit 0 (11686 jobs), no error. The targets were the importers' leaves of
  `S2Interim`/`MemberLessor` (`/shared/tmp/f7-leaves.txt`), among them `AuthViewDist`, `AuthServeProposed`,
  `kvremote.TopLevelRobustness` (M1's statement, unchanged), `putget.TopLevelRobustness` and `putgetk.Start`.

## F2 merged, one proposal (2026-11-26)

- `etcd-safe-f2` @ `54fa3c9780` merged into `etcd-safe-f7`. `MemberLessor.lean`: one copy (F7's was F2's verbatim).
- **One `NewServer.specG_dist_proposed`** (`AuthServeProposed.lean`): F7's `γa`/`"Hγa"`/`E.authMode = .on γa` and F2's
  `γl`/`"Hlslot"`/`mvccLeases E.γ = γl` (re-review C's N1). F2's copy in `Spec/.../dist/NewServerDist.lean` deleted
  (the file is back to the current axiom's text).
- **One `Serve_dist_proposed.spec`** (`AuthServeProposed.lean`): F7's, with the distinct-`Γ.au` premise guarded by
  `Γ.auth = true →` (N2), and the docstring stating condition C and the restart limit. F2's
  `Serve_dist.spec_proposed` in `Spec/.../dist/ServeDist.lean` deleted.
- **`readCheckedD`** gives `srvReqLogLb γR L` for `readAuthedD`'s `L` (re-review A's N1).
- Ledger: three entries of 2026-11-26 ("combined", "one proposed `Serve_dist`", "`readCheckedD`"). Review list:
  rows 5, 15, 16, 19 updated, row 20 (the combined proposal) awaits one fresh re-review before S2 adopts it.

## Handoff (2026-11-26, after the F2 merge; context limit)

- **Build: green** (`lake build` exit 0, 11721 jobs, no error; finished after the handoff was first written). fk-lean2, `~/eg/wt/etcd-safe-f7` at `9a3a07ef29` (detached), script
  `~/eg/logs/f7m-build.sh` (flock `~/eg/.build.lock`, MemoryMax=55G), log `~/eg/logs/f7m-build.log` (ends `EXIT n`).
  Targets `~/eg/logs/f7m-leaves.txt` (= `etc/importers.py --leaves` over `S2Interim`, `MemberLessor`, `NewServerDist`,
  `ServeDist`, `AuthViewDist`, `AuthServeProposed`, `kvremote/TopLevelRobustness`, `client/RunLease*`: 24 leaves).
  The Get and Txn drafts (`AuthViewDist`) typecheck with the new `readCheckedD`.
- `etc/tier-check.py --check`: ok (208 known violations, none new).
- Combined proposals: `NewServer.specG_dist_proposed` at
  `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthServeProposed.lean:104`, `Serve_dist_proposed.spec` at
  `:283` (same file).

## F2/F7 start side: the gate, L1, L2 (2026-11-26; the coordinator's widened brief)

**Done** (branch `etcd-safe-f7`):
- **The ordering gate** (first, as the lead asked): `etc/lease-order-check.py`, in `etc/gates.sh`'s source section with
  its self-test. Rule: every `axiom … .wp_proof` whose `.spec` serves etcd's table (`etcdAddrAt` with
  `etcdstart.memberUp`/`memberUpOn`) must mention `Γ.ls mid`; while one does not, no module may import (directly or
  not) a module declaring one of the six `Γ.ls`-reading lease axioms. An import is a link: the six are imported by
  nothing today (their users take their specs as hypotheses). Source only, ~6 s. Today: `Serve_dist` does not tie,
  nothing imports the six, so `lease-order: ok`; the self-test checks that a synthetic link fires it.
- **L2:** `lease.lessorSlot_alloc E used` (`LessorSlot.lean`): a lessor name outside `used` (strong allocation, for the
  start's injective `ls`), its half at `∅` and its slot. `newLessor_alloc` now calls it.
- **L1:** `etcd_dist.authNamesFreshG_alloc` (`dist/MemberNames.lean`): fresh auth names with their authorities, from
  `authHist_alloc`, `tokAlloc`, the rights' empty map and a mono-nat. `authNamesFreshG` is `authNamesFreshD`'s body at
  `[AllG GF]` (the proposal's is at a `HeapGS`, which the start, over `GooseGlobalGS`, does not have);
  `authNamesFreshG_iff` proves them equal at a `HeapGS`. When the proposal is adopted, state `NewServer_dist`'s
  `"Hγa"` with `authNamesFreshG` (or define `authNamesFreshD` at `AllG`) so that `memberShareD` can carry it.
- Built on fk-lean2 (`MemberNames`, `NewLessorAlloc`: exit 0).
- Packet rows: `notes/etcd-dist-f9-f2f7-rows.md`.

### Replacing the two axioms: the conflict (not done; for the lead)

Replacing `Serve_dist` by `Serve_dist_proposed` and deleting the current one breaks two other results on the branch,
which serve through `Serve_dist` with `memberUp` from an **in-process** start:
- **putget** (`putget/Member.lean:53`, `wp_Serve_dist`; `putget/AdequacyMember.lean:161` passes
  `etcd_dist.Serve_dist.wp_proof`): its member gets `memberUp` from `etcdstart.StartServer.spec` (proved, over the
  in-process `NewServer.specG`, whose lessor name is `NewServer`'s own: `∃` in the post).
- **putgetk** (`putgetk/Member.lean:221`; `AdequacyMember.lean:213`): its member gets `memberUp` from the hypothesis
  `etcd_dist.StartMember_dist.spec` (`Spec/.../dist/StartMemberDist.lean:90`, the post
  `∃ γn, memberUp s ρ E₀ lg γn id lm`), a premise of putgetk's results (`putgetk/Start.lean:152,196`).
The proposed `Serve_dist` needs `memberUpL … (Γ.ls mid)`, i.e. `mvccLeases E.γ = Γ.ls mid` for a name the start fixed in
the view before the member ran. Neither in-process route gives that:
- putget needs the in-process `NewServer.specG` carried to a caller's `γl` (f7-combined.md §1's retirement obligation:
  a `specG` variant whose proof calls `lease.NewLessor.specAt`, through `NewServerAlloc`/`StartServer`), plus the slot
  in putget's start (`memberShare`);
- putgetk needs `StartMember_dist.spec`'s post changed to `memberUpL … γl` with the slot in its pre: a change to a
  premise of putgetk's top-level results.
M1 is not affected this way: its member (`server/MainLogger.lean`) calls `NewServer_dist`, whose proposed post gives
`mvccLeases E.γ = γl`. **Options:** (a) carry the in-process `specG` to the name and change `StartMember_dist`'s text
(putgetk's statement changes); (b) retire putget/putgetk's results (superseded by M1's) in the replacement commit;
(c) keep them on a branch that does not take the replacement. Stopped here for the lead's choice.

### L3/L4: the plan (not started)

- `ClusterNames` gains `ls : w64 → GName` and `au : w64 → auth.AuthNames`; `ClusterNames.view := ⟨c.γk, c.ls, false,
  c.au⟩` (`Γ.kv = c.γk` and `Γ.auth = false` stay `rfl`, which is all `MainLogger`/`MembersStart` use:
  `MembersStart.lean:102`, `MainLogger.lean:155`). Every anonymous constructor `⟨γ, γk, …, reg⟩` (ClusterStart,
  ClusterStartD, putget/putgetk starts, StartOneSlice) gains the two fields; the starts that do not allocate (putget,
  putgetk, `etcdClusterStart`) may pass constants as `ofKV` does, since nothing they link reads them.
- `memberShareD` gains `ghostMapAuth (c.ls id) ½ ∅ ∗ lease.lessorSlot (c.ls id) ∗ authNamesFreshG (c.au id)` and the
  pure facts `(∀ a b, c.ls a = c.ls b → a = b) ∧ (∀ a b, c.au a = c.au b → a = b)` (the lease axioms' premise and
  the proposed `Serve_dist`'s guarded one). Not `memberSliceOf`: putget and StartOneSlice use it too.
- `clusterStartD` allocates them after `clusterAllocN`, by induction over `d.ids` (nodup): `lessorSlot_alloc` with
  `used` the names so far, `authNamesFreshG_alloc`; distinct `hist` names from exclusivity
  (`monoListAuthOwn_exclusive`). Injective over all `w64` by padding: for a non-member `x`,
  `ls x = B + uint.nat x` with `B` above every member's name (e.g. one plus their sum), and `au x` the record with
  every field `B' + uint.nat x` (`hist` decides `au`'s injectivity).
- `MainLogger` passes `"Hlslot"` to `NewServer_dist` (once replaced) and drops `authNamesFreshG` (auth off: `"Hγa"` is
  `True`); with the post's `mvccLeases E.γ = γl` it builds `memberUpL` (`MemberLessor.lean`) for `Serve_dist`.
- M1's statement (`Spec/.../kvremote/TopLevelRobustness.lean`) names none of these (`∃ c, memberShareD …` is in the
  proof file): it stays unchanged.

### L5: the auth-on deployment path (design only)

What the start and the member need for `d.cfg.auth = true`:
1. **Configuration.** `AdequacyMember`'s `Hauth : d.cfg.auth = false` and `memberCfg_off` get an auth-on counterpart
   `memberCfg_on`: `memberCfg` already sets `AuthToken' := "simple"`, `TokenTTL' := 300` when `Auth'`
   (`MemberDefs.lean`), which meets `NewServer_dist`'s `on = true → AuthToken = "simple" ∧ 0 < TTL < 2^32`.
2. **The KV names at `on = true`.** `clusterAllocN` allocates `kvInvM false …` and `ch0 = alarmChain false false false`;
   with auth on it must allocate `kvInvM true ρ.rd.raft ρ.rd.kv srvAuthSt0` with `ch0 = alarmChain true …`, and one
   cluster history name `Γ.kv.hist` that every member's `ρ.rd.kv.hist` equals (`Serve_dist_proposed`'s
   `Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist`; `kvCongr` leaves `hist` out). `ClusterOk` then takes `on`.
3. **The member's auth names.** `authNamesFreshG (c.au id)` from `memberShareD` (L1/L4), turned into `authNamesFreshD`
   (`authNamesFreshG_iff`) for `"Hγa"`; `c.au` injective (L4's padding) for the guarded premise. The view's `auth` field
   becomes the deployment's: `ClusterNames.view` takes `d.cfg.auth` (or `ClusterNames` gets an `auth` field).
4. **No TLS identity.** `memberUpOnL` needs `□ (srvTLSId s -∗ False)`: from `NewServer_dist`'s post
   `srvCfgFieldAddr srv "ClientCertAuthEnabled" ↦□ cfg.ClientCertAuthEnabled'` and the deployment's configuration
   setting it `false`.
5. **`memberUpOnL`** built as authkv's `startServer` does (`memberUpOn_intro`'s parts), plus `mvccLeases E.γ = γl`.
Statements: no `TopLevelRobustness` statement changes. M1's (`kvremote`) keeps `Hscope : KvOnly d ∧ d.cfg.auth = false`;
the full `etcd_safe_nocrash` statement has no auth scope, and L5 is what lets its proof drop `Hauth`. The auth-on
workloads' statements (`auth`, `authLease`) are F7's new ones.

### Handoff (2026-11-26, this session; context limit)

- Head: see `git log -1 etcd-safe-f7`. Built: the gate (source-only, ok), L1, L2.
- Next: the lead's choice on the conflict above; then the replacement commit (both axioms, the current `Serve_dist`
  deleted, `axiom-tok-allow.txt`'s `Serve_dist` entries re-keyed to the new spec, `tcb-baseline.txt` unchanged in
  names), L3/L4 as planned, the M1 member (`MainLogger`) fixed; then link leaseRead/leaseCatchup/leaseExpiry as
  N7-kv linked kv (the gate then passes because `Serve_dist` ties `Γ.ls mid`), and `etc/tcb-report.py --check --update`
  plus the collections for exactly the six lease axioms.
- Build: fk-lean2, `~/eg/wt/etcd-safe-f7` (detached at the pushed head), script `~/eg/logs/f7l-build.sh MODULES…`
  (flock, MemoryMax=55G), log `~/eg/logs/f7l-build.log`.

### Handoff 2 (2026-11-26, L3/L4 written, build running; context limit)

**Done (unbuilt when pushed; the build was running):** L3/L4 at `a6605a2dad`.
- `ClusterNames` gains `ls : w64 → GName`, `au : w64 → auth.AuthNames`. `ClusterNames.view := ⟨c.γk, c.ls, false, c.au⟩`.
  `ClusterNames.lsNone`/`auNone` are the constants (`ofKV`'s), passed by `etcdClusterStart` (putgetk) and `putget_shares`.
  `ClusterNames.NamesInj` is injectivity of both over all `w64`.
- `MemberDefs.memberNamesShare γl γa` (half of `γl`'s map at `∅`, `lessorSlot γl`, `authNamesFreshG γa`). `memberShareD`
  gains `c.NamesInj` in its pure conjunct and `memberNamesShare (c.ls id) (c.au id)` as its last conjunct.
  `MainLogger` drops both for now (`-` in its `icases`/`obtain`).
- `ClusterStartD`: `lsPad`/`auPad` (padding of non-members above every member's name; `lsPad_inj`, `auPad_inj`), `hists_ne`
  (exclusivity of the history authority, resources kept), `memberNames_alloc_list` (induction over the nodup ids:
  `lessorSlot_alloc` outside the names so far, `authNamesFreshG_alloc`), `memberNames_alloc` (padded), `names_members`;
  `memberShares_of` takes `Hinj` and the names list; `clusterStartD` allocates after `clusterAllocN`.
- M1's statement text is untouched (`memberShareD` is named, not unfolded, in `kvremote/TopLevelRobustness.lean`'s spec).

**Build:** fk-lean2, `~/eg/wt/etcd-safe-f7` (detached at `a6605a2dad`), log `~/eg/logs/f7l-build.log` (ends `EXIT n`).
Targets: `dist.server.ClusterStartD`, `dist.server.MainLogger`, `dist.kvremote.TopLevelRobustness`, `dist.putget.TopLevelRobustness`,
`dist.putgetk.TopLevelRobustness`. **Result: EXIT 1.** Every error is in `ClusterStartD.lean`, and everything up to it built
(`ClusterStart`, `MemberDefs`, `MemberNames`):
- `lsPad_inj`/`auPad_inj` (lines 98-112): `omega` fails and `simp` makes no progress. Probably `uint.nat` is opaque to
  `omega` (use `word`, or unfold `uint.nat` to `toNat`), and `simp only at this` is a no-op.
- `hists_ne` (line 274): `iunfold memberNamesShare` fails in the IPM. The definition comes from `MemberDefs` under
  `etcd_dist`; try `unfold memberNamesShare authNamesFreshG` before `icases`, or `iunfold` on a fresh hypothesis.
- `memberNames_alloc_list`: line 304, the `⟨fun a h => by cases h, …⟩` of the nil case (use `List.not_mem_nil`); lines 329-346,
  the cons step's pure part and the `bigSepL_mono` conversion.
`MainLogger` and the `TopLevelRobustness` targets were not reached.

**Next:**
1. Fix any L3/L4 build errors (likely spots: `simp only [... if_true, if_false]` in `lsPad_inj`/`auPad_inj` and the cons step
   of `memberNames_alloc_list`; `rw [hx] at *` in `hists_ne`; `imod` of the `|==>` from `authNamesFreshG_alloc`;
   `lessorSlot`'s section instances in `MemberDefs`). Then run `etc/tier-check.py --check` and `etc/lease-order-check.py`.
2. The putget carry (proof-only). `NewServer.wp_proofG` (`Proof/.../etcdserver/NewServer.lean:208`) calls `h24 :
   lease.NewLessor.spec` at line ~721. The lessor's name is `γl`, and `Hγl : mvccLeases γm = γl` at ~876; `E.γ = γm`.
   Plan:
   - Add `NewServer.specGAt` (specG plus a binder `γl`, the premise `"Hlslot" ∷ ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl`,
     and the post `mvccLeases E.γ = γl`).
   - Rename the proof to `wp_proofGAt`, with `h24 : lease.NewLessor.specAt` (`lease.NewLessor.wp_proofAt` exists).
   - Derive `wp_proofG` by allocating the slot first (`lessorSlot_alloc` at `hG.goose_globalGS`).
   - Link: `etc/link-lean-first-server.txt:993` `lease_NewLessor` → an At entry. `lease_NewLessor: lease_newLessor` at
     line 764 needs an At counterpart; check how `gen-link.py` names a variant's spec.
   - Then `etcdstart.StartServer` gets a `specAt` in the same way.
   - putget's `memberShare` (`putget/Defs.lean:67`) carries `memberNamesShare`, and `putget_shares` allocates with
     `memberNames_alloc [id]`.
   - putget's member builds `memberUpL … (Γ.ls mid)`. putget's result statements stay unchanged.
3. The replacement commit (the lead, #50 03:05Z):
   - `NewServer_dist` and `Serve_dist` take the proposed texts (`AuthServeProposed.lean`).
   - The current `Serve_dist` is deleted.
   - putgetk follows (a): `StartMember_dist.spec`'s post (`Spec/.../dist/StartMemberDist.lean:90`) becomes
     `memberUpL … Γ.kv.lm (Γ.ls mid)`. It is the hypothesis `HSM` of `putgetK_safe_of_S5` (`putgetk/Start.lean:392`),
     not a top-level change.
   - `MainLogger` passes `memberNamesShare`'s parts to `NewServer_dist` and builds `memberUpL`.
   - `axiom-tok-allow.txt` is re-keyed.
4. Link leaseRead, leaseCatchup and leaseExpiry. Update the tcb baseline and collections for exactly the new axioms. Run
   `etc/lease-order-check.py`, `etc/tier-check.py --check` and `etc/tcb-report.py --check`.

### Handoff 3 (2026-11-26, L3/L4 built; step 2's NewServer layer written; context limit)

**Done:**
- **Step 1, built** (`b676473728`, fk-lean2, EXIT 0 on `ClusterStartD`, `MainLogger`, the three dist `TopLevelRobustness`):
  `ClusterStartD`'s fixes. `GName` is `abbrev Nat`, and `omega` drops an `Eq GName` hypothesis, so `lsPad_inj`/`auPad_inj` go
  through `lt_add_one_add` and `Nat.add_left_cancel`. `iunfold` takes one name (`iunfold A at H`, then `iunfold B at H`).
  `hists_ne` uses `subst hx`. The allocation's induction step decides `a = x`/`b = x` with `by_cases` (no `rcases … rfl`,
  which re-introduced the shadowed `ha`). No `Spec/` file changed since `9e7c7a4442`, so M1's `etcd_kv_safe_nocrash` statement
  is untouched. `etc/tier-check.py --check` ok; `etc/lease-order-check.py` ok.
- **Step 2, NewServer layer (`d3c3a29b87`):**
  - `NewServer.specGAt` (Spec `NewServer.lean`, after `specG`): `specG`'s text with its comments dropped, the binder `γl` after
    `m`, `"Hlslot" ∷ (ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl)` FIRST in the pre (so that `pre_At = Hlslot ∗ pre_G`), and
    `mvcc.api.mvccLeases E.γ = γl` as the post's last pure conjunct.
  - `NewServer.wp_proofGAt` (was `wp_proofG`): `h24 : lease.NewLessor.specAt`, called at `γl` with `Hlslot`; the post's pure
    adds `Hγl` (mvcc `New`'s `mvccLeases γm = γl`).
  - `NewServer.wp_proofG`: derived (`lease.lessorSlot_alloc ⊤ []`, then `wp_proofGAt`). Its `h24`, and `wp_proofM`'s and
    `wp_proof`'s, is now `lease.NewLessor.specAt`.
  - Link: `lease_NewLessor+At: lease_newLessor+At` and `lease_newLessor+At: …` in `etc/link-lean-first-server.txt`, and
    `etcdserver_NewServer` takes `lease_NewLessor+At`. `Link.lean` regenerated (`etc/gen-link.py --server`).
  - Build: the first build of `d3c3a29b87` failed in the derivation only (a docstring before `set_option … in`; `imod` of
    `lessorSlot_alloc (Gg := hG.goose_globalGS)` under the WP is "not a modality": the `fupd` instances differ, so the
    allocation is first restated at the section's instances, `have hA : ⊢ |={⊤}=> … := lease.lessorSlot_alloc (Gg := …) ⊤ []`;
    the pre's `Hpkg` is split off by `wp_start_folded`). Fixed in the head commit; `etc/lean-check.py --fast` reports the
    derivation clean, but `wp_proofGAt`'s body and the Link are NOT yet built. **First thing next:** on fk-lean2,
    `~/eg/logs/f7l-build.sh Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServer Proof.go_etcd_io.etcd.server.v3.etcdserver.Link`
    plus the three dist `TopLevelRobustness` (sync the worktree to the branch first: fetch into `~/eg/etcd-grove.git`,
    `git checkout -f --detach etcd-safe-f7` in `~/eg/wt/etcd-safe-f7`). Likely spots in `wp_proofGAt`: the `h24` call's
    `$$ [Hopen Hwl Hrbo Hlslot]` and the new `isplitr … iexact Hlslot` at its pre's end, and `⟨hγs, HM.1, HM.2.1, Hγl⟩`.

**Next, step 2's remaining layers** (no statement of putget's results changes):
- `etcdstart.newServerMode` (`Proof/.../lib/etcdstart/newServerMode.lean:87`, `wpNS : NewServer.specG false cmp`) →
  a `newServerMode.specAt` over `NewServer.specGAt`, its post's built member carrying `mvccLeases E.γ = γl`.
- `etcdstart.newServer` (`newServer.lean`) → `specAt`, the same.
- `wp_Start_built` (used by `StartServer.wp_proof`) → its result `memberUpL … γl` from a built member carrying the fact
  (`memberUpL` is `memberUp` plus `mvccLeases E.γ = γl`, `dist/MemberLessor.lean`).
- `etcdstart.StartServer.specAt` (pre plus the half and the slot at `γl`; post `memberUpL … lm γl`), its proof as
  `StartServer.wp_proof`; then `wp_StartServer1`/`etcd_dist.wp_StartServer1_slice` At variants.
- putget: `memberShare` (`putget/Defs.lean:67`) carries `memberNamesShare (c.ls id) (c.au id)`; `putget_shares` allocates with
  `memberNames_alloc [id]`; `putget/Member.lean` calls the At start and gets `memberUpL … (c.ls id)`.
- Link entries for each `+At` (gen-link's `<fn>+At` → `<fn>.specAt`/`wp_proofAt`, the etcdstart list).

**Then steps 3 and 4 as in Handoff 2**, with the lead's request of #50 03:09Z (via the coordinator):
- The replacement `NewServer_dist` carries `specG`'s `etcdURLsFit U.peer → etcdURLsFit U.client →` (after `peerURLsDir`), which
  `specG_dist` and the proposed text dropped; discharge them at the start from `addrFits` and one URL per member, as M1 does
  (take M1's version if it is pushed by then; `etcdstart.etcdURLsFit_httpURL`, `etcd_dist.addrOk_addrFits`).
- The mechanical diff of every new or replaced dist axiom against its in-process spec: `notes/axiom-review/f7-diff-vs-inprocess.md`
  (written, uncommitted review aid, in the head commit). Its findings: (1) `NewServer_dist` and the proposed text drop
  `etcdURLsFit U.peer/U.client` (to be carried, above); (2) `StartMember_dist` (putgetk's placeholder hypothesis) also drops
  `addrFits peerAddr → addrFits client →`, unlisted in its "What changes": carry it in step 3's `StartMember_dist` edit;
  (3) the current `Serve_dist` ties nothing to `Γ.ls mid` (known, F2; the proposed text fixes it). Docstring nits in
  `AuthServeProposed.lean`: "the in-process `NewServer.specG` is not yet carried to the name" is stale (`specGAt`), and
  "distinct-names premises (kept here too)" holds only of the auth names.

### Handoff 4 (2026-11-26, step 2 carried; step 3 prepared, held for the putgetK verdict)

**Done:**
- **Step 1, built** (fk-lean2, `ce6319f67f`): `NewServer` (`specGAt`, `wp_proofGAt`, the derived `wp_proofG`) and the
  server `Link.lean` build. `etcdserver/Results.lean`'s `server_new_auth_on` then needed `lease.wp_NewLessorAt` (fixed).
- **Step 2, the putget carry** (proof-only; no statement of putget's results changes):
  - `NewServer.specAt := ∀ cmp, specGAt false cmp` (Spec `NewServer.lean`), `NewServer.wp_proofAt` (`wp_proofGAt` at
    auth off); Link entry `etcdserver_NewServer+At` (server list, same callees as `etcdserver_NewServer`).
  - `etcdstart.memberBuiltL … m γl` (`dist/MemberLessor.lean`: `memberBuilt`'s body plus `mvccLeases E.γ = γl`),
    `memberUpL_memberUp` (forgets the name), `etcdstart.wp_Start_builtL` (`Start.lean`: `memberBuiltL` → `memberUpL`).
  - `newServerMode.specAt`/`wp_proofAt`, `newServer.specAt`/`wp_proofAt`, `StartServer.specAt`/`wp_proofAt`: `spec` plus
    the binder `γl`, `ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl` first in the pre, `memberBuiltL`/`memberUpL … γl` in the
    post. Common list: `etcdserver_NewServer+At: @`, `etcdstart_{newServerMode,newServer,StartServer}+At`.
  - `etcd_dist.wp_StartServer1_slice` now takes `StartServer.specAt` and `γl` (with its half and slot) and gives
    `memberUpL … .none γl` (its only caller is putget's `Member`).
  - `memberNamesShare` moved from `server/MemberDefs.lean` to `MemberNames.lean` (same variables); putget's
    `memberShare` carries `memberNamesShare (c.ls id) (c.au id)`; `putget_shares` allocates one lessor name
    (`lessorSlot_alloc ⊤ []`) and auth names (`authNamesFreshG_alloc`) and sets `c.ls := fun _ => γl`,
    `c.au := fun _ => γa` (until then `lsNone`/`auNone`). putget's `Member` starts at `c.ls id` and, until step 3,
    weakens `memberUpL` to `memberUp` for the current `Serve_dist`; its `AdequacyMember` passes `etcdstart.wp_StartServerAt`.

**Step 3 (held: the lead's putgetK decision, #50 03:26Z).** What the replacement needs beyond the texts:
- `authNamesFreshD` and `etcdstart.memberUpOnL` move out of `AuthServeProposed.lean` (which the Spec files cannot import:
  it imports them) into a defs module (`MemberLessor.lean`, adding `auth.Boot`/`LessorSlot` imports); then the proposed
  texts replace `NewServer.specG_dist` (Spec `NewServerDist.lean`, plus `etcdURLsFit U.peer → etcdURLsFit U.client →` after
  `peerURLsDir`) and `Serve_dist.spec` (Spec `ServeDist.lean`), and `AuthServeProposed.lean` is deleted (only comments in
  `S2Interim`/`AuthViewDist` and `MemberNames`' import name it).
- `MainLogger` (dist/server) builds `memberUp` through `memberBuilt` → `memberBuilt_split` (`server/MemberSplit.lean:247`)
  → `wp_Start_built` → `memberUp_req` (`:303`) → `Serve_dist`: each needs an L variant (`memberBuiltL_split`,
  `wp_Start_builtL` exists, `memberUpL_req`), with `NewServer_dist`'s new `Hlslot` from `memberShareD`'s
  `memberNamesShare` (today dropped with `-` at line 104) and `etcdURLsFit` from `addrFits` (`etcd_dist.addrOk_addrFits`,
  `etcdstart.etcdURLsFit_httpURL`).
- putget's `Member`: `Serve_dist`'s `memberUpL … Γ.kv.lm (Γ.ls mid)` at `Γ = c.view`: needs `c.γk.lm = .none` (from
  `ClusterOk … .none`) to match the slice's `.none`; drop the `memberUpL_memberUp` weakening.
- putgetK: (a) `StartMember_dist`'s post `memberUpL … Γ.kv.lm (Γ.ls mid)` and back `addrFits peerAddr → addrFits client →`;
  or (b), if the review passes, putgetK's result deleted.

**Build state at handoff:** step 2's build of `a41e370ee7` was still running on fk-lean2 when this session stopped (context
limit): targets `etcdserver.Results`, `etcdstart.Link`, and the dist `putget`/`kvremote`/`putgetk` `TopLevelRobustness`;
log `~/eg/logs/f7l-build.log` (ends `EXIT n`). **First thing next:** read that log; if it failed, fix and rebuild those
targets (likely spots: `iframe Hl Ha`/`iexact Hslot` in `putget_shares`, the `isplitl [Hlslot]` framings of the `At`
proofs, `memberNamesShare`'s section variables in `MemberNames.lean`, the `(G := hG.goose_globalGS)` instance of
`lessorSlot` in putget's `Member`). Helper used: `/shared/tmp/f7sync.sh MODULES…` (fetches the branch into
`~/eg/etcd-grove.git`, checks it out in `~/eg/wt/etcd-safe-f7`, runs `f7l-build.sh`).

**Step 3:** held for the lead's putgetK verdict: (b) retire `putgetK_safe` (delete its result) if the independent
review confirms etcd_safe's driver subsumes it, else (a) strengthen `StartMember_dist` (above). Do not commit the
replacement until the coordinator relays the verdict.

**Step 4 (not started):** link leaseRead, leaseCatchup and leaseExpiry as N7-kv linked kv; `etc/tcb-report.py --check
--update` for exactly the new axioms (base and collections); `etc/tier-check.py --check`; `etc/lease-order-check.py`.
Step 5 (not started): `notes/axiom-review/f7-diff-vs-inprocess.md` and `notes/etcd-dist-f9-f2f7-rows.md` for the final texts.

**Addendum (after the handoff):** the build of `a41e370ee7` finished EXIT 1 with three errors only, all
`icases: threadTok not persistent` in the `wp_start` patterns of `newServer`, `StartServer` and `newServerMode`'s `wp_proofAt`
(the pre's `isPkgInit` is not stripped when it is not first). Fixed (an explicit `#Hpkg0` after `Hlslot`) in the next
commit, which is NOT yet built: rebuild the same targets first.

### Handoff 5 (2026-11-26, step 2 built; step 3's preparation built; the replacement held)

- **Step 2 built** (fk-lean2, `1c9bcde64e`, EXIT 0): `etcdserver.Results`, `etcdstart.Link`, the dist `putget`/`kvremote`/
  `putgetk` `TopLevelRobustness`. `etc/tier-check.py --check` ok (208 known); `etc/lease-order-check.py` ok.
- **Step 3's preparation, built in the same commit** (`1c9bcde64e` swept it in with the pattern fix: one worktree):
  - `authNamesFreshD` (namespace `EtcdGrove`) and `etcdstart.memberUpOnL` moved from `AuthServeProposed.lean` to
    `MemberLessor.lean` (defs; it now also imports `etcdserver.AuthApplyRes`, `auth.Boot`, `lease.LessorSlot`), so the
    Spec files `ServeDist.lean`/`NewServerDist.lean` can import them; `AuthServeProposed.lean` keeps only the two texts.
  - `etcd_dist.memberBuiltL_split` and `etcd_dist.memberUpL_req` (`server/MemberSplit.lean`, which imports
    `MemberLessor`): `memberBuilt_split`/`memberUp_req` over `memberBuiltL`/`memberUpL`, the name kept.
  - putget's `Member` derives `_Hlm : c.view.kv.lm = .none` from `ClusterOk` (unused until step 3; rename to `Hlm`).
- **Next (held for the lead's putgetK verdict, relayed by the coordinator):** the replacement texts of
  `NewServer.specG_dist`/`Serve_dist.spec` (Handoff 4, "Step 3"), `MainLogger` over the L lemmas, putget's `Member`
  without `memberUpL_memberUp`, and putgetK's (a) or (b).

### Handoff 6 (2026-11-26, step 3 replacement built and pushed; the lease link not started)

**Done** (`eb138f6f8c`, one commit, pushed; fk-lean2 EXIT 0 on putget/putgetk/kvremote `TopLevelRobustness`,
`putgetk.Start`, `etcdstart.Link`, `etcdserver.Results`):
- `NewServer.specG_dist` (Spec `NewServerDist.lean`): the reviewed text (binders `γa`, `γl`; `"Hlslot"`, `"Hγa"` last in
  the pre; post `on = true → E.authMode = .on γa` and `mvccLeases E.γ = γl`) plus `etcdURLsFit U.peer → etcdURLsFit
  U.client →` after `peerURLsDir`; the header lists every change; the `Hsdo` comment is the in-process one.
- `Serve_dist.spec` (Spec `ServeDist.lean`): the reviewed text verbatim; the old text deleted; both axioms' docstrings
  updated (the stale `specGAt` and distinct-names sentences fixed).
- putgetK (option (a)): `StartMember_dist.spec` has a binder `γl`, the post `memberUpL s ρ E₀ lg γn id lm γl`, and
  `addrFits peerAddr → addrFits client →` back. Its header says it is stronger than what `StartMember` can meet at
  putgetK's names (no lessor slot; `ClusterNames.lsNone`): a hypothesis (`HSM`), no axiom.
- `MainLogger`: `memberShareD`'s `memberNamesShare` unpacked (`Hlslot`; the auth names unused at auth off),
  `etcdURLsFit` from `Hwf.addrs` via `addrOk_addrFits`/`etcdURLsFit_httpURL`, `memberBuiltL`/`memberBuiltL_split`/
  `wp_Start_builtL`/`memberUpL_req`, `Serve_dist` at `c.view` (`hklg`). putget's and putgetK's `Member`: `Serve_dist`
  at `memberUpL` directly (`Hlm` / `hklg`). The auth-off branch is reached by `simp only [ClusterNames.view,
  Bool.false_eq_true, ↓reduceIte, …]`; the guarded premise by `fun h => absurd h Bool.false_ne_true` (`by decide`
  fails: free variables).
- `AuthServeProposed.lean` deleted; `MemberNames` imports `MemberLessor`; `S2Interim`/`AuthViewDist` docstrings updated.
- `etc/lease-order-check.py` ok; `etc/tier-check.py --check` ok (208 known).
- Notes: `axiom-review/f7-diff-vs-inprocess.md` (final texts, items 1-3 resolved), `etcd-dist-f9-f2f7-rows.md`, STATUS.

**Left on purpose (to avoid rebuilding `etcdstart.Start`'s whole cone, every etcd example's `Results`):**
`MemberLessor.lean`'s header and two docstrings still name `AuthServeProposed.lean`/`specG_dist_proposed`, and
`etcdstart.memberUpL_memberUp` is now unused; `MemberSplit`'s `memberBuilt_split`/`memberUp_req` are unused too. Fix
them with the next change that rebuilds that cone anyway.

**Not done:**
1. **`etc/axiom-tok-allow.txt`**: `Serve_dist.wp_proof`'s entry (line 196) and `trunc` line are keyed to the old
   `memberUp` handles. `memberUpOnL` adds `srvAuthLb`/`srvAuthStoreOn`/`isServerReqM true` (new keys likely), and
   `NewServer_dist` takes `authNamesFreshD`. Re-key from a run of `etc/axiom-tok-check.py` (needs `.lake/tcb.json` from
   `etc/tcb-report.py`, which needs every root built: run both on fk-lean2 under `systemd-run --user --scope -p
   MemoryMax=55G`, after `lake build` of what `tcb-report` names). `etc/tcb-baseline.txt` should not change (no axiom
   added or removed by step 3).
2. **Step 4, linking leaseRead/leaseCatchup/leaseExpiry** (as N7-kv linked kv, `client/KvLinked.lean`). What it needs:
   - `MainReady.spec` is kv-only (`⌜w.kind = W64 0⌝`, `OP ns w.ops`; `MainDeployment`/`Orchestrator` the same). Add per-kind
     variants for kinds LeaseRead/LeaseCatchup/LeaseExpiry whose share is the `RunLease*.spec` pre (`Γ`, `eps ↦*□ addrs`,
     the members' client facts, `Γ.kv.lm = .mono`/`.revocable` for catchup/expiry, distinct `Γ.ls`), proofs by the
     `switch` in `client.go:143`.
   - A `client/LeaseLinked.lean` (linking): `RunLeaseRead.wp_proof` over `leaseReadCheck`/`checked`/`ended`;
     `RunLeaseCatchup.wp_proof` over `newClient`, `leaseGrant.specMono`, `leaseList.specGranted`, `listed`; 
     `RunLeaseExpiry.wp_proof` over `leaseGrant.spec`, `leaseList.specLive`, `gone`, `listed`; each callee's proof over
     the six lease axioms; then `wp_OrchestratorLease*` as `wp_OrchestratorKv`.
   - For the axioms to enter the trust base a root must reach them (`etc/proof_roots.py`: `Link`/`MainLinked`/
     `Results`/`TopLevelRobustness`): `KvLinked` is reached through kvremote's `TopLevelRobustness`. Catchup and expiry
     need a cluster in mode `.mono`/`.revocable`, but `memberShareD`/`ClusterOk` fix `.none` and `MainLogger` serves at
     `.none`: a lease-mode start (the share at `lm`, `memberBoot_of_slice … lm`, `lease.bootCfg` at `lm`) is a
     prerequisite of any top-level use. Decide with the lead whether step 4 is the `LeaseLinked` theorems only (no
     root: the tcb report does not change) or a root (a `Results.lean` restating them, then a collection
     `etc/tcb-collections/etcd-dist-lease.txt` and `tcb-report --check --update` for exactly the six axioms).
   - The ordering gate then passes (`Serve_dist` ties `Γ.ls mid`).

### Handoff 7 (2026-11-26, steps 2 and 4 written, NOT built; step 1 run in flight; context limit)

**The lead's decision (#50 03:48Z, via the coordinator):** no new `TopLevelRobustness` statements (F8 proves the full
`etcd_robust_nocrash.spec`); instead the linked `wp_RunLeaseRead`/`Catchup`/`Expiry` at the axioms in a non-statement
linking module, root of a new collection `etc/tcb-collections/etcd-dist-lease.txt`, then `tcb-report --check --update`.
Generalizing the start over the lease mode: approved. Axiom-tok re-key on this branch: fine (at the later merge of M1's
head keep our `Serve_dist`/`NewServer_dist` entries, drop M1's old ones).

**Step 1 (axiom-tok re-key): run in flight, not read.** fk-lean2, script `~/eg/logs/f7atok.sh` (copy
`/shared/tmp/f7atok.sh`): `etc/AxiomTokCheck.lean` on `Serve_dist.wp_proof` and `NewServer_dist.wp_proof` only
(names `~/eg/logs/f7atok.names`, a two-line fake tcb `~/eg/logs/f7atok.tcb.json`) over the built
`kvremote.TopLevelRobustness` at `fb1ca9b3bd`; raw `~/eg/logs/f7atok.raw`, judged log `~/eg/logs/f7atok.log` (ends
`EXIT n`; ignore its stale-entry lines for every other axiom: the fake json names only the two). Next: take the
`Serve_dist` (and, if it now has findings, `NewServer_dist`) keys from the log and replace line 196's entry and the
`trunc` line (228) of `etc/axiom-tok-allow.txt` accordingly (drop the `trunc` line if the walk no longer truncates).

**Step 2 (lease-mode start), committed as WIP, NOT built:**
- `memberShareD c lm d …` (`server/MemberDefs.lean`): `ClusterOk … lm …`. (`lease.runCfg` cannot go in it: it
  needs `HeapGS`, the share has only `GooseGlobalGS`.)
- `MainLogger.spec`/`MainDeploymentLogger.spec`/server `MainDeployment.spec`: binder `lm` after `boot`, premise
  `lease.runCfg lm lm →` after `BootGoD`; proofs pass `lm`/`Hrun`. `MainLogger` proof: every `.none` → `lm`,
  `memberBoot_of_slice … lm Hrun hklg (fun h => hgps idm hidmem h)` (ClusterOk's last conjunct).
- `server/AdequacyMember.member_boot_dist`: `(lm) (Hlm : lm = .mono → lease.leasesNoExpiry)`, builds `Hrun` by cases
  (`runCfg_none`/`runCfg_mono`/`runCfg_revocable (srvRevokeLevels_of_srvLevels HLv) (srvRevokeOpen_intro
  EtcdServer.wp_revokeExpiredLeases)`).
- `server/ClusterStartD.lean`: `memberShares_of … lm …`; new `clusterStartDL d Hd boot Hbf Hrb lm hap` (post:
  `c.γk.log0 = [[],[]] ∧ c.γk.lm = lm ∧ c.NamesInj`, `etcdKV` only `if lm = .none`, every member's
  `lease.lessorSlot (c.ls id)`), `lessorSlots_of`; `clusterStartD` is now the `.none` wrapper (statement unchanged
  but `memberShareD c .none`).
- kvremote (`TopLevelRobustness`, `MembersStart`): `.none` instantiated; statement text unchanged.
- Likely build spots: `lessorSlots_of`'s `refine .trans (bigSepL_mono …) bigSepL_sep_eqv.1` (direction of
  `sep_eqv`), `Hγ.2.….1` projection for `c.γk.lm` (13th conjunct), `lease.runCfg` instance arguments in the Spec
  files (raft/etcdserver `Assumptions`), `EtcdServer.wp_revokeExpiredLeases`' instance args in AdequacyMember.

**Step 3 (MainReady/MainDeployment/Orchestrator lease variants): not started** (the lead's answer makes the roots the
linked runs only; the orchestrator dispatch is follow-up).

**Step 4, written, NOT built:** `Proof/.../dist/client/Results.lean` (named `Results`, not `LeaseResults`, because
`etc/proof_roots.py` takes roots only from `Link`/`MainLinked`/`Results`/`TopLevelRobustness`; linking by name, no
`tier-linking.txt` entry needed): `wp_newClientDist`, `wp_RunLeaseRead`, `wp_RunLeaseCatchup`, `wp_RunLeaseExpiry`.
Collection `etc/tcb-collections/etcd-dist-lease.txt` (roots line only; baseline to write). Next: build it, fix imports
(`time.wp_Sleep` from `Perennial.Proof.time.Link`; the axioms' namespace `etcd_dist.view`), then
`etc/tcb-report.py --collection etc/tcb-collections/etcd-dist-lease.txt --check --update` and the base
`--check --update` for exactly the six lease axioms (needs every root built, under the memory cap),
`etc/tier-check.py --check`, `etc/lease-order-check.py`.

**Build next:** `/shared/tmp/f7sync.sh` with targets `Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Results`
`…dist.kvremote.TopLevelRobustness` `…dist.putget.TopLevelRobustness` `…dist.putgetk.TopLevelRobustness` (after the
axiom-tok run exits: same worktree and lock).

**Step 5:** skipped (`MemberLessor.lean` is not in this change's cone).

**Addendum to Handoff 7 (the step-1 run finished):** `~/eg/logs/f7atok.log` on fk-lean2 (EXIT 1, raw kept in
`~/eg/logs/f7atok.raw`): `NewServer_dist.wp_proof` 200 findings, including a `TOKEN: level *: handed to a callback 2,
supplied directly 1` and `depth:` truncation (`ownMap`, `backend.bbAt`, `bbolt.isBolt`); `Serve_dist.wp_proof` 32
findings; FAILED counts: 2 unknown (scenario cap), 1 unknown (truncated), and the 50 stale entries that come from the
two-name json (ignore them). Before re-keying: `--reuse-raw ~/eg/logs/f7atok.raw -v` with the same fake json to print
each finding's key, and check whether the full gate (`etc/gates.sh`'s run, default depth) caps the same two walks;
`NewServer_dist` had no entry before, so its new findings may need the lead's review rather than an entry.

### Session 8 (2026-11-26): steps 1–4 of Handoff 7

**Step 1 (axiom-tok re-key), partly done; `NewServer_dist` waits for the lead.** Re-judged
`~/eg/logs/f7atok.raw` (fk-lean2; copy `/shared/tmp/f7atok.raw`) with `--reuse-raw … -v` and the two-name json:
- `Serve_dist.wp_proof`: line 196's entry re-keyed (`6780c67a11`) to the walk's 22 keys: the old 13 plus
  `3:A:produced3/consumed2`, `3:Pre:produced2/consumed1`, `3:Pre:produced3/consumed2`, `3:Y:produced1/consumed0`,
  `7:A`, `7:C`, `7:R`, `7:Lk:auth.AuthState→IPropGF→IPropGF`, `7:Sw:auth.AuthSess→IPropGF`: the auth-on handles of
  `memberUpOnL` (the reviewed text), every one a key of `EtcdServer.leaseTimeToLive`'s entry (line 64, same
  handles). The `trunc` line (228) stays: the walk still truncates (`decLb`, `cd.4`, `ownRWMutex`, `lessorPinAll`,
  the backend's and mvcc's predicates). With the entry, `Serve_dist`'s rule-2/3/7 findings are all accepted; what is
  left are 7 rule-5 findings (`http.*Raw`, `metadata.*Raw`, `status.statusAtRaw`), the cascade of
  `NewServer_dist`'s uncovered findings (it taints `metadata.*`/`status.statusAtRaw`, which `Serve_dist` consumes);
  they go when `NewServer_dist` passes.
- **Scenario cap.** Both walks hit it (`capped`: `PRUNEAT` 64 undominated scenarios, merged into one worst case);
  the cap is a constant of `etc/AxiomTokCheck.lean` and a walk is per axiom, at the same default `--depth` (14)
  the gate uses (`etc/gates.sh` passes no `--depth`), so the full gate caps the same two walks. A capped walk whose
  findings all have entries passes (`report`: capped counts only with findings left), as `Serve_dist` now does
  modulo the cascade.
- **`NewServer_dist.wp_proof` (no entry, not added; for the lead).** 200 findings, capped, and truncated (`depth:`
  `ownMap`, `backend.bbAt`, `bbolt.isBolt`, … 41 notes), so it needs both an entry and a `trunc` line. The token
  finding is rule 2b at the generic level point `*`: in the merged scenario the axiom consumes `tok:T` 3
  (`threadTok`, the token covering every level) of which 2 come back from callbacks (`ret:T 2`), and hands `tok:T`
  2 to user-supplied callbacks (`cb:T 2`, tokens produced at positive polarity under a flip, `walkTok`); the user
  supplies 1 directly (`Htok ∷ threadTok`). Rule 2b's reading: a callback may never return, so what is handed to
  callbacks must be paid by what is supplied directly. Which callbacks: not traced (the walker keeps no
  provenance); the spec's own `threadTok`s are only `Htok` and the post's (both arms); the callbacks are contracts
  inside the premises (none of `bootstrapContract`'s triple mentions `threadTok` directly; the new premises
  `Hlslot`/`Hγa` hold none either: `lessorSlot` is an invariant over `lessorHistOk`, `authNamesFreshD` ghost
  authorities). Since the walk is capped, `cb:`/`ret:` are maxima over merged scenarios, so `2 vs 1` may be two
  scenarios each handing one token sequentially (an artefact) rather than one scenario handing two. On M1:
  `NewServer_dist` exists on `etcd-safe-m1`/`-m1-fin` (same statement as M1's fk-lean2 worktree `d83e9825b7` but a
  comment), in `etc/tcb-baseline.txt`, with no entry and no `trunc` line in M1's allow file; whether M1's walk had
  the finding is not measured here (the M1 run: AxiomTokCheck on `Proof…dist.NewServerDist` in
  `~/eg/wt/etcd-safe-m1` with names = `NewServer_dist.wp_proof` only, the same script as `f7atok.sh`).

**Step 2 built** (`fb6dad2ca4`): `lessorSlots_of`'s first bullet needed `iexact Hsl` after `iframe`;
`client/Results.lean` is in namespace `etcd_dist_client` (the client proofs' namespace: in `etcd_dist`, `newClient`
and others resolved to `etcd_dist`'s own names) with `open … Net etcd_dist` (`netExt` is `Net.netExt`). fk-lean2:
`dist.client.Results` EXIT 0; `kvremote`/`putget`/`putgetk` `TopLevelRobustness` built (the run before failed only on
`Results`). kvremote's statement text unchanged; no `sorry`, no axiom beyond the six lease ones.

**Root name.** The linking module is `client/Results.lean`, not `LeaseResults.lean`: `etc/proof_roots.py` takes roots
only from `Link`/`MainLinked`/`Results`/`TopLevelRobustness` files.

### Handoff 8 (2026-11-26, context limit; step-3 job running)

- **Head:** `etcd-safe-f7` at this commit (code at `fb6dad2ca4`; step 1's re-key `6780c67a11`).
- **Step-3 job, running on fk-lean2** (`~/eg/logs/f7tcb.sh`, copy `/shared/tmp/f7tcb.sh`; summary log
  `~/eg/logs/f7tcb.log`, ends `EXIT`): `lake build` of all 248 proof roots (`f7tcb-build.log`), then
  `tcb-report.py --check` (base, NO `--update`: `f7tcb-base.log`), then `--reuse --collection
  etc/tcb-collections/etcd-dist-lease.txt --check --update` (`f7tcb-lease.log`; writes the collection's baseline
  in fk-lean2's worktree `~/eg/wt/etcd-safe-f7`, uncommitted), `tier-check.py --check` (`f7tier.log`),
  `lease-order-check.py` (`f7lo.log`). Under flock and MemoryMax=55G.
- **Next:** read `f7tcb.log`. If the base diff is exactly +6 (`etcd_dist.view.{Lease_Grant_dist,
  Lease_GrantLive_dist, Lease_LeasesGranted_dist, Lease_LeasesLive_dist, Client_LeaseLeases_dist,
  Client_LeaseTimeToLive_dist}.wp_proof`), run `python3 etc/tcb-report.py --reuse --check --update` there (under
  the lock), then copy `etc/tcb-baseline.txt` and `etc/tcb-collections/etcd-dist-lease.txt` back (scp) to
  `/shared/etcd-grove-f7`, commit, push. Anything else in the diff: stop and report. Tier and lease-order must pass
  (the new `Serve_dist` ties `Γ.ls mid`).
- **Axiom-tok:** `Serve_dist` re-keyed (above); `NewServer_dist` needs an entry and a `trunc` line, which the lead
  decides (the write-up above). Optional measurement for the lead: `~/eg/logs/f7atok-m1.sh` (copy
  `/shared/tmp/f7atok-m1.sh`, not run yet) walks M1's `NewServer_dist` in `~/eg/wt/etcd-safe-m1` read-only (log
  `~/eg/logs/f7atok-m1.log`) to show whether M1's statement already had the token finding; that worktree's
  `NewServerDist.olean` may be stale.
- **Left after that:** the axiom-tok gate (once the lead rules on `NewServer_dist`), step 3 of Handoff 7 (the
  orchestrator's lease dispatch), landing.

### Session 9 (2026-11-26): the two deployment restrictions; `NewServer_dist`'s token finding traced

**Q1, Q2 (the lead's decisions, F8 design `notes/etcd-dist-plan.md` §27.7 on `etcd-safe-f8/2026-11-26`)**, Go and Lean
in step (`adaea37e3a`):
- Q1, `typed.Deployment.WellFormed`: `d.cfg.auth = true → ∃ w ∈ d.workloads, w.needsAuth = true` (a new conjunct after
  the `needsAuth → auth` one). Go: `WellFormed`'s clause-5 loop sets `needed` on a `NeedsAuth` kind, and
  `c.Auth && !needed` fails after it. Since `auth`/`authLease` run alone, auth is on exactly in `[auth]`, `[authLease]`;
  review F10's `¬ (auth ∧ leaseExpiry ∈ ws)` is now implied (kept, as Go's check is).
- Q2, `typed.Compatible`'s fifth conjunct: a `grantsLeases` workload beside no other that `writesKeys` (`leaseRead`
  grants nothing). Go: `compatible`'s sole-writer loop runs also for `grantsLeases` kinds
  (`!needsSoleWriter(k) && !grantsLeases(k)`); `goCompatible`'s third conjunct takes the disjunction.
- Proofs: `compatible.wp_proof` takes `grantsLeases.spec` (link list and `deployment/Link.lean` regenerated); its
  inner loop is shared by the two "excludes writers" outcomes (`all_goals`); `WellFormed`'s loop invariant tracks
  `needed` (`nb = true → ∃ w ∈ take j, kindAlone`), then a case split on `auth`/`nb` for the new check;
  `goWellFormed_sound` proves both clauses; positional destructurings of `WellFormed` shifted (`.members`,
  `.urlBounds`, `BootFactsSat.satD_wf`). Every other consumer reads `WellFormed` by statement (`grind`).
- `deploy.go`: `RandomWorkloads` puts the granting lease workloads in a class of their own (`leaseRead`, and
  `leaseCatchup` or `leaseExpiry`), `leaseRead` beside the key writers; `randomCfg`'s auth exactly when needed.
  `TestWellFormed`: auth on with `putget` or no workload refused, no workload with auth off accepted, each granting
  kind beside `putget`/`compact`/`durable` refused and beside `leaseRead` accepted, `putget`+`leaseRead` accepted
  (mutation-checked: each new case fails with its check removed).
- Built on fk-lean2 at `adaea37e3a`: `deployment.Link`, `BootFactsSat`, `TopLevelWitness`, `client.Results`,
  `kvremote.{TopLevelRobustness,TopLevelWitness}`, `dist.TopLevelRobustness`, the two `SpecPlan` PkgInit leaves
  (`etc/importers.py --leaves`), EXIT 0; `etc/goose.py --check --project putget-dist` up to date.
- **Conflicts: none.** `clusterStartDL` and `compactorCfg_of_wf` read `WellFormed` by statement; `wp_RunLeaseRead`'s
  spec is over any `Γ` (its "lease mode `none`" is a comment), so `leaseRead` beside a granter is covered. The auth
  start (`{auth}`, `{authLease}` with auth on) is exactly Q1's case. Note for F9: kvremote's scope
  `KvOnly d ∧ d.cfg.auth = false` now has its second half implied by `WellFormed ∧ KvOnly` (not changed: statement
  text is the lead's).

**`NewServer_dist`'s rule-2b finding**: traced to `lease.bootCfg`'s revocable conjunct `srvRevokeOpen`
(`revokeExpiredLeases.spec`, a triple the caller supplies: its `threadTok` in and out) and, inside it, `lessorOk`'s
`Promote` triple (a borrow); write-up `notes/axiom-review/f7-newserver-atok.md`, with M1's comparison. No allow
entry added (the lead's call).

### Handoff S2-1 (2026-11-26, P-A1 written, its build running; context limit)

**P-A1 (written, build running at handoff).** Head `c9b4c6402a`+1 (the parenthesization fix); fk-lean2 build of
`etcdserver.Results`, `etcdserver.Link`, `dist.MemberNames` via `/shared/tmp/f7sync.sh`, log `~/eg/logs/f7l-build.log`
(ends `EXIT n`; client copy `/shared/tmp/f7s2-b1.out`). The two earlier runs failed only in `auth/Boot.lean`
(`unfold authBootFresh` missing; `|==> A ∗ B` parses as `(|==> A) ∗ B`: conclusions now parenthesized, also
`srvTpInv_alloc_given`). Nothing past `Boot.lean` was elaborated yet: expect errors further on.
- `auth.authBootFresh γa` / `auth.authBoot_given` (`auth/Boot.lean`): `authBoot_alloc`'s conclusion at given names.
- `auth.newTokenProviderSimple.specAt`/`wp_proofAt`, `auth.NewTokenProvider.specAt`/`wp_proofAt` (pre `tokAuth γt γf ∅`
  given; post without `∃ γt γf` and without the rights' authority); link entries `+At` in
  `etc/link-lean-first-server.txt`, `Link.lean` regenerated (`python3 etc/gen-link.py --server > …/Link.lean`).
- `AuthSrv.lean`: `authNamesFreshTP γa` (tok, fresh map, `authBootFresh`), `srvAuthNamesFresh γa` (+ `monoNatAuthOwn γa.rdy 1 0`),
  `authSrvTPAt on` (binders `γy γa`, pre `⌜on → γa.rdy = γy⌝ ∗ (⌜on⌝ -∗ authNamesFreshTP γa)`, post `on → M = .on γa`),
  `authSrvTPAt_off`, `srvAuthNamesFresh_alloc`, `ite_on_wand`, `ite_on_intro`. `AuthSrvLinked`: `authSrvTP_on` became
  `authSrvTPAt_on` (over `NewTokenProvider.specAt`, `authBoot_given`). `Results`: `srv_auth_tp_on/off : authSrvTPAt …`.
- `InvStart.srvTpInv_alloc_given`; `NewServer.lean`: `srvTpInv_allocA`; the big proof is now `NewServer.wp_proofGAtA`
  (spec `NewServer.specGAtA`: binder `γa` after `γl`, `"Hγa" ∷ (if on then srvAuthNamesFresh γa else True)` FIRST in the
  pre, post `on = true → E.authMode = .on γa`); `wp_proofGAt` derived (allocates `γa`; `wp_start_folded`, frame
  `isplitl [Ha]`, `ite_on_intro`); every `hTP` is `authSrvTPAt`. Likely spots: the token-provider call's frame bullet
  (`iframe Hzlg Hγa`, then `isplitr` pure / `isplitr` waiter / `ipureintro; exact Hγy`: if `iframe` already closed
  the pure, drop the last line), `srvTpInv_allocA`'s `iframe H1 Hi`, `authSrvTPAt_on`'s `ihave Hfr := Hfr $$ []`,
  the derivation's `Hq.2.2.1`/`Hq.2.2.2` projections.
- `dist/MemberNames.authNamesFreshD_iff_srv` (imports `AuthSrv`): `authNamesFreshD γa ⊣⊢ srvAuthNamesFresh γa`.
  `NewServer_dist`'s text is unchanged.

**Step 2 (auth-on member boot): not started; research done.** Findings:
- **Statement premises.** `d.cfg.auth = false →` is a premise of three Spec files: `Spec/.../dist/server/MainLogger.lean:53`,
  `MainDeploymentLogger.lean:49`, `MainDeployment.lean:49`, and `member_boot_dist`'s `Hauth` (`AdequacyMember.lean:74`,
  a proof file, used only by `kvremote/TopLevelRobustness.lean:119` with M1's `Hscope.2`). Dropping them is a spec
  change of those main-program specs (not top-level, not axioms): needs the lead's OK under "proof-only except L5"
  (L5 names only `Hauth`). `member_boot_dist.law` (`kvremote/Start.lean:123`) has `⌜Γ.auth = false⌝` in its post.
- **Missing, global (no-heap) allocation**: no `GooseGlobalGS` auth-on counterpart of `clusterAllocN`/
  `srvClusterBoot_allocG` (the on ones, `srvClusterBootOn_alloc` `ES/NewServerAllocOn.lean:58`, `allocNOn`, are `HeapGS`
  and need `bootMarshal`); `ClusterOk` (`alarmChain false`) and `ClusterNames.view` (`auth := false`) take no `on`;
  no auth-on `memberBoot_of_slice` (`AllocN.lean:305`). Auth on needs `cmp = false` (`NewServer_dist`'s `cmp → ¬on`).
- **Missing, member chain**: auth-on `memberBuiltL`/`memberBuiltL_split`/`wp_Start_builtL`/`memberUpL_req` (all
  auth-off today); a lessor-tied `memberUpOn_intro` (`etcdstart/Served.lean:191`, generic `γa m`) giving
  `memberUpOnL`. Templates: `etcdstart/StartMemberAuth.lean:196-238` (generic lease mode) and authkv's `startServer`:
  `NewServer` on, `isServerBuilt_of_gapM`, `isServerBuiltM_C (.on γa)` + `srvStop.slot_intro`, `wp_Start … (.on γa)`,
  `memberUpOn_intro`; TLS by `srvTLSId_false` (`ES/AuthReqDerive.lean:103`) with `iExactEq Hcca; rfl`
  (`memberCfg` never sets `ClientCertAuthEnabled'`: zero value). `srvLeaseRd_of_srvInv` and the peer specs are generic in `on`.
- MainLogger's off-only spots: `:110` drops the auth names, `:169` `memberBoot_of_slice`, `:205` `memberCfg_off`,
  `:241` `simp [kvInvM_false, …]`, `:318` `isServerBuilt_of_gap`, `:337` `memberBuiltL`, `:399/:408` peer at `false`,
  `:434-441` Serve_dist's off branch.

**Next:** (1) read the build log, fix P-A1 until `Results`/`Link`/`MemberNames` build; `etc/tier-check.py --check`,
`etc/lease-order-check.py`. (2) Ask the lead whether step 2 may drop `d.cfg.auth = false` from the three main-program
specs (exact texts above). (3) Step 2 in order: global auth-on cluster allocation (`ClusterOk on`, `view` with
`d.cfg.auth`, one `Γ.kv.hist`), `memberBoot_of_slice` on, the auth-on member chain ending in `memberUpOnL`, MainLogger
split on `d.cfg.auth`. (4) Step 3 (`RunAuthLease` plan): not started.

**Addendum to Handoff S2-1:** the P-A1 build of `e2b163b6b9` finished **EXIT 0** (fk-lean2: `etcdserver.Results`,
`etcdserver.Link`, `dist.MemberNames`; no error). Next is unchanged except item (1): run `etc/tier-check.py --check`
and `etc/lease-order-check.py`, and build the dist `TopLevelRobustness` leaves (`NewServer.specGAt`'s users are unchanged).


### Handoff S2-2 (2026-11-26; step 1 closed, step 2 blocked on one statement-level gap, research done)

**Step 1 (P-A1): done.** `f9b5d39bca`'s build of `etcdserver.Results`, `etcdserver.Link`, `dist.MemberNames` EXIT 0
(fk-lean2); `etc/tier-check.py --check` ok (208 known), `etc/lease-order-check.py` ok. The dist `TopLevelRobustness`
leaves (the addendum's) were building at handoff, at `323b40ae38` (notes only past `f9b5d39bca`): `dist.TopLevelRobustness` and `dist.kvremote.TopLevelRobustness` via `/shared/tmp/f7sync.sh`, log `~/eg/logs/f7l-build.log` on fk-lean2 (ends `EXIT n`), client copy `/shared/tmp/f7s2-b2.out`. Next session: read it first.

**Step 2 (auth-on member boot): blocked before any Lean, on one gap the coordinator's decision assumed away.**
"Auth on means compaction off; use `WellFormed`" does not hold:
- `typed.Deployment.WellFormed` (`DeploymentDefs.lean:246`) ties auth only to workloads (Q1:
  `(d.cfg.auth = true → ∃ w ∈ d.workloads, w.needsAuth = true)`), and the compactor only to `compact`
  (`(Workload.compact ∈ d.workloads → d.cfg.compactor.isPeriodic = false)`). `ServerCfg.Supported` allows
  `.revision r`/`.periodic p` with `auth = true`. So `[auth]` with a revision compactor is well formed.
- `memberShareD`'s `v3compactor.bootCfg d.cfg.compactorMode d.cfg.retention cmp cret` forces `cmp = true` when
  the retention is nonzero (`BootCfg.lean`: `ret = W64 0 ∨ (cmp = true ∧ …)`), and `NewServer_dist` (axiom) takes
  `(cmp = true → on = false)` (`Spec/.../dist/NewServerDist.lean:109`). The member cannot call `NewServer_dist` in
  that deployment, so `MainLogger` cannot be proved for it, whatever the start allocates.
- `WellFormed`'s doc comment (item 5) says Q1 "keeps `compact` from auth, which `NewServer`'s `cmp = true → on = false`
  excludes": true of the `compact` workload, not of the server's compactor, which sets `cmp` alone.
No Lean was written for step 2. Options (the lead's): (a) a `WellFormed` conjunct `(t.cfg.auth = true → t.cfg.compactor = .off)` with Go's
`WellFormed` check and a `TestWellFormed` case (a change to the top-level premise's definition: the deployments
covered shrink by auth-with-compactor); (b) the three main-program specs keep a narrower premise,
`d.cfg.auth = true → d.cfg.retention = W64 0`, in place of `d.cfg.auth = false` (intermediate specs only; the
whole-system proof then still needs (a) or (c) to discharge it); (c) revisit `NewServer_dist`'s `cmp → ¬on` (an
axiom: a new review). Nothing was changed.

**Second finding (no decision needed, it sizes the work): `kvInvOn` is heap-bound.** `kvInv` is defined over
`GooseGlobalGS` (`InvRequest.lean:935`, section `kvGhostG1`), which is why `clusterFacts`/`clusterAllocN` run at the
start's global ghost state. `kvInvOn`, `kvWorkOn`, `kvModelOn`'s neighbours (`KVAuthModel.lean`, sections `defs`
1753-1816 and 1839-1872, `[hG : HeapGS …]`) and `kvInvOn_alloc_boot` (`ServerOn.lean:644`, HeapGS) are not. The global
auth-on allocation first moves them into heap-free sections (the file's own `defsHF` pattern: `[Gg : GooseGlobalGS
HasLC.hasLC GF] [GoLocalContext]`; HeapGS callers reach them through `HeapGS.goose_globalGS`), with whatever lemmas
`kvInvOn_alloc_boot`'s proof uses (`onGhostVarHalves`, `authHist_split`, …). Then `srvClusterBootOn_allocG` =
`srvClusterBoot_allocG` (`NewServerAlloc.lean:203`) with its KV part replaced by `srvClusterBootOn_alloc`'s
(`NewServerAllocOn.lean:197-215`: `mono_list_own_alloc [srvAuthSt0]`, `γk0` at `alarmChain true …`, `cmp = false`,
`cret = 0`, `kvInvOn_alloc_boot`), post `kvInvOn … srvAuthSt0 ∗ etcdKV … ∗ authHistView γk [srvAuthSt0]`.

**Design for step 2 once unblocked (keeps every caller's text):** a trailing `(on : Bool := false)` on `ClusterOk`
(`ch0 = alarmChain on false false`, and `on → cmp = false`), `ClusterNames.view` (`auth := on`) and
`clusterFactsOf` (as `kvInvM on … srvAuthSt0`; `kvInvM_false` gives today's); `memberShareD` passes `d.cfg.auth`;
`clusterAllocN`/`clusterStartDL` split on `on` (on: `srvClusterBootOn_allocG`); `memberBootOn_of_slice` from
`memberBootOn_of` (`Alloc3On.lean:140`) as `memberBoot_of_slice` is from `memberBoot_of`; then the member chain
(`memberBuiltL`/split/`wp_Start_builtL`/`memberUpL_req` at on, `memberUpOn_intro` with `mvccLeases E.γ = γl`) after
`StartMemberAuth.lean:186-240`; `MainLogger` split on `d.cfg.auth` (its off-only spots are listed in Handoff S2-1).

**Next:** (1) the leaves build's result (fix if red). (2) The lead's choice among (a)/(b)/(c) above. (3) Move `kvInvOn` and `kvInvOn_alloc_boot` (and what its proof uses) to heap-free sections; build `etcdserver.Results`. (4) `srvClusterBootOn_allocG`, then the design's steps in order, building and pushing after each.

### Handoff S2-3 (2026-11-26; steps 1-2 written and building, option (a) in WellFormed; step 3 analysed, not written)

**Option (a) approved by the lead (#50, 05:15Z) and done** (`1bdfd5798e`): Go `WellFormed` refuses
`c.Auth && c.Retention != 0` ("the token provider beside an auto-compactor"), `randomCfg` sets no compactor beside
the token provider, `TestWellFormed` has two cases (revision and periodic compactor beside `auth`) that fail without
the check (checked by disabling it), retranslated (`etc/goose.py --project putget-dist`, one file). Lean: typed
`WellFormed`'s conjunct `(d.cfg.auth = true → d.cfg.compactor = .off)` right after Q1; item 5 of its doc comment
fixed (Q1 keeps the `compact` *workload* from auth; the server's compactor sets `cmp` by itself); `goWellFormed`
gains `(d.cfg.auth = true → d.cfg.retention = W64 0)` before the sizes, `goWellFormed_sound` maps it through
`typedCfg`; `WellFormed.wp_proof`'s tail gets `hacmp` from the new `if` (`‹d.cfg.retention = W64 0›`);
positional uses shifted (`WellFormed.members`, `.urlBounds`, `satD_wf`); new
`Deployment.WellFormed.authCompactorOff : d.WellFormed → d.cfg.auth = true → sint.Z d.cfg.retention = 0`, which
discharges what the brief called `Hauthcmp` (with `v3compactor.bootCfg_off`, choose `cmp = false`, `cret = 0`).

**Step 1** (`f05dedcae7`, proof-only): `kvModelOn`…`kvWorkOn_of_kvWork`, `kvInvOn`, `kvInvM` (+ instances,
`kvInvM_false/true`) and `authHist_split` (`KVAuthModel.lean`), `onGhostVarHalves` and `kvInvOn_alloc_boot`
(`ServerOn.lean`, new section `lemmasHF`) moved to heap-free sections (`GooseGlobalGS` + `GoLocalContext`,
`gooseInvGS` local instance), as `kvInv`. **Step 2** (`bdc7514127`): `srvClusterBootOn_allocG`
(`NewServerAllocOn.lean`, section `allocG`): `srvClusterBoot_allocG`'s text with `srvLogInv_alloc … true`, no
`cmp`/`cret` parameters (post `γk.cmp = false ∧ γk.cret = 0`, `ch0 = alarmChain true false false`), the KV part
from `srvClusterBootOn_alloc` (post `kvInvOn … srvAuthSt0 ∗ etcdKV γk (kvStateOf (kvModelOn …)) ∗ authHistView γk
[srvAuthSt0]`, unconditional: no `if γk.lg`). Build at `1bdfd5798e` of `NewServerAllocOn`, `etcdserver.Results`,
`dist.deployment.Link`, `dist.BootFactsSat`: client copy `/shared/tmp/f7s2-b3.out`; read it first (the WellFormed
proof's new `if` step and `hacmp` were written blind; `kvInvOn_alloc_boot`'s `package_sem` instance in HF
unverified).

**Step 3, analysed (not written): `ClusterOk` is coupled to `clusterAllocN`'s pure post.** `ClusterStart.lean`
proves `⌜ClusterOk …⌝` by `exact Hγ` from `clusterAllocN`'s post, and `ClusterStartD` passes `Hγ` to
`memberShares_of` as `ClusterOk` and projects it positionally (`Hγ.2.2.2.2.2.1`, `Hγ.2^12.1`). So adding
`(on : Bool := false)` to `ClusterOk` (`ch0 = alarmChain on false false`, a trailing `∧ (on = true → cmp = false)`)
must be done together with `clusterAllocN (on := false)` (post the same text, plus `clusterFacts … on`; hypothesis
`on = true → cmp = false ∧ cret = 0`; proof split on `on`, the `true` arm via `srvClusterBootOn_allocG`), and the
`etcdKV` tail of its post must become `if on then etcdKV γk (kvStateOf (kvModelOn …)) ∗ authHistView γk
[srvAuthSt0] else <today's>` (callers' `isimp … Bool.false_eq_true, ↓reduceIte` reduce it). Destructurings of
`ClusterOk` to fix: only `MainLogger.lean:112` binds the last conjunct (`hgps` → `hgps, -`); `StartOneSlice:87`,
`putgetk/Member:283`, `putget/Member:97` end in `-`. `clusterFacts` (`etcdstart/AllocN.lean:197`) gets
`(on : Bool := false)` with `kvInvM on ⟨γ, [], W64 0⟩ γk srvAuthSt0` last (`srvAuthSt0`: `KVModelM.lean`); it is
unfolded only in `AllocN` (instance, `clusterAllocN`'s `iframe #`: needs `rw [kvInvM_false]` or defeq,
`memberBoot_of_slice`'s `$$ Hkv`: defeq); `clusterFactsOf c (on := false) := clusterFacts … on`;
`ClusterNames.view c (on := false) := ⟨c.γk, c.ls, on, c.au⟩`.

**Build result (`/shared/tmp/f7s2-b3.out`, EXIT 1):** `KVAuthModel` and `BootFactsSat` built; the one failure
is `dist/deployment/WellFormed.lean`'s tail (lines 588-615): the new `if c.Auth && c.Retention != 0` makes
`repeat' wp_if_destruct` leave extra goals that `err_exit` does not close: some auth-on / `nb = false` branches
reach `hneed` (595: unsolved `∃ w ∈ d.workloads, kindAlone …`), some Iris goals are `⊢ False` with contradictory
loop-exit `Hif`s (602: `iapply HΦ` cannot apply to `False`), and the old `first | exact Hif | …` at 584 now reports
its type mismatch. `NewServerAllocOn`/`ServerOn`/`etcdserver.Results` did not appear in the log (not reached before
the failure): build them again. To debug: on fk-lean2, `etc/lean-check.py --fast --goal 593 <file>` (37 goals; a
dump was in `/tmp/f7g.txt` there). Likely fix: run `wp_auto` between the two `if`s per branch (split on
`d.cfg.retention = W64 0` explicitly, as the `rcases hau`/`hnb` split does), close the `False` goals by the
contradictory `Hif`s before `hneed`, and keep `hacmp` from the retention split.

**Next:** (1) fix `WellFormed.wp_proof`'s tail as above; build `NewServerAllocOn`, `etcdserver.Results`,
`dist.deployment.Link`, then the dist `TopLevelRobustness` leaves. (2) Step 3 as above, in one commit with `clusterAllocN`'s `on`. (3) Step 4 (the auth-on
member chain), unchanged from S2-2's design; `Hauthcmp` comes from `WellFormed.authCompactorOff`.

### Handoff S2-4 (2026-11-26; step 1 done, step 2's build running, step 3 written unbuilt)

**Step 1 done** (`cc6ca7462d`, checked with `etc/lean-check.py --fast -a` on fk-lean2: 0 errors). Cause: in some outer
branches the loop's exit `wp_if_destruct` leaves `Hif : ¬ #(decide _) = #true` and the goal as `if decide (#(decide
_) = #false) = true then WP else False`, so the checks' `repeat' wp_if_destruct` split on the loop condition again
(the `⊢ False`/`¬True` goals, `hneed`/`hacmp` unsolved). Fix: `Hif'` gets a third alternative (`intro h; apply Hif;
rw [decide_eq_true h]`), then `try simp only [decide_eq_false Hif', _root_.decide_true, ↓reduceIte]` (`decide_true`
is ambiguous with `BI.decide_true`). Second bug: `hneed`/`hacmp`'s `(rw [hau] at ha; cases ha)` *succeeds* without
closing the goal when auth is on (`cases` on `true = true`); now `exact absurd ha (by decide)`.

**Step 2: build running at handoff** (started on fk-lean2 from `cc6ca7462d`; result not read): targets
`etcdserver.NewServerAllocOn`, `etcdserver.Results`, `dist.deployment.Link`, `dist.TopLevelRobustness`,
`dist.{kvremote,putget,putgetk}.TopLevelRobustness`; log `~/eg/logs/f7l-build.log` on fk-lean2 (ends `EXIT n`),
client copy `/shared/tmp/f7s2-b4.out` (last line only). If it failed, the build lock may still be held: check before
starting another. Then run `etc/tier-check.py --check`, `etc/lease-order-check.py` (not run yet).

**Step 3 written, not built** (the WIP commit after `cc6ca7462d`; build it next, with step 2's targets):
`etcdstart/AllocN.lean`: imports `NewServerAllocOn`; `clusterFacts … (on := false)` ends in `kvInvM on ⟨γ, [], W64 0⟩ γk
srvAuthSt0`; `clusterAllocN … (cmp) (cret) (on := false) (Hon : on = true → cmp = false ∧ cret = 0 := nomatch)`, post
`ch0 = alarmChain on false false`, trailing `∧ (on = true → cmp = false)`, `clusterFacts … on`, tail `if on then
etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries …))) ∗ authHistView γk [srvAuthSt0] else <old tail>`;
proof `cases on`, the false arm the old proof (+ `simp only [Bool.false_eq_true, ↓reduceIte]` before `iframe Hetcd`,
`try iexact Hkv` after `iframe #`), the true arm via `srvClusterBootOn_allocG` (`obtain ⟨rfl, rfl⟩ := Hon rfl`,
`isimp only [hboot] at Hetcd Hah`, `simp only [↓reduceIte]`). Untested guesses: the `simp only` on IPM goals, the
`kvInvM false` defeq in `memberBoot_of_slice` and `clusterFacts`' `iframe #`, `etcdClusterStart`'s `iexact Hetcd`
through `if false = true`. `dist/ClusterStart.lean`: `ClusterOk … (on := false)` (`ch0 = alarmChain on false false`,
trailing `∧ (on = true → cmp = false)`), `clusterFactsOf c (on := false)`, `ClusterNames.view c (on := false)`.
`MainLogger.lean:112` binds `hgps, -`. `ClusterStartD:501`'s projections are of early conjuncts (unchanged).

**Next:** read step 2's log; fix; build step 3; then step 4 (S2-2's design, `Hauthcmp` from
`WellFormed.authCompactorOff`); STATUS entry added at this handoff.

### Handoff S2-5 (2026-11-26; steps 2-3 green, step 4 started; context limit)

**Step 2 green** (`cc6ca7462d`, fk-lean2 EXIT 0 on every target). **Step 3 green** (`cbaabdcba4`: `41f0fcbf6f` fixed
`AllocN` (`rw [kvInvM_false/true]` before `iframe #`, `rw [if_pos (rfl : true = true)]` in the on arm, `isimp only
[hboot] at Hetcd` only, `memberBoot_of_slice` by `rw [clusterFacts, kvInvM_false]`, `etcdClusterStart`'s caller binds
`hgps, -` and reduces `Hetcd`); `cbaabdcba4` reduces `clusterAllocN`'s `if false = true` tail in `ClusterStart` and
`ClusterStartD`). EXIT 0 on `NewServerAllocOn`, `etcdserver.Results`, `dist.deployment.Link`, the `TopLevelRobustness`
of `dist`, `kvremote`, `putget`, `putgetk`. `etc/tier-check.py --check` ok (208 known), `etc/lease-order-check.py` ok.

**Step 4, first piece (the commit after `cbaabdcba4`; `NewServerAllocOn`, `Alloc3On`, `AllocN`, `auth/MainAlloc` checked
0 errors with `etc/lean-check.py -a` on fk-lean2; the full build was started at handoff, unread):**
- `srvMemberBootOn_alloc`'s post gains a trailing `∧ kvCongr ρ.rd.kv γk` (the mode-off one's; proof as there). Its
  restatement `server_member_alloc_on` (`etcdserver/Results.lean`) carries it (a stronger post of a package result;
  no top-level statement). Destructurings in `Alloc3On` and `auth/MainAlloc` end in `, -`.
- `etcdstart.memberBootOn_ofMC` (`Alloc3On`): the old `memberBootOn_ofM` with `∧ kvSame ρ.rd.kv γk ∧ kvCongr ρ.rd.kv γk`
  in its post; `memberBootOn_ofM` is now derived from it (same text as before).
- `etcdstart.memberBootOn_of_slice` (`AllocN`, which now imports `Alloc3On`): `memberBoot_of_slice`'s, at `clusterFacts …
  true`, `ch0 = alarmChain true …`, `cmp = false`, with **`hne : lm = .revocable → lease.leasesNoExpiry`**; post
  `memberBootOn … id false lm` with `st/c0/ch0/log0/hist/raft`, `kvSame`, `kvCongr`.

**Finding (blocks the premise removal; for the lead):** with auth on and the revocable lease mode, the member's boot
needs `lease.leasesNoExpiry` (no lease expires during the run): `NewServer_dist` takes `lease.bootCfg lm m on`, whose
auth row is `on = true → m = .revocable → leasesNoExpiry` (`LeaseApi.lean:69`), and `memberBootOn_ofM` takes the same.
`MainLogger`/`MainDeploymentLogger`/`MainDeployment` give only `lease.runCfg lm lm` (in the revocable mode: the
revoke levels and `srvRevokeOpen`, not no-expiry). So with `d.cfg.auth = false →` simply removed, `MainLogger` is
unprovable for an auth-on deployment in the revocable mode (and `AuthViewDist`'s `Lease_*On_dist` drafts are exactly
auth on + revocable). Options: (a) replace the premise by the weaker `(d.cfg.auth = true → lm = .revocable →
lease.leasesNoExpiry) →` in the three specs (implied by today's `d.cfg.auth = false`, so every caller still
discharges it; kvremote from M1's scope); (b) revisit the auth row of `lease.bootCfg` (`NewServer_dist`'s, an axiom: a
new review). (a) is within "premise weakening on intermediate specs" but is not plain removal: asking first.

**Next (in order):** (1) read the build started at handoff (fk-lean2 `~/eg/logs/f7l-build.log`, ends `EXIT n`; targets
the step-2 ones plus `etcdstart.Link` and `auth.Link`); fix (`etcdserver.Results`'s restatement was not checked alone). (2) The lead's choice above. (3) The rest of step 4, per
S2-2's design, unchanged: `memberShareD` passes `d.cfg.auth` to `ClusterOk`/`clusterFactsOf`/`view` and
`ClusterStartD` allocates at `on := d.cfg.auth` (`Hon` from `WellFormed.authCompactorOff` + `v3compactor.bootCfg_off`:
`cmp = false`, `cret = 0`); the auth-on `memberBuiltL`/split/`wp_Start_builtL`/`memberUpL_req`; the lessor-tied
`memberUpOn_intro` (`StartMemberAuth.lean:186-240`, `srvTLSId_false` with `iExactEq Hcca; rfl`); `MainLogger` split on
`d.cfg.auth` (off-only spots: Handoff S2-1); then the premises.

### Handoff S2-6 (2026-11-26; step 1 green, step 4 half done; context limit)

**Step 1 green:** the S2-5 build (`a915ee621e`; step 3's targets plus `etcdstart.Link` and `auth.Link`) EXIT 0.

**The coordinator's decision: option (a)** (ledger entry 2026-11-26, "the main-program specs' auth premise"). In
`MainLogger`/`MainDeploymentLogger`/`MainDeployment`, `d.cfg.auth = false →` becomes `(d.cfg.auth = true → lm =
.revocable → lease.leasesNoExpiry) →`; `member_boot_dist`'s `Hauth` too (kvremote passes `fun _ h => nomatch h`, since
`lm = .none` there). `MainDeployment*`'s proofs pass `Hauth` through unchanged. **Not applied yet.** It goes in one
commit with `MainLogger`'s auth-on branch, which it makes necessary.
**For the lead's F8:** the full theorem must discharge `leasesNoExpiry` for authLease. The single-process theorem does
this with its lease premises (`Spec/.../etcd/all/TopLevelRobustness.lean`, around lines 38-40 and 69-70).

**Step 4, done:**
- **`fe644e80d4`, built** (fk-lean2 EXIT 0: `MainLogger`, `dist.TopLevelRobustness`, `kvremote.TopLevelRobustness`;
  tier-check ok, 208 known; lease-order ok).
  - `memberShareD` at `ClusterOk … d.ids d.cfg.auth`, `clusterFactsOf c d.cfg.auth`, `etcdAddrAt … (c.view d.cfg.auth)`.
  - `compactorCfg_of_wf_auth`: with auth on, `cmp = false`, `cret = 0`.
  - `clusterStartDL` allocates at `on := d.cfg.auth`. Its `etcdKV` tail is `if d.cfg.auth then True else …`
    (`ite_drop_left`), and its client facts are at `c.view d.cfg.auth`.
  - `clusterStartD` and `member_boot_dist_law` take `(Hauth : d.cfg.auth = false)`; kvremote passes `Hscope.2`.
  - `MainLogger` reduces the share with `isimp only [Hauth] at Hshare`.
- **`b7c07b43f0` and the commit after it: the auth-on chain.** `etc/lean-check.py -a` on fk-lean2 gives 0 errors for
  both files; the full build has not run.
  - In `etcdstart/Start.lean`: `memberBuiltOnL` (`memberBuiltL` with `E.authMode = .on γa`, `isServerBuiltM true … (srvErM
    true …) … (bootKVOf true)`, plus `□ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD`), `memberUpOnL_intro` (the
    lessor-tied `memberUpOn_intro`), and `wp_Start_builtOnL` (`Start` at `.on γa`, giving `memberUpOnL`).
  - In `dist/server/MemberSplit.lean`, which now imports `Start`: `memberBuiltOnL_split` and `memberUpOnL_req`
    (`isServerReqM true`).

**Next, in order:**
1. **`MainLogger`'s split.** `cases hau : d.cfg.auth` at the share (replacing `isimp only [Hauth]` with `isimp only
   [hau]`). The off branch is today's proof. The on branch duplicates it with these differences:
   - `icases Hnames with ⟨Hlh, Hlslot, Hau⟩`; `Hau : authNamesFreshG (c.au idm)` becomes `authNamesFreshD` through
     `authNamesFreshG_iff`/`authNamesFreshD_iff_srv` (`MemberNames.lean:87-94`); check which form `Hγa` takes.
   - `obtain rfl : cmp = false := hlast hau` (`ClusterOk`'s last conjunct).
   - `memberBootOn_of_slice` (`AllocN.lean:398`; `hne := Hauth hau`, after the premise change) in place of
     `memberBoot_of_slice`. Its pure post has 11 conjuncts (the off one has 10): `…, hNx, hslg, hnoexp`.
   - No `memberCfg_off`: `cfg.Auth' = true`. Check that `serverConfig`'s `memberCfg` reduces at `d.cfg.auth = true`.
   - Call `wp_NewServer_dist true false`, simplified with `[NewServer.specG_dist, ↓reduceIte]` only.
     - Its `cmp → ¬on` premise is `fun h => nomatch h`.
     - `lease.bootCfg_of_run hslg (fun _ => hnoexp)`.
     - `Hγa` framed from `Hau`.
   - The post's last three are `#Hcca`, `#HBF`, `Hkeep`.
   - `isServerBuilt_of_gapM true`.
   - Build `memberBuiltOnL … (c.au idm) lm (c.ls idm)`, with the TLS row from `srvTLSId_false` and `iExactEq Hcca;
     rfl` (`memberCfg` leaves `ClientCertAuthEnabled'` false), and `HBF` applied to `⌜true = true⌝`.
   - Then `memberBuiltOnL_split`, `wp_Start_builtOnL`, `memberUpOnL_req`, and `NewPeerHandler_dist`/`PeerServe_dist`
     at `true`.
   - `Serve_dist` at `c.view true`: its premises `(fun _ => Hinj.2)` (from `Hsh`'s `NamesInj`) and `Or.inr` (`hist`
     agreement from `Hρ`), and its `if` reduced to `memberUpOnL`.
2. **The premise change (a)** in the three Spec files (fix the "-- the scope" comment), `member_boot_dist`, and
   kvremote's call (line 119).
3. Build `MainLogger`, `AdequacyMember`, the dist `TopLevelRobustness` leaves, `etcdstart.Link`, and `auth.Link`.
   Then run tier-check and lease-order. kvremote's statement text stays unchanged.

### S2 step 4 done (2026-11-26, after Handoff S2-6)

- **Confirmation build** of `f27e3cd99d` (`MainLogger`, `etcdstart.Link`): EXIT 0. `Start`'s `.olean` matched the
  commit's source, and `MemberSplit`, which imports it, was rebuilt. So the auth-on chain did compile; the 0.6s
  lean-check was incremental.
- **`df93c75c28`**, one commit:
  - `MainLogger` splits on `cases hau : d.cfg.auth`, after the common prefix (the share split once,
    `Hau` kept, `hch` rewritten per branch).
  - The auth-on branch follows the handoff's list. It has three new pieces:
    - `memberCfg_on` (`MemberSplit.lean`, beside `memberCfg_off`);
    - `memberCfg_tokenOk` (`NewServer_dist`'s token premise; `by decide` and `word` do not work inside the
      `wp_apply` term);
    - `NewServer`'s `cfg` given explicitly, as the goal's literal `configOf` record.
  - Option (a) is applied in `MainLogger`, `MainDeploymentLogger` and `MainDeployment`.
  - `member_boot_dist`'s `Hauth` is the same premise, now bound after `lm`. kvremote passes `fun _ h => nomatch h`, and
    `kvMemberBoot`'s scope binder becomes `_Hscope`, its statement unchanged.
  - Ledger entry marked applied.
- **Built** on fk-lean2: `MainLogger`, `etcdstart.Link`, the dist/kvremote/putget/putgetk `TopLevelRobustness`, EXIT 0.
  `tier-check` ok (208 known); `lease-order` ok. No `sorry`, no axiom.

### Handoff S3-1 (2026-11-26; steps 1, 2, 4 (in part), 5 done; step 3 blocked: `RunAuthLease` has no proof)

**Done** (the lead's approval, #50 06:08Z; nothing lands before F9's approval):
- **Step 1** (`93ab11f3ae`): `notes/axiom-review/f7-changed-since-review.md`. All 14 drafts were last reviewed at
  `6d9d9fd662` (`f7-rerev-{a,c}.md`; `f7-combined.md` at `5b15e37521` reviewed only NewServer/Serve). Changed since:
  **`KV_GetOn_dist` only** (re-review A's N1: `readCheckedD`/`readAuthedD` now give `srvReqLogLb γR L` at the permitted
  prefix, a stronger post, never reviewed). `Lease_TimeToLiveKeysOn_dist`: one comment line. The rest unchanged. The
  tie they rely on changed: `Serve_dist_proposed` adopted as `Serve_dist` (+ `etcdURLsFit` in `NewServer_dist`).
- **Step 2** (`c1328f9156`, built on fk-lean2, EXIT 0): the 14 drafts are `axiom etcd_dist.authd.<X>.wp_proof`, each in
  its own pair `Spec/.../dist/<F>.lean` + `Proof/.../dist/<F>.lean` (`<F>` in `etcd-dist-plan.md` §18.4, "Adopted
  2026-11-26 (F7 S3)"), statements byte-for-byte the drafts'; `AuthViewDist.lean` keeps the vocabulary (defs tier; the
  specs import it). Docstrings carry the reviews.
- **Step 4, in part:** `tier-check` ok (208 known), `lease-order` ok. **The base is unchanged by construction**: no
  module outside the 14 pairs imports them, so no root reaches them; `tcb-report --check`/`--update` not run (a full
  build for an empty diff). **The axiom-tok walk** run directly on the 14 (no root reaches them, so the script's
  tcb.json run would not): `notes/axiom-review/f7-auth-axiom-tok.md` — all 14 need an entry, all truncated; 11 have
  exactly `Client_Put_dist`'s accepted keys (rule 2 `8/1`, rule 7 `∃ P`), `Txn_CommitOn` rule 2 `10/1`, `KV_GetOn`
  rule 3 (`Q` produced 1), `New_user` rule 5 (`grpcConn`, ...) and `∃ scd`. No entries added.
- **Step 5** (`33409106a9`): 14 rows in `etcd-dist-f9-f2f7-rows.md`, routes in `etcd-dist-plan.md` §18.4.

**Step 3, blocked: what `RunAuthLease` needs** (`examples/etcd/dist/client/authlease.go:127`; nothing in Lean yet:
no `Spec/.../dist/client/RunAuthLease.lean`). Its single-process counterpart is `Proof/.../examples/etcd/authlease/`
(5.9k lines: `run.lean` 1382, `Cell`/`CellModel` 1.5k, `Refusals` 408, `LeaseAttempts` 276, `Holds` 186), over
`etcd_auth.SetUp.spec` (`auth/SetUp.lean` 414 + `SetupInv`/`SetupHist`/`SetupWrite`). The port, in order:
1. **A missing contract (for the lead: the 14 do not suffice).** `noAuth`'s third call, `cli.Lease.TimeToLive(ctx,
   id)` with **no options**, must be refused for the anonymous and the bad-token caller (`v3_server.go:700`,
   `requireAuthInfo` runs whatever `r.Keys`). No axiom covers it: `Lease_TimeToLiveKeysOn_dist` requires `leaseKeysFold
   gs false = true` (keys), and `Client_LeaseTimeToLive_dist` is view-free with no check in its success arm, so
   `refused` cannot be proved. Options: (a) generalize `Lease_TimeToLiveKeysOn_dist` (drop the keys premise; post
   `leaseCheckD … (fun info => if keys then leaseKeysVerdictFrom … else True)`): a statement change and a re-review;
   (b) a 15th axiom `Lease_TimeToLiveOn_dist` (approval + review). The single-process proof used `etcdLeaseTTLSpecMd`
   for both calls (`authlease/noAuth.lean:116`).
2. **Specs at the view for the dist client's helpers** (none exist): `newUserClient` (over `New_user_dist`),
   `barriers` (`New_user_dist` + `KV_GetOn_dist` per member, leaving `authFloorD` per member), `grantPut`
   (`Lease_GrantOn_dist`, `WithLease`, `KV_PutOn_dist`), `noAuth`, `foreign` (`Lease_RevokeOn_dist`,
   `Lease_TimeToLiveKeysOn_dist`, `Lease_LeasesOn_dist`: refusals by refuting `leaseCheckD`/`writeCheckedD`),
   `absent` (`KV_GetOn_dist`), `refused`, `reqCtx` (the bad token: `outTokOk none` via `¬ tokShape "badtoken"`).
3. **`etcd_auth.SetUp` at the view** (`SetUp.spec_dist`): the same Go, re-proved over `KV_PutOn_dist` and the five
   `Auth_*_dist` (with `histAu`/`SetupInv` at `Γ.kv`), through the anonymous `newClient` client.
4. **`RunAuthLease.spec`**: as `RunLeaseExpiry.spec` (eps of `leaseMember`s) plus, with auth on, the orchestrator's
   share of `etcdKV Γ.kv`'s client half and `authHistView Γ.kv` (`notes/etcd-dist-f7.md`, "How the workloads link";
   `MainLogger`'s auth-on branch must hand them out), `Γ.auth = true`, `Γ.kv.lm = .revocable`, the distinct-names
   premises; then the cell (`Cell.lean`) moved to `Γ.kv` and `Γ.ls mid`.
5. **Link and collection:** `wp_RunAuthLease` in a new root `Proof/.../dist/client/auth/Results.lean` (a separate
   `Results.lean`, so its collection is not `etcd-dist-lease`'s); then `etc/tcb-collections/etcd-dist-auth.txt`
   (`roots ^Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/auth/Results\.lean$`, header as
   `etcd-dist-lease.txt`'s). **Not created now:** `tcb-report` fails a collection whose pattern matches no root
   (`etc/tcb-report.py:381`), which would break `etc/gates.sh`. Then `tcb-report --check` (base diff = the auth axioms
   the link reaches), `--check --update` for base and collection, and the axiom-tok gate's real run.

### Handoff S4-1 (2026-11-26; S4 steps 1 (7 of 9 helpers) and 2 done; `noAuth`/`foreign` blocked on two view gaps)

**Done** (branch `etcd-safe-f7`, built on fk-lean2, tier-check ok (208 known), lease-order ok; no `sorry`, no new axiom):
- `d79d211b48`: the lead's choice (a): `Lease_TimeToLiveKeysOn_dist` generalized to any options and renamed
  `Lease_TimeToLiveOn_dist` (keys arm unchanged; without keys the check is `requireAuthInfo`'s, written
  `principalOf cfg = some info.Username'`, because `userOk` alone admits the empty user). `8330c5220b`: its fresh
  review `notes/axiom-review/f7-getOn-n1.md` (SOUND as drafted; must claim nothing of TTL/Keys), `KV_GetOn_dist`
  with N1 SOUND (keep `serializable = false`), retirement obligation R1 in its docstring; F9 rows cite it.
- `4359c342ff` (step 2): `etcd_auth.SetUp.spec_dist` / `SetUp.wp_proof_dist` (`auth/SetUpDist.lean`,
  `SetupInvDist.lean`): pre `userClientAt` + `authClientAt` of the anonymous client (`principalOf cfg = none`),
  `srvReqLogLb γR L₀`, the set-up puts' `writeAuD … L₀`, `authHistView Γ.kv [srvAuthSt0]`; post (ok) `authHistFrozen
  Γ.kv γz hs ∗ srvReqLogLb γR Lset ∗ ⌜admStates … Lset = hs ∧ srvAuthAtLog … Lset = setupSt r⌝`.
- `18155a8b18` (step 1, part): `dist/client/{reqCtx,refused,newUserClient,barrier,barriers,grantPut,absent}` and the
  defs module `AuthLeaseDefs.lean` (`reqMd`, `userCli`, `barrierFloor Γ γR L₀ addr := ∃ mid m, etcdAddrAt addr Γ mid ∗
  authFloorD Γ γR mid L₀ m`).

**Blocked (for the lead): two gaps of the view that refusals need.**
1. **`leaseCheckD` is vacuous for an anonymous principal when `K = True`** (`Lease_GrantOn_dist`,
   `Lease_RevokeOn_dist`): its info arm is `∃ info, ⌜userOk P info.Username'⌝ ∗ (admin ∨ K info)` and `userOk none ""`
   holds, so anon's/bad's Grant success cannot be refuted (the single-process proof used `principalBound tok (some
   info)`, false at no token). Proposed: `leaseCheckD`'s binding `P = some info.Username'` (true of etcd: with auth on
   a non-nil `AuthInfo` comes from an accepted token, which is `New`'s for `cfg`'s user); a change to four reviewed
   axioms (Grant, Revoke, TimeToLive, Leases), and `Lease_TimeToLiveOn_dist`'s no-keys `principalOf` clause becomes
   redundant.
2. **No per-member fix of the auth state after the barrier**: `authFloorD` gives `Γ.au mid`'s state at one index
   `i ≤ m`; a later lease check reads index `≥ n`. Refuting it needs the dist form of `akAuthFixed`: every state of
   `Γ.au mid` from the floor on is the frozen set-up state. Review `f7-getOn-n1.md`'s R1 lemma (from `authHistTie`:
   a later member state is `srvAuthAtLog L` at a committed `L ⊒ L'`) is exactly its core, so with the frozen history
   it follows from Serve's resources; at the view it needs a law (an axiom's post, e.g. `authFloorD` strengthened to
   `□ ∀ j st, i ≤ j → authStateAt (Γ.au mid) j st → ∃ L ⊒ L₀, srvReqLogLb γR L ∗ ⌜st = srvAuthAtLog … L⌝`).
3. Smaller: the dist `newClient.spec` post gives no `clientF cl "cfg" ↦□ cfg` with `cfg.Token' = [] ∧ principalOf cfg =
   none`, which `SetUp.spec_dist` and `noAuth` need: strengthen it (`etcdstart.NewClients` sets no user/password/token).

**Next:** after the lead's decisions: `noAuth` (the five calls; with (1) only "auth disabled" is left, refuted by (2)
since `setupSt` has auth enabled), `foreign` (callees as they are; premises: the caller's refutations, as
`authlease/foreign.lean`), `newClient`'s stronger post, then `RunAuthLease` (Handoff S3-1, items 4-5).
