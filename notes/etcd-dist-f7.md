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
