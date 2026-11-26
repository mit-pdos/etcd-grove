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
