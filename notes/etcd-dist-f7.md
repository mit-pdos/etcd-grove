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

- **Build: running, result unknown.** fk-lean2, `~/eg/wt/etcd-safe-f7` at `9a3a07ef29` (detached), script
  `~/eg/logs/f7m-build.sh` (flock `~/eg/.build.lock`, MemoryMax=55G), log `~/eg/logs/f7m-build.log` (ends `EXIT n`).
  Targets `~/eg/logs/f7m-leaves.txt` (= `etc/importers.py --leaves` over `S2Interim`, `MemberLessor`, `NewServerDist`,
  `ServeDist`, `AuthViewDist`, `AuthServeProposed`, `kvremote/TopLevelRobustness`, `client/RunLease*`: 24 leaves).
  Next session: read the log; on an error fix it (most likely spots: `AuthServeProposed`'s new `"Hlslot"`/`γl`, its
  `LessorSlot` import; `AuthViewDist`'s `readCheckedD`/`readAuthedD` with the new `L` parameter).
- `etc/tier-check.py --check`: ok (208 known violations, none new).
- Combined proposals: `NewServer.specG_dist_proposed` at
  `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthServeProposed.lean:104`, `Serve_dist_proposed.spec` at
  `:283` (same file).
