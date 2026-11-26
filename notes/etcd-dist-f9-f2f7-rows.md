# F9 packet rows: F2 + F7 (leases and the auth view on the no-crash line), 2026-11-26

Branch `etcd-safe-f7`. One row per axiom this change adds to the trust base of `etcd_safe_nocrash`'s line, and the
two axioms it replaces. Reviews are in `notes/axiom-review/`. The ordering gate `etc/lease-order-check.py` (in
`etc/gates.sh`) refuses a link of the six lease axioms while any serve axiom of etcd's table does not tie the
member's lessor to `Γ.ls mid` (f7-combined.md §3's caveat).

**State (2026-11-26, `eb138f6f8c`):** the replacement is made (both axioms in one commit, the old `Serve_dist` deleted;
the lead's option (a): `putgetK_safe` stays, its placeholder `StartMember_dist` gives `memberUpL`), built on fk-lean2
(putget/putgetk/kvremote `TopLevelRobustness`, `etcdstart.Link`, `etcdserver.Results`). The six lease axioms are still
unlinked (`notes/etcd-dist-f7.md`, Handoff 6).

## The replaced axioms

| axiom | Today | With this change |
|---|---|---|
| `etcd_dist.NewServer_dist.wp_proof` (`Spec/.../dist/NewServerDist.lean`) | (before `eb138f6f8c`) `NewServer.specG_dist`: the server's auth names are `∃ γa` in the post, its lessor name is NewServer's own; `etcdURLsFit` dropped | `NewServer.specG_dist` (since `eb138f6f8c`): binders `γa`, `γl`; premises `etcdURLsFit U.peer → etcdURLsFit U.client →` (carried back from `NewServer.specG`), `"Hγa"` (auth on: `authNamesFreshD γa`) and `"Hlslot"` (`ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl`); post `E.authMode = .on γa` (auth on) and `mvccLeases E.γ = γl`. Review: `f7-combined.md` §1, SOUND; `f7-diff-vs-inprocess.md`. |
| `etcd_dist.Serve_dist.wp_proof` (`Spec/.../dist/ServeDist.lean`) | (before `eb138f6f8c`) auth off only (`Γ.auth = false`), `etcdstart.memberUp` (no tie of the member's lessor or auth names to `Γ`) | `Serve_dist.spec` (since `eb138f6f8c`, the reviewed text verbatim): `kvCongr ∧ (Γ.auth = false ∨ hist agrees)`, `memberUpOnL … (Γ.au mid) Γ.kv.lm (Γ.ls mid)` (auth on) or `memberUpL … Γ.kv.lm (Γ.ls mid)` (auth off), distinct `Γ.au` with auth on. Review: `f7-combined.md` §1, §3, SOUND provided it replaces the current one (the gate enforces the order). |

## The new axioms (in the trust base once leaseRead/leaseCatchup/leaseExpiry are linked)

| axiom | what it asserts | review | retirement route |
|---|---|---|---|
| `etcd_dist.view.Lease_Grant_dist` | a `LeaseGrant` RPC to member `mid` at the view `Γ` meets `lessor.Grant`'s contract at the member's lessor `Γ.ls mid` (mono mode), names distinct over `w64` | `f2-lease-axioms.md`; `f7-combined.md` §3 | S2's `etcdSvc` handler entries (`notes/etcd-dist-plan.md` §18.4: the in-process `lessor.Grant.spec` at `etcdLeaseGrantSpec γl` through grpc's server) |
| `etcd_dist.view.Lease_GrantLive_dist` | the same in revocable mode (`etcdLeaseGrantSpecLive`) | same | same (§18.4) |
| `etcd_dist.view.Lease_LeasesGranted_dist` | a `LeaseLeases` RPC lists a superset of the leases granted at `Γ.ls mid` before it (mono) | same | `lessor.Leases.spec` at `etcdLeaseLeasesSpec γl` (§18.4) |
| `etcd_dist.view.Lease_LeasesLive_dist` | the same in revocable mode, with the absent-stays law | same | `etcdLeaseLeasesSpecLive γl` (§18.4) |
| `etcd_dist.view.Client_LeaseTimeToLive_dist` | a `LeaseTimeToLive` RPC (no options) meets `lessor.TimeToLive`'s contract at the member | `n9b-lease-ttl.md`, `lease-ttl-*.md`; `f7-combined.md` §3 | `etcdLeaseTTLSpec` (§18.4) |
| `etcd_dist.view.Client_LeaseLeases_dist` | a `LeaseLeases` RPC returns a well-formed listing (no history claim) | `n9b-lease-leases.md`; `f7-combined.md` §3 | `etcdLeaseLeasesSpecAny` (§18.4) |

## The auth axioms (F7 S3, 2026-11-26; in the trust base once `RunAuthLease` is linked, collection `etcd-dist-auth`)

The lead's approval (#50 06:08Z). Namespace `etcd_dist.authd`, each in its own Spec/Proof pair under
`Proof/.../dist/` (file names in `notes/etcd-dist-plan.md` §18.4, "Adopted 2026-11-26 (F7 S3)"); the vocabulary is
`AuthViewDist.lean`. Every one is tied to the member by `Serve_dist`'s auth-on premise (`memberUpOnL` at `Γ.au mid`,
`Γ.ls mid`); every error arm claims nothing. Changed since review: `notes/axiom-review/f7-changed-since-review.md`.

| axiom | what it asserts | review | retirement route |
|---|---|---|---|
| `etcd_dist.authd.New_user_dist` | `clientv3.New(cfg)` with a user name, at an auth-on view: success names the member `mid` that answered and its `CheckPassword` verdict at `Γ.au mid` (or auth disabled there) | `f7-a.md` (UNSOUND: free `A`) → f7-rerev-a.md (`6d9d9fd662`) SOUND (Serve tie); unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.KV_PutOn_dist` | an auth-on `Put` (with or without a lease, revocable mode) meets `client_put_on`: the persistent update fires once at commit, a success tells the serving member and its grant (`writeCheckedD`) for the principal of `cfg` | `f7-a.md`, f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.KV_DeleteOn_dist` | the same for `Delete` (`client_delete_on`) | `f7-a.md`, f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Txn_CommitOn_dist` | an auth-on `Txn.Commit` (linearizable): read-only, the member's `txnClassFrom` check at its published index (`txnReadCheckedD`); writing, the grant of `irrTxn` (`writeCheckedD`) | `f7-a.md` (UNSOUND: free `A`) → f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.KV_GetOn_dist` | an auth-on linearizable `Get` meets `client_range_on`; a success names the member, its verdict at its published index above the barrier's floor (`authFloorD`), and the cluster-level permission at a committed prefix `L ⊒ L₀` (`readCheckedD`) | `f7-a.md` (UNSOUND) → f7-rerev-a.md (`6d9d9fd662`) SOUND + N1; **N1 applied since, unreviewed** (`f7-changed-since-review.md`) | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Auth_UserAdd_dist` | `UserAdd` through any client: the caller's persistent history update fires at the admitted entry; a success is `adminRepliedD` (member, admission after the requested prefix, the update's `Q`) | `f7-b.md` (NEEDS-FIX: name bound) → f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Auth_UserGrantRole_dist` | the same for `UserGrantRole` | `f7-b.md`, f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Auth_RoleAdd_dist` | the same for `RoleAdd` | `f7-b.md`, f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Auth_RoleGrantPermission_dist` | the same for `RoleGrantPermission` | `f7-b.md`, f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Auth_AuthEnable_dist` | the same for `AuthEnable` | `f7-b.md`, f7-rerev-a.md (`6d9d9fd662`) SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Lease_GrantOn_dist` | an auth-on `Grant` at member `mid` (revocable): the persistent update at the granted id, the lease live at `Γ.ls mid`, and the member's `requireAuthInfo` check (`leaseCheckD`) at its published index `≥ n₀` | `f7-c.md` (NEEDS-FIX F1, F2) → `f7-rerev-c.md` (`6d9d9fd662`) SOUND given the adopted Serve; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Lease_RevokeOn_dist` | an auth-on `Revoke`: a write through raft (`writeAuD`), its grant of `irrLeaseRevoke` (`checkLeasePuts`) and member `mid`'s `requireAuthInfo` | `f7-c.md` (NEEDS-FIX F1) → `f7-rerev-c.md` SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Lease_TimeToLiveOn_dist` (was `Lease_TimeToLiveKeysOn_dist`; **generalized before approval**, 2026-11-26, the lead's choice (a)) | an auth-on `TimeToLive(id, opts...)` at member `mid`: the echoed ID and, with attached keys, the member's keys verdict (`leaseKeysVerdictFrom`), without, the info's user the principal (`requireAuthInfo`), at its published auth index and lessor index, or an admin pass | `f7-c.md` (UNSOUND as written) → `f7-rerev-c.md` SOUND (keys form); generalized since: **needs a fresh review** | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |
| `etcd_dist.authd.Lease_LeasesOn_dist` | an auth-on `Leases` at member `mid` (revocable): its lessor's listing at `j ≥ m₀`, and its check (admin, or every listed lease's keys readable) | `f7-c.md` (UNSOUND as written) → `f7-rerev-c.md` SOUND; unchanged | S2's client side: the in-process contract as an `etcdSvc` entry (§18.4, "Adopted 2026-11-26 (F7 S3)") |

Not linked yet: `RunAuthLease` has no Lean spec or proof (`notes/etcd-dist-f7.md`, "Handoff S3-1"), so the base
(`etc/tcb-baseline.txt`) does not contain them and the collection's baseline is empty.
