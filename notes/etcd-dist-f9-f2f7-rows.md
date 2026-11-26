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

Not new: the auth-on drafts of `AuthViewDist.lean` (definitions, no axiom) stay drafts; with auth on, the deployment
has no path yet (L5, `notes/etcd-dist-f7.md`).
