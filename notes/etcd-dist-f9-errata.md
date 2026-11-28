# F9 packet: errata on its coverage (2026-11-27)

The F9 packet says the distributed `etcd_safe` covers "every workload" of the single-process theorems. It does,
with two limits that the packet and `notes/etcd-dist-plan.md` §6/§13 did not state. Source: the coordinator's
rule-41 subsumption review (`rule41-subsumption-proposal.md`, §2.7 and §5).

## 1. At most 64 members

`deployment.MaxMembers = 64` (`examples/etcd/dist/deployment/deployment.go:91`; Lean `maxMembers`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/DeploymentDefs.lean:204`). `Deployment.WellFormed`
admits no larger cluster. The single-process theorems reach larger ones:

- txnlinfaultsN up to `k₁ ≤ 1000` members, and leaseexpiryN up to 1000 (`leaseexpiryN.go:159`);
- authN, authlease and leaseN up to 300 (`examples/etcd/all/checked.go:132-137`).

**Resolved 2026-11-27** (rule 41 item 2, `283810f2f8`): `MaxMembers = typed.maxMembers = 1000`, the interim
axiom `bootstrap.wp_proof_dist`'s premise raised with it. Before that, clusters of 65 to 1000 (or to 300) members
were covered only by the single-process theorems. Plan §6's
"no 300 bound" and "any `k`" meant "any `k` the predicate admits", and the predicate caps `k` at 64.

## 2. authlease: weaker refusal checks (not a coverage gap)

The single-process `foreign` (`examples/etcd/authlease/authlease.go:193-208`) requires three refusals for a
lease holding a key the user may not touch: `Revoke`, `TimeToLive` with keys, and `Leases`. The dist
`foreign` (`examples/etcd/dist/client/authlease.go`) keeps the `Revoke` refusal and proves the property behind
the other two: no reply discloses a key the caller cannot read (`TimeToLive` with keys is refused or carries no
forbidden key; `Leases` returns lease IDs only). The single-process refusals tested etcd's all-or-nothing policy
(`checkLeaseTimeToLive`, `checkLeaseLeases`), and etcd does not keep that policy while a member applies a
snapshot, which the dist cluster does: `applySnapshot` calls `lessor.Recover`, which reloads every lease with
no key attached, before `kv.Restore` re-attaches the keys (etcd `main` `4e090c033`: `server/etcdserver/server.go:1067,1074`,
`server/lease/lessor.go:820-826`, `server/storage/mvcc/kvstore.go:403-413`), and both checks read the receiving
member's lessor in between. Evidence: `TestV3LeaseAuthDuringSnapshotRestore`
(`issues/etcd-lease-auth-snapshot-restore-keyless.md`, branch `issues-leasegap/2026-11-27`) fails at etcd `main`
4 runs of 4 with no failpoint: a user who may not read `z/lease` gets `Leases` answered and `TimeToLive(Lz, keys)`
answered with `["z/lease"]` at a follower restoring a snapshot. At the old pin `df6af0c36a` the same follower
case is `notes/etcd-dist-f7-bprime.md`'s `TestF7bLeaseKeysAfterSnapshot` (branch `etcd-safe-f7-bprime`); the
verified fork `d26dd5da6` re-checks the returned keys (`checkLeaseTimeToLiveKeys`), which makes the property hold
for `TimeToLive`, not the refusal (a leader restoring a snapshot answers from its own half-restored lessor:
`nonissues/etcd-lease-keys-mid-apply.md`, inference, not tested). So the property is proved; the refusal is a
policy etcd cannot guarantee during a snapshot's apply (Upamanyu's option (a), 2026-11-27). The earlier guess (a
member lagging after the barrier) was wrong: the barriers rule plain lag out.

