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

So clusters of 65 to 1000 (or to 300) members are covered only by the single-process theorems. Plan §6's
"no 300 bound" and "any `k`" meant "any `k` the predicate admits", and the predicate caps `k` at 64.

## 2. authlease: weaker refusal checks

The single-process `foreign` (`examples/etcd/authlease/authlease.go:193-208`) requires three refusals for a
lease holding a key the user may not touch: `Revoke`, `TimeToLive` with keys, and `Leases`. The dist
`foreign` (`examples/etcd/dist/client/authlease.go:102-120`) keeps only the `Revoke` refusal. For
`TimeToLive` with keys it checks only that a success returns no forbidden key, and it ignores `Leases`'
result. So single-process checks 4 and 5, and the `Leases` half of check 3, are not covered by the dist
theorem. A lagging member after the barrier may be why dist cannot demand these refusals under faults. That
explains why the dist theorem is weaker, but the single-process checks are still not subsumed.
