# Questions and pending decisions (lease-expiry, worktree /shared/etcd-grove-leaseexp)

Relayed by the user's session; answers come back by message.

## Q1 (2026-11-05): confirm the three approvals given through AskUserQuestion
The user approved, through the coordinator's AskUserQuestion dialog (recorded in
notes/lease-expiry-plan.md, "Decided (the user, 2026-11-05)"):
1. `lease.NewLessor.wp_proof`'s post gains `lease.leaseEver γl ∅` (E3 (c), route A);
2. E2 revision 5, the restated trusted `EtcdServer.leaseTimeToLive.spec`;
3. `etc/bounds-baseline.txt` +1 spec-thread / +2 spec-receipt (leaseexpiry `Main.spec`).
The Part E agent declined to act on them as relayed. The coordinator is proceeding on them
(they are the user's own answers); a veto here stops the work that uses them.
Depends on it: E2's application, E3 (c) stages 1-2, `Main`'s proof and link, trust base 785/7.
Recommendation: confirm.

## Pending before Freeze (hard stop)
- `axiom` skill on: `schema.MustUnsafeGetAllLeases.wp_proof` (new), `lease.NewLessor.wp_proof`
  (widened post), restated `leaseTimeToLive`, restated `lessorExpiredC`.
- P1: the Perennial thread-tokens-by-level change (upstream: a hard stop) to discharge
  `srvRevokeOpen_open`.
