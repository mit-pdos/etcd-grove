# leaseN handoff

## START HERE (2026-11-16)

- Branch `leaseN`, worktree `/shared/etcd-grove-leaseN`, off lean `5d2a12df97`. Not landed, not pushed.
- Stage: `etcd_lease_safe` and `etcd_leaseexpiry_safe` at `k` members (`1 ≤ k ≤ 1000`) on the generic start, as N
  versions beside the one-member theorems. The plan: `notes/leaseN-plan.md`.
- Done (this run, one commit on top of lean):
  - the plan (statements §2, decisions D1-D12 §8);
  - Go: `examples/etcd/leaseN` (reads at every member, mode none, token `leaseN-2422`, ports 10000/11000) and
    `examples/etcd/leaseexpiryN` (a grant through every member, each member's listing polled until its lease is gone,
    then listed again; token `leaseexpiryN-1973196`, 15-bit apart; ports 12000/13000, its tests 14000-14306);
  - tests pass (`TestMemberIDs`, `TestMembers`, `TestMainRun` for k ∈ {1,2,3,5,7,9}, `TestRunChecked`,
    `TestTTLThroughFollowerPanics`), log `/shared/tmp/leaseN/runs.log`.
- **Open: HARD STOP, the statements (plan §2) and D1-D12 with the user.** Nothing in Lean yet.
- Next, in order (after approval): plan §6 items 1-6 (build, translation and gen-init, leaseN's proofs, leaseN's
  linking and landing stop, leaseexpiryN's proofs, its linking and landing stop).
- Then (D10): `leasecatchupN`, a stage of its own (Figure 2 row, 3 members today).

**Pitfalls**
- The one-member leaseexpiry check (`TimeToLive` not found, then `Leases`) panics through a follower: the examples'
  peer listeners answer `/leases/internal` with 404, read as not found (`TestTTLThroughFollowerPanics`). Do not port it.
- A member's "not listed" says something only of a lessor that held the lease: each member checks the lease granted
  through itself (the proposer applied the grant before answering).
- auth-lease S4 (`/shared/etcd-grove-rs56`) changes the client lease specs (`lessor.*.spec` to the metadata form) and
  the C5′ contracts: do not edit those modules; expect to adapt proof bodies at merge (plan D12).
- Go tests: `GOWORK=off PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`, under `systemd-run --scope -q -p MemoryMax=32G`;
  `/shared/tmp/leaseN/runs.sh` reruns the matrix. Do not stop members in tests whose peers still serve the raft
  handler (net/http logs the handler's recovered "raft: stopped" panic).
- No `.lake/build` here yet: seed only per the common rules' disk section, else targeted builds with
  `--packages=/shared/tmp/manifest-e9e.json`.
- STATUS.md's "Last updated" entry is left for landing (nothing landed in this run).
