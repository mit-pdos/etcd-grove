---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# lease: `SetCheckpointer` is safe only once, before the lessor is primary

`lessor.SetCheckpointer(cp)` stores `le.cp` under the lessor's lock, but its readers test `le.cp`
under the lock and call it after releasing it: `Renew` (`clearRemainingTTL := le.cp != nil && ...`
under the read lock, `server/lease/lessor.go:412`; the call `le.cp(...)` at `:437`) and the run loop
(`findDueScheduledCheckpoints` returns nothing when `le.cp == nil`, `:773`; `checkpointScheduledLeases`
calls `le.cp(...)` unlocked, `:679`). A `SetCheckpointer(nil)` between the test and the call makes
Go call a nil function (a panic); a `SetCheckpointer(cp2)` there is a data race. The `Lessor`
interface (`lessor.go:89`) does not say it must be called at most once, before use.

**Why not an issue:** a precondition etcd meets. The server calls it once, in `NewServer`
(`server/etcdserver/server.go:395`), before the member can be the leader (the lessor calls the
checkpointer only when primary, after `Promote`, which the apply thread calls after `start`). No
test; found by the review of batch 3c (specs-only branch).

## Proof

no: `lessor.SetCheckpointer.spec` (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease/lessor__SetCheckpointer.lean`)
takes a once token (`Lease.lessorCkptTok`) that `NewLessor` gives; the server's one call has it.

## Notes

Documentation fix, if wanted: "SetCheckpointer must be called at most once, before the lessor is
promoted." Or read `le.cp` once under the lock and call the copy.
