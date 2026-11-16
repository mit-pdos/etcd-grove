# k8s 7f-6 stage C (the bridge): handoff

## START HERE
- Branch `k8s-7f6c` (worktree `/shared/etcd-grove-k8s7f6c`), based on `k8s-7f5` at `edf33c7a14`.
- Done: the plan, `notes/k8s-7f6c-plan.md` (target statement §1, counterexample §2, lemmas §3).
- **Stopped at the checkpoint (hard stop)**: the bridge needs F1 (at most one change under the prefix
  per revision), which `Q`'s laws, `KRelH` and `oneKeyRevs` do not give (plan §2). Waiting for the
  coordinator: strengthen the store's `KvNext` (recommended) or keep F1 as a named premise.
- Next, once decided: `KWatchBridge.lean`, lemmas 1-11 of plan §3, in that order.
- Pitfalls: `oneKeyRevs` is over the ghost history (state diffs), not etcd's changes; `KTail` is
  over `revEvents` (one event per change). `kvWfHist` at revision 0 makes the base empty (with
  `compacted = 0`), which gives F2.
- Build: no `.lake/build` yet; targeted `lake build --packages=/shared/tmp/manifest-e9e.json
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge` under
  `systemd-run --scope -q -p MemoryMax=64G`; `TMPDIR=/shared/tmp`.
