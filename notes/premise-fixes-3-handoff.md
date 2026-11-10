# premise-fixes-3: handoff

Branch `premise-fixes-3` (worktree `/shared/etcd-grove-pf3`, off lean `de9c19e020`). Both fixes
done (`notes/decisions.md`, "Premise fixes 3"); full build green, interfaces unchanged, tcb
baseline and collections `k8s`, `k8scompactor`, `k8setcd3` updated (2 axioms out, 2 in). Left:
gates, then `etc/land.sh` (the coordinator's go). On merging premise-fixes-1: take this branch's
gates step 9/9b.

Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
--packages=/shared/tmp/manifest-ddc.json`.
