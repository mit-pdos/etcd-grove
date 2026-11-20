# k8s 7g follow-up (B'): handoff

## START HERE

Brief: `notes/k8s-7g-listaccessor-bprime.md` (approved by the user to start after wal-fsfix). Context:
`notes/k8s-7g-trust.md` §11-§12. Worktree `/shared/etcd-grove-bprime`, branch `k8s-bprime` off lean
`cd4e31df13`; manifest `/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`;
`.lake/build` seeded from `/shared/etcd-grove-k8sunified` (built at `f7f4930794`). Scratch:
`/shared/tmp/bprime/`. The k8s closed theorems are one now: `k8s_safe`/`k8s_robust`
(`examples/k8s/all`, collection `etc/tcb-collections/k8s-all.txt`); they must stay textually unchanged.

State (2026-11-20):
- Q1, Q2 APPROVED by the user 2026-11-20 via etcd-grove-03 (also in the worktree's `questions.md`).
- Done: goose config (patch reproduced), `ListAccessor.spec` restated and proved; 7g callers through
  `correctness/ListAccessorObjList.lean`; pager/reflector over `cache.typedListMeta` (pending `?` entry of the
  k8scache list); Links regenerated (only the cache's changes); `TestTypedListMeta` (daemonset/apimodel) and
  `TestListAccessorObjList` pass; tcb baseline -1, clientgo-cache -1, k8s-all -1; notes `k8s-7g-trust.md` §13,
  STATUS entry.
- Builds: full timed `20261120-161449-844527` (at 2a3a51669a), after merging lean 9d6a486a91 incremental timed
  `20261120-164052-938906`, both green.
- Next: gates (`etc/gates.sh`), then LAND STOP (the coordinator runs etc/land.sh).
