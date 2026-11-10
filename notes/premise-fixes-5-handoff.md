# Premise fixes 5: handoff

Branch `premise-fixes-5`, worktree `/shared/etcd-grove-pf5`, off lean `f4e98c54f9` (its `.lake/build` a
full build at that commit, moved in from premise-fixes-2's worktree). Scratch: `/shared/tmp/premise-fixes-5/`.
Coordinator: etcd-grove-81.

Two findings:
- **A. ctxOk's Done gap** (7e-1's axiom attack, `/shared/tmp/k8s7e1/attack-wrb/`): `ctxQuiet` and
  `ctxErrs` (`Proof/google_golang_org/grpc/InvGrpc.lean`) say nothing of `Done()`, so the axioms taking
  `ctxOk` that select on `ctx.Done()` (`waitRetryBackoff`, grpc's `Invoke` through `grpcInvokerOk`,
  `NewStream`) are false of a context whose `Done()` panics, or is closed while `Err()` is `nil`.
- **B. keySized**: `mvcc.keySized` (`storage/mvcc/BackendBridge.lean`) assumed by `bootOk`'s `#Hsz`
  (`InvBoot.lean`), the restart contract's (`InvRestart.lean`) and mvccrand's `Hks`; to become one counted
  bbolt axiom `backend.rtxSnap_size` and a proved `keySized_all`.

## State

- Checkpoint (a) approved by etcd-grove-81 (2026-11-10; `questions.md`, untracked).
- Done (commits `704ebf5e6b`, `eed48b6f50`, `d35a230efa`, then the STATUS commit): A and B implemented
  as approved; `examples/premisefix/ctxdone` passes; `notes/axiom-review/ctxok-done.md`, audit rows
  (ctxOk, `rtxSnap_size`); STATUS entry. Targeted builds green for the changed client, backend and
  mvccrand modules; `NewServer`/`etcdserver.Results` fixed after the first targeted build
  (`ihave X := thm` for a `⊢ P` theorem, no `$$ []`).

## Done since

- lean `ef6bc4663b` (raft-entsize) merged (`1bf6ed29b3`, only STATUS/status-history conflicted).
- Full build green after the merge (13642 jobs, `/shared/tmp/premise-fixes-5/full2.log`); interfaces
  regenerated (3 files); `tcb-report --check`: exactly `+axiom backend.rtxSnap_size`; baseline (849
  entries) and 15 collections updated (`f08f4ae924`); gates steps 1-5 passed (build, links, tcb 844
  axioms 5 sorries, collections 53, goose 40, gen-init 223).
- Gates from 5b on (model-param-check takes over an hour) run as
  `/shared/tmp/premise-fixes-5/gates-rest.sh` (gates.sh without steps 1-5, root fixed), log
  `gates3.log`.

## Next, in order

1. Gates 5b-9b result; then checkpoint (b) report. Stop before land.sh.
2. If lean moves again (premise-fixes-4: context error facts' no-Format conjuncts, `rnSetLoggerOk`):
   merge, rebuild, tcb/collections again.

## Build command

```
export TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
