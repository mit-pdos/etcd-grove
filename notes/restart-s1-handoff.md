# Restart S1 handoff (branch `restart-s1`, worktree `/shared/etcd-grove-rs1`)

Plan: `/shared/tmp/restart-scope/s1-plan.md`. Decisions: `notes/decisions.md`, "Restart S1".

## Done
- All of the plan's texts (§1.1-§1.11) implemented; `NewServer.lean` needed no edit (its `Hrnames`
  comes from `NodeStartSpec`, unchanged).
- Choice left to the implementer: the committed handed log `isCommittedLogLb γ.node.cl (srvLE γ.srv L)`
  is a conjunct of `rnLoopTokP` (every `onStop` exit has it, busy driver or not).
- `raftNode.start` reads `rnRestartOk` once before its loop (`rnLoopTok_restartOk`, `#Hrok0`).

- Verified (2026-11-11): full build clean (exit 0, `/shared/tmp/restart-s1/full.log`);
  `etc/tcb-report.py --check` matches the baseline (865 axioms, 5 sorries); every
  `etc/tcb-collections/*.txt --check` matches; `etc/gen-interface.py --check` clean for all five APIs
  (no interface diff: `RNNames`'s new fields reach no generated interface); `etc/gen-init.py --check` clean.

## Next
1. Report sent to etcd-grove-81; wait for its go, then merge `lean` and land with `etc/land.sh`
   (it runs the gates). Never push.

## Build
`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`

## Pitfalls
- `rnLoopTokP` gained two conjuncts at its end: every `icases` of it has two more names (`%Hc0, #HcL0`).
- `rn_ready_recv` takes `Hc0` and its post's both disjuncts end with `%Hcm`.
