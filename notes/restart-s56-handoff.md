# Restart S5/S6 handoff (branch `restart-s56`, worktree `/shared/etcd-grove-rs56`, from `lean` `90c3e25e77`)

Stage of etcd-grove-81: restart S5 (constructors: HS1 `NewAuthStore` over `authBoot`, `lateWBR`
deleted) and S6 (`NewServer` over both boots), against the restart/WAL interface
(`notes/wal-crash-handoff/restart-wal-interface.md`). S2 and C6 are deferred (the WAL collaborator).

## Phase: plan written, waiting for etcd-grove-81's approval (D1-D4). No Lean edited, nothing built.

- Plan: `/shared/tmp/restart-s56/plan.md`: the statements old → new (§1 S5, §2 S6), the hard stops
  (§3), the order and checkpoints CP1-CP3 (§4), the files and collisions (§5), the decisions D1-D4 (§6),
  and the risks R1-R5 (§7).
- Decisions go in the worktree's `questions.md` (untracked).

## Next, in order (once approved)

1. A0: baseline build (below).
2. A1: probe `Scratch/S56Probe.lean` (untracked; P1-P7 of the plan). CP1: report.
3. A2: texts in the files that are not the auth fix's. CP2: Freeze package, spec-reviewer, axiom skill. STOP.
4. Phase B, only after the auth fix lands: merge lean, edit `NewServer.lean`/`AuthSrv.lean`. CP3: STOP before land.

## Build

`export TMPDIR=/shared/tmp`;
`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json`
(retry once on 143). Targeted builds: the same command without `flock`, with the targets. Checks:
`LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py -a FILE`.

## Pitfalls

- `NewServer.lean`, `AuthSrv.lean`, `InvStart.lean`, `ServerOn*.lean` and `AuthCompRows.lean` are being
  edited by the auth fix (`/shared/etcd-grove-authfix`). Do not edit them before it lands.
- `.lake/build` was copied during another build, so it is partly stale. The first build rebuilds it.
- `Scratch/` is untracked: never `git add -A`.
