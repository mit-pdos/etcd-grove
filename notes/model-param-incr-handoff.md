# model-param-incr: handoff

Branch `model-param-incr` (worktree `/shared/etcd-grove-mpc`, cut from `lean` 0c3adbf69e), a session
of etcd-grove-81. Task: make gate 5b (`etc/model-param-check.py`) cheap; then (coordinator's change
of plan, 2026-11-11) profile and optimize `etc/ModelParamCheck.lean`, a fine-grained cache, and run
`etc/gates.sh`'s read-only gates in parallel. STOP before `etc/land.sh`.

## Done

- Profiled (scratch copies with timing lines, `/shared/tmp/model-param-incr/prof/`): rule 7 passed
  over every constant once per registration (36 x 25s on the main group); the main loop computed
  `isProject` per constant. Fixed in `etc/ModelParamCheck.lean` (one pass gathering the
  registrations' modules' theorems, in the same order; `isProject` per module index). Per group,
  old -> new (interpreted, JSON byte-identical): main 899s -> 23s, examples 3619s -> 148s, RaftWitness
  46s -> 13s, PorcupineDag 23s -> 6s, selftests (18, all ok) 30s.
- The judging's `code_line_ok` memoized (144k satax lines, 988 distinct): minutes -> 6s.
- `etc/model-param-check.py` caches each Lean run (per root group) in `/shared/tmp/model-param-cache/`,
  keyed by a SHA-256 of all its inputs (docstring); `--no-cache`.
- `etc/gates.sh`: steps 2-9 run in parallel after the build, output printed in order, any failure
  fails (planted-failure harness test: exit 1). reader-slot-check moved into the goose section (it
  reads `.lake/goose`, which goose.py maintains). Full gates, no-op build, model-param cached:
  693s sequential -> 462s parallel (tcb is the critical path); same output but reader-slot's place.
- Cache verification: cold (cache empty) 235s, warm 17s (5/5 cached), both JSON-identical to the old
  script's full run (6954s, under load); a scratch axiom in PorcupineDag's Results re-ran only that
  group (4/5 cached, 791 statements); a planted rule-1 violation there failed (also from the cache);
  reverted, rebuilt: 5/5 cached again (byte-identical .oleans).

## Next

- Accepted by etcd-grove-81 (2026-11-11); the fine-grained (per-statement) cache is NOT to be built
  (decided by etcd-grove-81: soundness risk for little gain).
- Land next, after premise-fixes-5, when etcd-grove-81 says so: merge lean, STATUS "Last updated"
  entry (status-history.md append-only), full build under the lock and 64G cap, then
  `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc
  etc/land.sh > /shared/tmp/model-param-incr/land.log 2>&1`. Never push.

## Pitfalls

- `lean --run` prints the checker's compile warnings to stdout: compare only the `{` lines.
- Run under `systemd-run --scope -q -p MemoryMax=32G`, `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`,
  on an up-to-date build. Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p
  MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`.
- Any edit to `etc/model-param-check.py` or `etc/ModelParamCheck.lean` changes every cache key.
