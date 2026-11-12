# Merging `specs-only` into `lean` as the part `SpecPlan/` (2026-11-12, branch `specs-merge`)

The branch `specs-only` (base `037bf21c75`, tip `267f2538fc`) replaced `lean`'s `Spec/`, `Proof/`,
`interface/`, `RaftWitness/` and `PorcupineDag/` by its specs. On `lean` (`49fff2f95c`, 619
commits later) its specs are a sibling part instead, next to the real specs and proofs:

- **`SpecPlan/Spec/`**: specs-only's `Spec/` tree (3236 modules), modules `SpecPlan.Spec.*`. Every
  `public import Spec.X` became `public import SpecPlan.Spec.X` (`Spec.PkgInit.*` and `Spec.smoke.*`
  included); imports of the shared translations (`GeneratedProof.*`, `GooseLang.*`) and of
  `Perennial.*` are unchanged. Path references in comments (`` `Spec/... ``, `` `Spec.X ``) were
  rewritten to `SpecPlan/Spec/...` where they mean this tree, not where they cite the old tree
  (specs-ref's, "the old ..."). Namespaces are unchanged (`Perennial.EtcdGrove.<Pkg>`): they are the
  main tree's, so nothing imports both trees, as with `RaftWitness/`.
- **`lakefile.toml`**: a `[[lean_lib]] SpecPlan` (`globs = ["SpecPlan.+"]`); `lean`'s `RaftWitness`,
  `PorcupineDag` and `Bbolt` libraries kept (specs-only had deleted the first two).
- **Scripts**: `etc/specs-build.sh`, `etc/specs-build-all.sh` (builds the `SpecPlan` library) and
  `etc/gen-specs-pkginit.py` (writes `SpecPlan/Spec/PkgInit/`, imports `SpecPlan.Spec.PkgInit.*`;
  `--check`). `etc/proof_roots.py` says why `SpecPlan/` is no part root (no roots, so the trust-base
  and verified-code scripts ignore it); `etc/errorf-wrap-check.py` skips it (it walked every `.lean`).
  The other checks only walk `Spec/`, `Proof/` and the goose parts' trees.
- **Notes and examples**: `notes/specs-only/**` (paths rewritten as above; README's first lines say
  where the specs now are), `examples/specreq/**`, `examples/etcd/crashreconf/**`, specs-only's new
  `issues/`/`nonissues/` and its edits to existing ones (none of which `lean` had changed since the
  base; `nonissues/raft-commit-lost-with-entries-kept.md` moved to `issues/`; indexes regenerated),
  and its edits to `notes/perennial-changes.md` (merged with `lean`'s later entries: both kept),
  `notes/rafthttp-http-boundary.md`, `notes/raft-durability-plan.md`,
  `notes/raft-conf-lag-model/guard-fix.md`, `notes/reconfiguration-{model-check,safety}.md`,
  `notes/parallel-work.md` (unchanged on `lean` since the base: taken whole). Lines specs-only added
  there have their `Spec/` paths rewritten. `notes/STATUS.md`: specs-only's section, retitled to the
  part. Not taken: specs-only's `lakefile.toml`, its CLAUDE.md banner, its deletions.

## Fixes for `lean`'s moved translations and Perennial

The Perennial pin did not move (`lake-manifest.json` unchanged since the base).

- `etc/gen-specs-pkginit.py` regenerated `SpecPlan/Spec/PkgInit/` against `lean`'s translations:
  new modules for the packages `lean` added (`github_com/spf13/pflag`,
  `github_com/mit_pdos/etcd_grove/examples/mvccfull`), and new dependency imports for
  `examples/k8s/etcd3` and `k8s_io/component_base/featuregate` (their translations import more
  packages now). No stale module (every one still has its translation).

No spec module needed a fix: `etc/timed-build.py SpecPlan` built all of them against `lean`'s
translations at the first try (6058 jobs, 3435 modules compiled, none failed; 15m05s wall on this
shared 24-core machine at load 30-45, 3h06m of CPU, of which the `SpecPlan` modules about 2h20m and
the rest the translations `lean` changed since the base; peak 2.6 GiB). So `SpecPlan` is one of
`lakefile.toml`'s `defaultTargets`: it adds about 2h20m of CPU, some 6-8 minutes of wall time on 24
cores, to a full build, and keeps every spec type-checking against the translations as they move.

## Checks

2026-11-12, on `specs-merge`:

- `etc/gen-specs-pkginit.py --check`, `etc/issues-status.py --check`, `etc/gen-init.py --check`,
  `etc/goose.py --check` (41 projects up to date: no translation changes), `etc/bounds-check.py
  --check` (374, the baseline), `etc/mode-check.py --check`, `etc/api-check.py` on every list,
  `etc/import-all-check.py --check`, the links, `errorf-wrap`, `errdesc`, `reader-slot`, `entsize`,
  `joint-landing`, `premisefix`: ok (`etc/gates.sh`'s sections, run without its full build).
- `etc/proof_roots.py`: the part roots are still `Bbolt`, `PorcupineDag`, `RaftWitness`;
  `SpecPlan/` is in none of its lists, so `etc/tcb-report.py --check` and `etc/verified-code.py`
  see nothing of it (no roots, no axioms, no `sorry`s by design).
- Not run here: the full `lake build` (and so `etc/tcb-report.py --check`, `model-param`,
  `pbschema`, which need the main tree's `.olean`s, and `etc/gen-interface.py --check`): the disk was
  at 97-99% (3-9 GB free), too little for a full build in this worktree, which was seeded only with
  the translations' build. The k8s gate's Go tests failed with "no space left on device" in `/tmp`
  (unrelated to this merge). Nothing in this merge changes a module of the main tree.
- `cd examples && go vet ./etcd/crashreconf/ ./specreq/...` ok; `gofmt -l` clean. `go test
  ./etcd/crashreconf/` against `lean`'s `examples/go.mod` (etcd `71f99a4b`, bbolt `ea4cab52`):
  the second run ok (23s, alone); the first was `Illegal`, with every initial member failing to
  listen on its fixed ports (`127.0.0.1:2430x`/`2431x`) for its first 5-23 s: another agent ran the
  same test at the same time (confirmed by the coordinator), and the two clusters collided. A
  harness limitation, not a regression: the ports are package constants, so two runs on one machine
  share them. Run it alone, or give it per-run ports (open).
