---
name: proof-perf
description: Make this repository's full Lean build as fast as possible without changing what it proves — every result's statement, every definition the statements are written in terms of, every axiom and every `sorry` stay exactly as they were. Use when asked to improve build time or proof performance.
---

# Making the build faster

**Goal:** the full build of this repository (`lake build`) as fast as possible: its wall time (bounded
by the critical path on many cores) and its total CPU time (what bounds it on few cores, as on
CI's runner). Measure; keep only what is measured faster. `etc/timed-build.py` and
`etc/build-report.py` record and report a build's per-module times; `notes/decisions.md` ("Build
speed: …") and `notes/STATUS.md` ("Build performance") record what was measured and tried before.

**Constraint: what is proved does not change.** Only proofs get faster. The trust base (CLAUDE.md,
"Trust base") stays exactly as it is:

- edit only `Proof/**/*.lean`, and never a generated file there (`Link.lean`, `Init.lean`,
  `Initialize.lean`); not `Spec/`, `Code/`, `GeneratedProof/`, `etc/`, the lakefile, the manifest,
  the toolchain, or Perennial (a speedup that needs one of those is a proposal for the user);
- no change to a result's statement, to a definition a statement reaches, or to an axiom; no new
  axiom or `sorry`, nothing that weakens what the kernel checks (`native_decide`, `implemented_by`,
  `debug.skipKernelTC`, ...);
- the proof rules of CLAUDE.md ("Proof writing") still hold.

The constraint is checked mechanically. On a cold build of `origin/lean` before starting
(`fingerprint.py -o BASE`), and on a cold build of the result at the end:

| check | must |
|---|---|
| `lake build` | pass |
| `.claude/skills/proof-perf/check.py --base origin/lean` | no FAIL; each WARN explained |
| `.claude/skills/proof-perf/fingerprint.py -o NEW`, then `--diff BASE NEW` | no line differs |
| `etc/tcb-report.py --check`, and `--collection C --check --reuse` for each `etc/tcb-collections/*.txt` | pass, never `--update` |

`fingerprint.py` hashes, from the elaborated environment, the statement of every theorem of every
`Link.lean` and `Results.lean`, the type and body of every definition of this repository those
statements reach (translations included), and the type of every axiom declared here (about 6
minutes). `check.py` checks the diff's paths and added text. A change that fails a check is dropped.

**Deliverable:** a branch `perf/<YYYY-MM-DD>` off `origin/lean`, one commit per change with its
measurement in the message, pushed to `origin`; a line in `notes/STATUS.md`; and a report of the
build's wall and CPU time before and after, what was changed and what was tried and dropped. Never
merge it or push to `lean` or `main`; the user reviews it.
