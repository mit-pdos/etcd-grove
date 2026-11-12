# Brief: re-review after the repairs (2026-11-09)

The verification round (`verify-brief.md`, reports `notes/specs-only/verify/A*.md`) found first-tier
findings in most areas; 14 repair groups fixed them (`verify/repair-*.md`). You are a fresh,
independent reviewer of one area (your prompt names it and its two reports). Read-only, except your
report.

Read first: `notes/specs-only/README.md`, `.claude/skills/spec/PRINCIPLES.md`, `verify-brief.md` (what
provable and complete mean here), then your area's two verify reports (`A<n>-…-provability.md`,
`A<n>-…-completeness.md`). Do **not** read the repair reports until you have written your own verdict on
each finding; afterwards you may read them to check a disagreement.

## What to do

1. **Each first-tier finding** in your two reports: is it resolved in the specs/snippets as they are now?
   Check the spec text itself (file, line) against the Go code (`.lake/src/…`), not the author's
   description. Resolved / resolved differently (and fine) / not resolved / resolved but recorded as an
   open user decision (name it, `open-questions.md`).
2. **Regressions.** For every spec file in your area changed since commit `1aa6fc1337`
   (`git diff --stat 1aa6fc1337 -- <your dirs>`; read-only git is fine): does it still close (a proof plan
   from its callees' specs as they are now; premises with sources; posts strong enough for its callers'
   sketches)? Is anything false of the code, or inconsistent (a way to prove `False`, or a panicking
   program proved safe)? New laws: plausible from their stated realization, not vacuous.
3. **Snippets** changed or added in your area's `examples/specreq/` packages: provable from the specs
   under their stated assumptions; do they cover the user patterns the completeness report listed?

## Report

`notes/specs-only/verify/R-<area>.md`: per batch, PASS / PASS WITH OPEN DECISIONS (name them) / FAIL; a
table of the original first-tier findings with their status; new first-tier findings (file, step, evidence,
suggested fix); counts. Final message: the verdict per batch and new first-tier findings, one line each.
