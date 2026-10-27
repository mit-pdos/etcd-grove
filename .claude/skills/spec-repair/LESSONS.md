# Lessons from review

One entry per critique of a run: date, target, what the user said, the rule it became (in `SKILL.md`).

## 2026-10-27, the compactor pilot's specs (first review, `notes/spec-first-study/pilot-review-1.md`)

The author's self-review by the rubric found 4 problems; the independent review found those and 5
more, the most serious a vacuous guarantee no proof would have flagged. Rules (now the reviewer's
"Failure patterns"): check an environment contract's resource against the implementing callee's spec;
check that the post carries what the caller inspects; for each disjunction ask whether the weak side
is ever false; try the trivial model of an axiom family; check that trust-boundary facts can be
chained with what the caller holds; check every mode variant; compare configuration premises with
what the Go parser accepts. And: give the review to a fresh reviewer, not the author (the author's
review missed the vacuous disjunct it had itself written).

## 2026-10-27, the compactor pilot's specs (second review, `notes/spec-first-study/pilot-review-2.md`)

Three blockers, two of them introduced by the first round's repairs (a once-per-run token spent by a
retried call; a reader resource asserting "never compacted" in `Compact`'s spec), and one false
positive (a Go issue reported as unrecorded that `issues/` already had). Rules (in the reviewer's
"Failure patterns"): check retry paths for once-only resources; read the definitions of the resources
a spec takes; in later rounds, look hardest at what changed. For the orchestrator: always run another
round after repairs.

## 2026-10-27, the compactor pilot's specs (rounds 3 and 4, `notes/spec-first-study/pilot-review-{3,4}.md`)

Round 3: a permit parameter quantified per call is vacuous (each caller picks it); a resource missing
since round 1 (the slice the run token should own) that two rounds had missed; a Go defect no spec can
fix (the compactor run before `Start`), resolved by a fork fix. Round 4: nothing in the first tier,
but its first-ranked finding had been fixed after its snapshot. Rules: a parameter only in a
precondition, chosen by the caller, is vacuous; name the commit under review and compare with `HEAD`
before reporting; give the reviewer a context bundle (rounds take about 9 minutes, mostly reading).


## 2026-10-27, the compactor pilot's phase 3 (the `Run` proofs)

Four review rounds never counted the unfolds a client makes of another package's definitions; the
two `Run` proofs had three (the clock's `clockOk`, mvcc's initializer fact taken by position,
Perennial's `isContextDef`), each a missing law. The user's rule: a client of a good spec does not
unfold its definitions. Rule (the reviewer's "Failure patterns", and phase 3 of
`notes/spec-first-plan.md`): list every cross-package unfold in the callers' proofs, add the law to
the owning package, and freeze only with the list empty.

## 2026-10-27, the compactor pilot's round 5 (before the freeze, `notes/spec-first-study/pilot-review-5.md`)

The author's list of cross-package unfolds (made by grepping for the definitions the author had in
mind) missed one (`fmt.argsOk` in `New`); the fresh reviewer found it by reading every caller's
`unfold`/`simp only [...]`. Rule: build the list mechanically (every `unfold`, `iunfold`, `simp only
[...]` and positional `icases` of a package fact in the callers' proofs, filtered by the defining
module), not from memory; and a package's proof-only definitions (a loop invariant) go in a module
only that proof imports, not the package's public `Defs`.
