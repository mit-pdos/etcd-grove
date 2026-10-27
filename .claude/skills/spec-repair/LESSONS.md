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

