# Lessons from review

One entry per critique of a candidate: date, finding, what the user said, the rule it became (in `SKILL.md`).

- 2026-10-16, setup: start fix branches from current upstream `main`; the existing fix branches on the fork are not
  a starting point. (SKILL.md, "Where things are".)
- 2026-10-16, setup: no fork of etcd-io/website until a PR there is actually needed. (SKILL.md, "Where things are".)
- 2026-10-16, etcd-txn-delete-then-ignore-put (my own run, for the user's review): the root cause was already public
  with an open fix PR (#22395) that did not know the impact (every member panics, permanently). Rules added to
  step 3: search for the root cause as well as the symptom, read the matches' comments, verify an existing PR
  against the finding's reproductions instead of making a competing branch, and treat the impact, not the root
  cause, as what a security disclosure is about.
