# Lessons from review

One entry per critique of a run: date, bug, what the user said, the rule it became (in `SKILL.md`).

- 2026-10-16, batch 2026-10-16 (several new issues): reproduction tests were left in the scratchpad or
  only quoted inline in the issue file. The user: "if you have new tests that you've written that go
  along with a new issue you've found, put the test next to the issue, so they get checked into the
  git repo". Rule (step 7): the test goes in `issues/<slug>/<name>_test.go`, with a header saying
  where it runs and how, linked from the issue file.
