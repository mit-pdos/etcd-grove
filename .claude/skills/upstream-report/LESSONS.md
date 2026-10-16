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
- 2026-10-16, etcd-range-sort-none-limit (my own check before review): the version block was typed in a format
  `etcd --version` does not print. Rule (step 8): every output in `issue.md` is pasted from a run at the base,
  binaries built there; test output may be trimmed, not reworded.
- 2026-10-16, etcd-range-sort-none-limit: "Why should `SortOrder: NONE` give the same result as `ASCEND`? Is this
  documented?" It is not: `rpc.proto` says `NONE` is "no sorting"; only the server (#6672), its tests and `etcdctl`'s
  `--order` help say ascending. Rule (step 8, "What did you expect"): ground the expectation in a source the reader
  can check, read the docs before relying on them, and say so when sources disagree.
- 2026-10-16, etcd-range-sort-none-limit: "Shouldn't the fix just change etcdctl?" Rule (step 5): fix the layer where
  the defect is and name the alternatives (a client-side fix, changing the documented or tested behavior) in the PR
  with what each leaves broken.
- 2026-10-16, etcd-range-sort-none-limit: "The example with increasing limit is more clear that something is buggy;
  use it." Rules (step 8, "What happened"; step 4): lead with an example that is visibly wrong on its own (one
  request varied in a parameter, answers contradicting each other), and test that property.
- 2026-10-16, etcd-range-sort-none-limit: remove the unnecessary comment from the fix (the doc comment on the new
  helper `rangeSortOrder`, which restated its code). Rule (step 5): no comment that restates the code.
- 2026-10-16, etcd-range-sort-none-limit: "The issue does NOT need to explain the root cause; no mention of rangeLimit,
  sortRangeResults, etc." Rule (step 8, "What happened"; step 2; "Writing for upstream"): the issue has the symptom,
  the expectation and the reproduction only (no function names, code permalinks or history); the root cause goes in
  the PR and the commit message.
- 2026-10-16, etcd-range-sort-none-limit: "Get rid of the release comment. The note about the documentation is worth
  keeping, but since it is potentially actionable, the issue could ask a question." Rule (step 8, "Anything else"):
  no claims about other releases in the issue; an actionable side finding is a question to the maintainers.
- 2026-10-16, etcd-range-sort-none-limit: "Can the example that triggers the bug be made simpler?" Six puts (to make
  versions differ) became three (`put c 1; put b 2; put a 3`, `--sort-by=CREATE`). Rule (step 8, "What happened"):
  minimize the example to the commands the bug needs, on data where every target the text names reproduces.
- 2026-10-16, etcd-range-sort-none-limit: "Make the 'the same happens with' sentence more concise; we don't need to
  list all the command line flags in excruciating detail." Rule (step 8, "What happened"): what else is affected is
  one plain sentence, not a list of flags, enum values or client calls.
