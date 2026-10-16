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
- 2026-10-16, etcd-range-sort-none-limit: "'How can we reproduce it' mentions a linked branch, but I'm not sure what
  the linked branch is. Insert a tentative link to the fork/branch/commit with the unit test. Don't explain the test
  in this issue, and make the unit test as simple as the etcdctl example." The test became the example (three puts,
  CREATE/NONE, limits 0-2), replacing a sweep over every target and order. Rules: step 8 ("How can we reproduce
  it"): link the test on the fork's branch, tentative until pushed, and do not describe it; step 4: the test is the
  issue's example, no wider; step 9: hand off the push command. The step-8 rule from the previous critique that let
  the test keep a richer setup is gone.
- 2026-10-16, etcd-range-sort-none-limit: "Make a standard comment we'll use for all these issue reports that
  indicate I was verifying etcd and using AI." Rule (step 8, "Anything else"; upstream's rules): every issue ends
  with the same disclosure, word for word: "I found this while formally verifying etcd, working with AI tools. I
  reproduced the bug and reviewed this report myself."
- 2026-10-16, etcd-range-sort-none-limit: "'The same happens with the other non-key sort targets, and for any client
  that sends SortOrder: NONE with one and a limit' is ambiguous ... It should be 'the same happens for any client
  sending SortOrder NONE with a non-key sort target and a limit'." Rule (step 9, "What happened"; "Writing for
  upstream"; `review.md` item 1): a list of conditions is one clause naming them all; no "one"/"it" for something
  earlier.
- 2026-10-16, after etcd-range-sort-none-limit was approved: "improve the skill so you would automatically make
  those revisions ... a few internal rounds might help, especially for making the report more concise and clearly
  written" (the aim: great reports in one shot). Restructured: the example is found first, by running it
  (`etcdctl-transcript.sh`), and the test and fix follow it (steps 4-6); step 9 is a section-by-section template
  after the approved issue (`example/issue.md`); step 10 adds review rounds (at most three): `check.py` for the
  mechanical rules, then a fresh reviewer agent with `review.md` (ambiguity and cuts first), until a round brings
  no change. The approved issue drops the setup puts' `OK` lines; step 9 now allows that edit (and trailing blank
  lines) and no other.
- 2026-10-16, etcd-range-sort-none-limit (trial of step 10 on the approved candidate): the reviewer found four real
  PR errors the user had not reviewed yet (no permalinks; a relative path; a manual test on other data, with ties;
  "the behavior since #6672" unexplained) and proposed cutting the user's limit sweep. Rules: `check.py` checks that
  named paths exist and warns on a PR without permalinks; step 10 rejects edits against the user's critiques;
  `review.md` keeps the sweep and checks manual claims against the example's data.
