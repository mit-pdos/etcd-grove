---
name: upstream-report
description: Turn a finding in issues/<slug>.md into an upstream-ready candidate — a GitHub issue text, a fix branch off upstream main with a regression test, and a PR description — for etcd-io/etcd, etcd-io/raft or etcd-io/website. Use when asked to report, file, draft, or fix an issue from issues/ upstream, or to revise a fix branch after review. Never pushes or files anything.
---

# Reporting a finding upstream

From one finding, `issues/<slug>.md`, produce for the user to review:

- a fix branch `fix/<slug>` in `~/etcd-fixes/<slug>`: signed-off commits off current upstream `main`, first the
  tests (which fail at that commit), then the fix, then (if the repository keeps one) the changelog entry;
- `issues/upstream/<slug>/issue.md`, `pr.md` and `meta.md` (base commit, commands run and results, duplicates
  found, answers to likely reviewer questions, state).

Never push, file, or comment on GitHub; the user does. Aim for a candidate the user can file as it is.
`example/issue.md` and `example/pr.md` are approved candidates: match their shape, length and tone.

| Target | Clone | Remotes |
|---|---|---|
| etcd-io/etcd | `~/etcd` | `upstream` etcd-io/etcd, `origin` upamanyus/etcd |
| etcd-io/raft | `~/etcd-raft` (clone on first use) | `upstream` etcd-io/raft, `origin` upamanyus/etcd-raft |
| etcd-io/website | `~/etcd-website` | `upstream` etcd-io/website (no fork) |

`git -C <clone> fetch upstream && git -C <clone> worktree add ~/etcd-fixes/<slug> -b fix/<slug> upstream/main`. Never
base a fix on the fork's branches (Goose branches, old fix branches). From a session isolated in an etcd-grove
worktree, git in `~/etcd*` is refused: leave the worktree (keep) for that work and re-enter it by path.

## Upstream's rules

- Commits, so that the tests can be seen to fail before the fix: first the tests only (`*_test.go`, subject
  `<package>: test <what>`), then the fix (subject `<package>: <what changed>`, the PR's title), then, where the
  repository has a changelog for the next release, its entry alone (`changelog: add entry for <what>`, no body; the
  link `pull/TODO` until the PR exists). Messages are as short as upstream's: most etcd and raft commits have no
  body, and nine in ten at most three lines. The tests commit says only that the test fails until the next commit;
  the fix commit says in a sentence or two what was wrong and what changes, in words rather than function names,
  without restating the diff. Subjects at most 72 characters; the prefix the package's history uses (`client/v3:`,
  `etcdserver:`, `raft:`). `git commit -s`, no AI trailer of any kind. The messages are drafts the user rewrites
  (etcd does not accept AI-written messages). Amend the commits until the PR is open.
- The issue and the PR each end with their standard AI disclosure (below). Replies to reviewers are the user's.
- A bug a client with ordinary access can use to crash or hang a member, lose or corrupt acknowledged data, or
  bypass auth is a security report: before writing anything public, stop and let the user decide (etcd's
  `security/README.md`). A public duplicate of the root cause does not make the impact public.

## Procedure

1. **Read** the finding and what it links to. Its wording is for this repository; none of it carries over as is.
   Pick the target: code and Go doc comments are in etcd or raft, operator docs in etcd-io/website.
2. **Re-check** at current `upstream/main` that the code is unchanged; record the base commit. If fixed, update
   the finding and stop.
3. **Duplicates**, in a background agent while you do steps 4-7: at most five searches
   (`curl -s 'https://api.github.com/search/issues?q=repo:etcd-io/etcd+<terms>'`; about ten a minute are allowed
   unauthenticated) for the symptom and the root cause; open only matches that look like the same bug. If an open
   PR fixes it, stop and tell the user. Record matches in `meta.md` and the finding's front matter
   (`issues/README.md`).
4. **The example**: the reproduction, in whatever form the bug needs (usually a Go test; `etcdctl` commands, a
   client program, a cluster configuration when that is what shows it). Build binaries only if it needs them. Run
   it at the base and make it:
   - visibly wrong on its own: the same request varied in one parameter, giving answers that contradict each other;
   - minimal: the fewest steps, keys, values and options, choosing the variant of the bug that needs least setup.

   Ground the expectation in what you already have open (API docs, Go doc, an existing test); if the sources
   disagree, ask the maintainers in the issue.
5. **The test** is the example (or, if the example is not a test, does what it does): same data, same requests,
   nothing more; next to the package's tests, in their style. It asserts the guarantee the bug breaks (a read
   includes the writes committed before it), not incidental details of how the fix provides it (which index, how
   many responses); setup checks that the scenario happened are fine. One test per distinct way the bug shows. It
   must fail at the base; keep the output.
6. **The fix**: in the layer where the defect is; the smallest change in the surrounding style; no refactoring, no
   comment that restates the code. Note in `meta.md`, "If a reviewer asks", the alternatives and costs you
   considered; do not research more for it.
7. **Verify**: the new tests (fail at the tests commit, pass at the fix commit), the package's tests, `gofmt -l`, `go vet`;
   nothing broader unless the change leaves the package. Record the commands and results in `meta.md`.
8. **Write** `issue.md` and `pr.md` (below), commit the tests, the fix and the changelog entry, and run
   `python3 -I .claude/skills/upstream-report/check.py <slug>`: fix every FAIL, decide every WARN.
9. **Hand off**: branch and commit, base, the files, the commit message to rewrite, anything not verified, and the
   push command the issue's links need: `git -C ~/etcd-fixes/<slug> push origin fix/<slug>`. State `draft` in
   `meta.md`.

## The issue

The bug-report form's sections, as in `example/issue.md`. Only the symptom, the expectation and the reproduction:
no root cause, code names, code links, history, or claims about other releases.

- **What happened?** One sentence of when it happens and what goes wrong, with the example's output when it shows
  the bug at a glance; one sentence on who else is affected, as one clause naming the whole condition ("for any
  client sending X with Y and Z").
- **What did you expect?** One or two sentences, in terms of the example.
- **How can we reproduce it?** Whatever it takes, at `main` (<sha>): the steps, or the test linked on the fork's
  branch (`https://github.com/upamanyus/etcd/blob/fix/<slug>/<path>#L<a>-L<b>`, the test's lines from its doc
  comment to its closing brace, and `.../tree/fix/<slug>`), not described, with its failing assertion.
- **Anything else?** Impact or workarounds if any; side findings as questions to the maintainers; then, word for
  word: "I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this
  report myself."
- **Version** and **configuration**: what the reproduction ran on (the base commit; `etcd --version` and `etcdctl
  version` if it ran binaries) and the configuration it needs.

Outputs are pasted from runs, never typed; trivial lines (setup `OK`s, trailing blank lines) may go, and test output
may be trimmed to the assertion.

## The PR

A few plain sentences, as in `example/pr.md`, no sections. `Title:` the commit subject. Then: the root cause, saying
what each piece of code does and which part is wrong, with permalinks at the base
(`https://github.com/etcd-io/etcd/blob/<sha>/<path>#L<a>-L<b>`); the change as "This PR ..."; `Fixes #<issue>`; one
line that the new tests (the first commit) run the issue's example and fail on `main`, and pass with the fix (the second); and, word for word: "This PR was written
in part with the assistance of AI; I have reviewed and tested every change." Nothing else: alternatives,
costs and backports stay in `meta.md`.

## Writing

The reader is an etcd maintainer with two minutes, who knows etcd and not this repository.

- Each sentence has one reading: name every condition in one clause; no "it", "one", "both" or "the same" whose
  referent must be guessed; a word with two meanings (the request's limit, mvcc's read limit) says which.
- Cut everything the reader does not need to believe or reproduce the bug: lists of flags or values become one
  phrase.
- Every reference resolves: branches and tests are linked, names are introduced.
- Only this bug and this change: no other features the code serves, no other bugs (those go to `issues/`).
- No vocabulary from this repository (spec, proof, premise, Goose, unit, ghost, verified code).
- Plain claims; say what was and was not reproduced.

## After filing

Set the finding's front matter to `upstream: reported` with the issue and PR in `links`, and `meta.md`'s state to
`filed` (`fixed` when merged; `etc/issues-status.py --refresh` updates states). After a PR is open, revise with new
commits, not force-pushes; rerun step 7 and `check.py`.

## Improving this skill

When the user critiques a candidate: fix the candidate, then change this file (or `check.py`) so the
next candidate gets it right; the critique wins over any rule here. Replace `example/` when the user approves a
better model.
