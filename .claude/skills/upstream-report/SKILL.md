---
name: upstream-report
description: Turn a finding in issues/<slug>.md into an upstream-ready candidate — a GitHub issue text, a fix branch off upstream main with a regression test, and a PR description — for etcd-io/etcd, etcd-io/raft, etcd-io/bbolt or etcd-io/website. Use when asked to report, file, draft, or fix an issue from issues/ upstream, or to revise a fix branch after review. Never pushes or files anything.
---

# Reporting a finding upstream

From one finding, `issues/<slug>.md`, produce for the user to review:

- a fix branch `fix/<slug>` in `~/etcd-fixes/<slug>`: signed-off commits off current upstream `main`, first the
  tests (which fail at that commit), then the fix, then (in raft, for a change not to be backported) the changelog
  entry;
- `issues/upstream/<slug>/issue.md`, `pr.md` and `meta.md` (base commit, commands run and results, duplicates
  found, answers to likely reviewer questions, state).

Never push, file, or comment on GitHub unless the user asks; a branch already pushed is replaced only by a
force-push the user approved. Aim for a candidate the user can file as it is. `example/` holds approved candidates:
`issue.md`/`pr.md` (an `etcdctl` example) and `raft-issue.md`/`raft-pr.md` (a test example, the shape after the
2026-10-18 review): match their shape, length and tone. `raft-issue.md` predates the 2026-10-23 review: a raft
issue now has its content without its sections, and explains the cause too ("The issue").

| Target | Clone | Remotes |
|---|---|---|
| etcd-io/etcd | `~/etcd` | `upstream` etcd-io/etcd, `origin` upamanyus/etcd |
| etcd-io/raft | `~/etcd-raft` (clone on first use) | `upstream` etcd-io/raft, `origin` upamanyus/etcd-raft |
| etcd-io/bbolt | `~/etcd-bbolt` | `upstream` etcd-io/bbolt, `origin` upamanyus/bbolt |
| etcd-io/website | `~/etcd-website` | `upstream` etcd-io/website (no fork) |

`git -C <clone> fetch upstream && git -C <clone> worktree add ~/etcd-fixes/<slug> -b fix/<slug> upstream/main`. Never
base a fix on the fork's branches (Goose branches, old fix branches). From a session isolated in an etcd-grove
worktree, git in `~/etcd*` is refused: leave the worktree (keep) for that work and re-enter it by path.

## Upstream's rules

- Commits, so that the tests can be seen to fail before the fix: first the tests only (`*_test.go`, subject
  `<package>: test <what>`), then the fix (subject `<package>: <what changed>`, the PR's title). In raft, a bug fix
  the maintainers will backport to stable releases gets no changelog entry (the etcd-io/raft#536 review,
  2026-10-19): leave it out of bug fixes unless a reviewer asks. Once the backports merge, the maintainers ask for
  entries in the stable releases' changelogs (etcd-io/raft#534, 2026-10-23): one PR per repository to its `main`
  (raft's `CHANGELOG-3.<x>.md`, etcd's for its `raft/`), a new patch section linking each backport PR. Otherwise the changelog entry comes last, alone
  (`changelog: add entry for <what>`, no body, in `CHANGELOG/CHANGELOG-<next minor>.md` on `main`, the link
  `pull/TODO` until the PR exists): raft keeps its changelogs on `main`, mostly in commits of their own. In etcd, no
  changelog edit: its changelog is updated separately (few changelog commits touch code). Nor in bbolt, whose
  `CHANGELOG/` entries go in commits of their own, mostly by the maintainers after merging.
- Messages are as short as upstream's: most etcd and raft commits have no body, and nine in ten at most three lines.
  The tests commit has no body; the fix commit says in one short sentence what changes, or what was wrong, in words
  rather than function names, without restating the diff. Subjects at most 72 characters; the prefix the package's
  history uses (`client/v3:`, `etcdserver:`, `raft:`; bbolt's root package: `tx:`, `db:`). `git commit -s`, no AI trailer of any kind. The messages are
  drafts the user rewrites (Kubernetes' AI guidance, which etcd follows, forbids AI-written commit messages). Amend
  the commits until the PR is open.
- The issue and the PR each end with their AI disclosure (below; etcd's PR template asks for one, following
  Kubernetes' AI guidance: disclosure in the PR description, no AI trailers). Replies to reviewers are the user's.
- A bug a client with ordinary access can use to crash or hang a member, lose or corrupt acknowledged data, or
  bypass auth is a security report: before writing anything public, stop and let the user decide (etcd's
  `security/README.md`). A public duplicate of the root cause does not make the impact public.

## Procedure

1. **Read** the finding and what it links to. Its wording is for this repository; none of it carries over as is.
   Pick the target: code and Go doc comments are in etcd or raft, operator docs in etcd-io/website.
2. **Re-check** at current `upstream/main` that the code is unchanged; record the base commit. If fixed, update
   the finding and stop.
3. **Split** if the finding holds more than one bug: a distinct root cause, trigger or workaround is a separate
   issue and PR (its own slug and finding file, `issues/<slug>.md`), each branch off `main` and independent. Check
   how they combine: `git merge-tree --write-tree <a> <b>` for conflicts, and build the merge (a signature change
   in one breaks a call the other adds). Place the tests apart so that they merge cleanly. The issues do not
   mention each other; each PR ends with a note that it conflicts with the other, that the second to merge needs a
   rebase, and that you can combine both in one PR if they prefer.
4. **Duplicates**, in a background agent while you do steps 5-8: at most five searches
   (`curl -s 'https://api.github.com/search/issues?q=repo:etcd-io/etcd+<terms>'`; about ten a minute are allowed
   unauthenticated) for the symptom and the root cause; open only matches that look like the same bug. If an open
   PR fixes it, stop and tell the user. Record matches in `meta.md` and the finding's front matter
   (`issues/README.md`).
5. **The example**: the reproduction, in whatever form the bug needs (usually a Go test; `etcdctl` commands, a
   client program, a cluster configuration when that is what shows it). Build binaries only if it needs them. Run
   it at the base and make it:
   - visibly wrong on its own: the same request varied in one parameter, giving answers that contradict each other,
     or an answer that misses what an earlier acknowledged request did. Wrong under every linearization, not
     only under the implementation's: an operation that has observed nothing yet may take effect at any point of
     its interval, so a read transaction that reads once, after a later write, may rightly see it. Show the
     transaction observing the old state first (it reads `v1`, then `v3`: no single snapshot gives both; the
     2026-10-23 review of `bbolt-commit-meta-error-frees-reader-pages`);
   - minimal: the fewest steps, keys, values and options, choosing the variant of the bug that needs least setup;
   - legitimate: every component behaves as its documentation requires (raft's application applies a `Ready`'s
     committed conf changes before `Advance`, right after it learns they are committed; a client reads its
     channels), so the bug cannot be blamed on misuse, and no avoidable gap (commit before apply, an extra step)
     is needed to show it.

   Ground the expectation in what you already have open (API docs, Go doc, an existing test); if the sources
   disagree, ask the maintainers in the issue.
6. **The test** is the example (or, if the example is not a test, does what it does): same data, same requests,
   nothing more; next to the package's tests, in their style, through the package's usual harness (raft's
   `network.send`, etcd's integration cluster); messages delivered by hand only where the scenario needs an order
   the harness cannot give. No helper written for one test. It asserts the guarantee the bug breaks (a read
   includes the writes committed before it), not incidental details (which index, how many responses, whether a
   node is still leader); setup checks only that the scenario happened. Comments state what is required ("does not
   answer before the only voter confirms"), not a circumstance that suggests it would be fine otherwise. One test
   per distinct way the bug shows. It must fail at the base; keep the output.
7. **The fix**: in the layer where the defect is; the smallest change in the surrounding style; no refactoring.
   - Put a check where every path goes through it (a request postponed and later released does not come back
     through the function that postponed it).
   - Keep exported APIs: when a helper's name or doc comment promised more than it checks and a caller relied on
     it, do not change the helper's signature; add a small helper for what the caller needs, its doc in the
     package's terms, and check both at the caller (`IsVoter(r.id) && IsSingleton()`, as the etcd-io/raft#536 review
     asked instead of `IsSingleton(id)`).
   - Fix the root cause, not its symptoms at the callers: when a helper's result contradicts its name or doc comment
    (its informal spec), fix the helper so that it meets that spec, once, if every caller wants the corrected
    result, rather than working around it in each caller that is hit (etcd-io/etcd#22615 fixed
    `IsDefaultOrdering` itself, one change fixing two bugs, where our #22616 and the `rangestream` candidate
    patched two callers). Read every caller first; this differs from the `IsSingleton` case above, where the
    helper did what it said and a caller needed more. Before settling on a fix, list the candidate layers and
    fixes in `meta.md`, "If a reviewer asks", and say why the chosen one is the one a maintainer would pick.
  - A comment only when it says why (an ordering that matters), never what the code does.
   - A fix that changes only documentation (doc comments, `doc.go`, `README.md`) has no test that can fail before it
     and pass after: the branch is that one commit, and the reproduction test goes on a branch `repro/<slug>` off the
     same base (worktree `~/etcd-fixes/<slug>-repro`), which `meta.md` names in its line "**Reproduction branch**"
     (the branch and the worktree, each in backticks, as on the line "**Branch**") and the issue links instead of
     `fix/<slug>`; the PR leaves out the first-commit sentence, and the hand-off pushes both branches. `check.py`
     accepts this shape only when the fix changes no code or tests.
   - Try the simplest alternative first (reorder, one more condition); if it fails, run it and record why in
     `meta.md`, "If a reviewer asks", with the other alternatives and costs; do not research more for it.
8. **Verify**: check out the tests commit (the new tests fail) and the fix commit (they pass, the module's tests
   pass), `gofmt -l`, `go vet`. When running a test against the base by `go test -overlay`, overlay every file the
   fix changes. Record the commands and results in `meta.md`.
9. **Review** the branch as a maintainer would (the `code-review` skill, or by hand): correctness, every caller of
   anything changed, comments and docs that still claim the old behavior, alternatives a reviewer will raise.
   Check each finding against the code before acting: a scenario counts only if it is reachable under the
   documented protocol. Fix what belongs to this change; record other real bugs in `issues/` (with "found by code
   reading" or the reproduction), and record findings that turn out unreachable as `upstream: not-filing` with why.
10. **Write** `issue.md` and `pr.md` (below), commit, and run
    `python3 -I .claude/skills/upstream-report/check.py <slug>`: fix every FAIL, decide every WARN. In `meta.md`,
    answer the questions a reader will ask: why the fix works (what the base does at each step, what the fix
    changes), why the test shows the bug and not a misuse, how the candidate relates to its siblings.
11. **Hand off**: branch and commits, base, the files, the commit messages to rewrite, anything not verified, and
    the push command the issue's links need: `git -C ~/etcd-fixes/<slug> push origin fix/<slug>` (with
    `--force-with-lease=fix/<slug>:<sha>` over an earlier push, once the user approves). State `draft` in `meta.md`.

## The issue

For etcd, the bug-report form's sections, as in `example/`. Only the symptom, the expectation and the
reproduction: no root cause, code names, code links, history, other issues, or claims about other releases.

bbolt's and raft's issue forms are free-form (no template; raft has none, and etcd's structured sections read as
boilerplate there): no headings. Write the same content as plain paragraphs, in this order: the symptom with the
setup it needs (base commit, Go version and platform, options) in the first sentence, the steps, the expectation
in one sentence, (raft) the cause, the test link and its output, then any question, then the disclosure (the
2026-10-23 reviews). The sections below say what each part contains.

A raft issue explains the bug as well as the symptom (the 2026-10-23 review): after the expectation, one paragraph
saying what raft's code does at each step of the example and which assumption fails, naming the functions, with
permalinks at the base (`https://github.com/etcd-io/raft/blob/<sha>/<path>#L<a>-L<b>`, the full sha), so that a
maintainer sees from the issue alone why it happens. Say what is wrong, not how to fix it: the change and its
alternatives stay in the PR and `meta.md`.

- **Title**: the symptom and the condition, covering every case the issue shows.
- **What happened?** The configuration that matters ("With `ReadOnlySafe`:"), then, for more than two events,
  numbered steps, each saying when it happens relative to the others ("Before committing an entry in its new term,
  node 1 answers ..."); the example's output when it shows the bug at a glance; one sentence on who else is
  affected, as one clause naming the whole condition ("for any client sending X with Y and Z").
- **What did you expect?** One or two sentences, in terms of the example, saying what should happen ("X should
  Y"), not what does ("X does Y" reads as a description of the current behavior).
- **How can we reproduce it?** Whatever it takes, at `main` (<sha>): the steps, or the test linked on the fork's
  branch (`https://github.com/upamanyus/etcd/blob/fix/<slug>/<path>#L<a>-L<b>`, the test's lines from its doc
  comment to its closing brace, checked on GitHub after the push, and `.../tree/fix/<slug>`), not described, with
  its failing assertion.
- **Anything else?** Impact or workarounds if any; side findings as questions to the maintainers; then, word for
  word: "Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and
  reviewed the report."
- **Version** and **configuration**: what the reproduction ran on (the base commit; `etcd --version` and `etcdctl
  version` if it ran binaries; not that it ran none) and the configuration it needs.

Outputs are pasted from runs, never typed; trivial lines (setup `OK`s, trailing blank lines) may go, and test output
may be trimmed to the assertion.

## The PR

A few plain sentences, as in `example/`, no sections. `Title:` the fix commit's subject. Then: the root cause,
saying what each piece of code does and which assumption is wrong ("assuming, as its comment says, that ...; X does
not guarantee that"), with permalinks at the base (`https://github.com/etcd-io/etcd/blob/<sha>/<path>#L<a>-L<b>`);
the change as "This PR ...", with why code moves if it moves; `Fixes #<issue>`; "The first commit adds a test of
the issue's example, which fails on `main`; the second, the fix, makes it pass."; for split candidates, the
conflict note (step 3); and, word for word: "Written with the assistance of generative AI; I reviewed and tested
every change." Nothing else: alternatives, costs and backports stay in `meta.md`.

## Writing

The reader is an etcd maintainer with two minutes, who knows etcd and not this repository.

- Each sentence has one reading: name every condition in one clause; no "it", "one", "both" or "the same" whose
  referent must be guessed; a word with two meanings (the request's limit, mvcc's read limit) says which; a role
  that can change says which node holds it ("the only voter", not "the voter").
- Cut everything the reader does not need to believe or reproduce the bug: lists of flags or values become one
  phrase.
- Every reference resolves: branches and tests are linked, names are introduced.
- Only this bug and this change: no other features the code serves, no other bugs (those go to `issues/`).
- No vocabulary from this repository (spec, proof, premise, Goose, unit, ghost, verified code).
- Plain claims; say what was and was not reproduced.

## After filing

Set the finding's front matter to `upstream: reported` with the issue and PR in `links`, and `meta.md`'s state to
`filed` (`fixed` when merged; `etc/issues-status.py --refresh` updates states). Fill in the PR number in the raft
changelog commit and the sibling's conflict note. After a PR is open, revise with new commits, not force-pushes,
unless a reviewer asks for a rebase: then rebuild the branch on `upstream/main` (keep the old head as a local
`backup/<slug>-v1` branch), apply the review, and leave the force-push for the user to approve; update the
issue's links to the branch's lines, which move (a commit permalink does not). Rerun step 8 and `check.py`.

## Improving this skill

When the user critiques a candidate: fix the candidate, then change this file (or `check.py`) so the
next candidate gets it right; the critique wins over any rule here. Replace `example/` when the user approves a
better model.
