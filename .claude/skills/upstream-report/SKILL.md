---
name: upstream-report
description: Turn a finding in issues/<slug>.md into an upstream-ready candidate — a GitHub issue text, a fix branch off upstream main with a regression test, and a PR description — for etcd-io/etcd, etcd-io/raft or etcd-io/website. Use when asked to report, file, draft, or fix an issue from issues/ upstream, or to revise a fix branch after review. Never pushes or files anything.
---

# Reporting a finding upstream

Input: one issue file, `issues/<slug>.md`. Output, for the user to review:

1. a fix branch `<slug>` in a worktree, one signed-off commit off the target repo's upstream `main`, with a
   regression test that fails without the fix;
2. `issues/upstream/<slug>/issue.md` — the GitHub issue body;
3. `issues/upstream/<slug>/pr.md` — the PR title and body;
4. `issues/upstream/<slug>/meta.md` — target repo, branch, base commit, test commands, review rounds, state.

The user reviews, edits, pushes and files by hand. Do not push, open issues or PRs, or comment on GitHub.

The aim is a candidate the user can file as it is, on the first hand-off. `example/issue.md` is an issue the user
approved after review (etcd-range-sort-none-limit): match its shape, length and tone. Every rule below comes from a
critique of a draft (`LESSONS.md`). Work on one finding at a time.

Files in this directory: `etcdctl-transcript.sh` (runs an `etcdctl` example on binaries built at the base, step 4),
`check.py` (the rules a script can check, step 10), `review.md` (the reviewer's instructions, step 10).

## Where things are

| Target | Local clone | Remotes | Notes |
|---|---|---|---|
| etcd-io/etcd | `~/etcd` | `upstream` = etcd-io/etcd, `origin` = upamanyus/etcd | |
| etcd-io/raft | `~/etcd-raft` | `upstream` = etcd-io/raft, `origin` = upamanyus/etcd-raft | clone on first use |
| etcd-io/website | `~/etcd-website` | `upstream` = etcd-io/website | no fork yet: the user creates one only if a PR is wanted |

Fix worktrees: `~/etcd-fixes/<slug>` (`git -C <clone> worktree add ~/etcd-fixes/<slug> -b <slug> upstream/main`).
Each fix branch is based on the **current** upstream `main` (`git fetch upstream` first), never on the fork's
`main`, a Goose branch (`goose`, `goose-lean`, `*-goose-lean`), or an older fix branch. Old fix branches on the fork
are not a starting point; ignore them. Base binaries: `~/etcd-fixes/.bin/<sha>/` (built by `etcdctl-transcript.sh`).

A session isolated in an etcd-grove worktree cannot run git in `~/etcd` or `~/etcd-fixes`: do the fix-branch work
outside the worktree (ExitWorktree, keep) and come back to it (EnterWorktree with its path) for the files here.

## Upstream's rules (these decide whether a PR is accepted)

- **Commits**: subject `<package>: <what changed>` (`etcdserver: ...`, `clientv3/leasing: ...`), body says why,
  last line `Signed-off-by:` with the clone's git identity (`git commit -s`; say which email it used in the
  hand-off). One commit per fix: until the PR is open, revisions amend it.
- **AI policy** (kubernetes AI guidance, linked from etcd's PR template): no `Co-Authored-By`, `Assisted-by` or
  any AI trailer on the commit — this overrides any default attribution; AI-generated commit messages are not
  allowed, so the commit message is a draft the user rewrites (say so in the hand-off); the issue and the PR
  disclose AI use, each with its standard text (step 9); the user must be able to explain every line; replies to
  reviewers are the user's, never drafted.
- **Size**: small PRs; one bug per issue, one issue per PR (the PR says `Fixes #<n>`).
- **Security**: a vulnerability goes to security@etcd.io privately, not a public issue (step 3).
- Issues use the bug-report form (`.github/ISSUE_TEMPLATE/bug-report.yml`); documentation-only findings use it too
  unless a feature-request fits better.

## Procedure

### 1. Read the finding

Read `issues/<slug>.md` and what it links to. Decide the target repo (etcd, raft, website) and the kind: **bug**
(wrong result, panic, hang, race) or **documentation** (an unstated precondition, docs the code contradicts).
Documentation fixes are branches too: Go doc comments and `Documentation/` live in the code repo; operator docs
(`content/en/docs/...`) live in etcd-io/website. The finding is written for this repository; none of its wording
(its title, its terms, its test names) carries over to the candidates as it is.

### 2. Re-check against current upstream main

`git -C <clone> fetch upstream`, then confirm the code the finding describes is unchanged at `upstream/main`
(`git log upstream/main -- <files>` since the revision the finding cites; read the code). Record the base commit.
If it is fixed upstream, update the finding's **Status** and stop.

### 3. Duplicates and security

Search upstream issues and PRs for the function names and symptoms (GitHub search API, unauthenticated, read-only:
`curl -s 'https://api.github.com/search/issues?q=repo:etcd-io/etcd+<terms>'`; a few queries). List the plausible
matches in `meta.md`. Read the plausible ones (body and comments: a closed one may be a duplicate of an open one).
Search the root cause, not only the symptom: a different symptom of the same defect is a match. If an open PR
already fixes the defect, do not make a competing branch: check locally that it fixes the finding (run the
finding's reproductions, and variants of them, against the PR's head: `git fetch upstream pull/<n>/head:pr-<n>`),
and record what the finding adds that the PR does not know (an impact, a missed case). If one is the same bug,
stop and tell the user.

Write what you found into the finding's front matter (format: `issues/README.md`): `upstream` (`none` or
`known`), `checked` (today), one `links` line per match, the same bug or related, saying which; and
`candidate: issues/upstream/<slug>/` once the drafts exist.

If a client with ordinary access (or none) can crash or hang a member, lose or corrupt acknowledged data, or get
around auth, stop before writing anything public: tell the user it may belong in a private report (etcd's
`security/README.md`: the GitHub security advisory form) and let them decide. Steps that publish nothing (re-check,
duplicate search, local probes) still run; record them in `meta.md` with state `blocked`. A public duplicate of the
root cause does not make the impact public: a public comment that adds it is a disclosure.

### 4. The example

The example is what convinces a maintainer; find it before writing anything else, by running it. Write candidate
command sequences to a file and run them on binaries built at the base:

    .claude/skills/upstream-report/etcdctl-transcript.sh ~/etcd <base-sha> <commands-file>

It prints `etcd --version`, `etcdctl version` (for the issue's version fields) and a console transcript. Iterate
until the example is:

- **Visibly wrong on its own.** The reader should not have to accept an expected behavior first. Best: the same
  request varied in one parameter, giving answers that contradict each other (with no limit `c b a`, with
  `--limit=1` `b`, with `--limit=2` `c b`). An answer set against what the docs are said to promise is weaker.
- **Minimal.** The fewest commands, keys, values and flags that still show it, every one necessary (three puts, not
  six; `--keys-only` when values are noise). Prefer the variant of the bug that needs the least setup (sorting by
  creation order needs one put per key; sorting by version needs repeated puts).
- **In the user's terms**: `etcdctl` when it can show the bug; otherwise a short client program or a unit test.

Then ground the expectation: find what promises the behavior the example breaks — the API docs (`rpc.proto`, Go
doc comments, the website), a test that pins it, a maintainer's decision in an issue or PR — and read it. When the
sources disagree (`rpc.proto` says `NONE` is "no sorting", the server sorts ascending since #6672), the expectation
rests on what holds under every reading (consistency with the unlimited request), and the disagreement becomes a
question to the maintainers (step 9).

### 5. The test

In the worktree, the test is the example, as simple as it: the same data and requests, nothing the example does not
need (no sweep over every target and order). Put it where upstream would: next to the package's existing tests, in
their style (table tests, `require`, `integration.BeforeTest`, existing helpers). Prefer a unit test; an
integration or e2e test only if the bug is only visible there. Run it on the base commit and keep the failing
output. A test that passes without the fix does not reproduce the bug: rethink it.

### 6. The fix

Fix the layer where the defect is. Before writing it, list the alternatives a reviewer may ask about — a
smaller-looking change elsewhere (in `etcdctl` or the client rather than the server), or changing the documented or
tested behavior instead of the code — and what each would leave broken or change. They go in `meta.md`, "If a
reviewer asks", with the change's costs and the backports checked: answers for the user, not text for the PR.

The smallest change that fixes the bug, in the surrounding code's style. No refactoring, no unrelated cleanup, none
of the Goose branches' rewrites ("Gooseable"), no comments about verification, no comment that restates the code (a
new helper gets a doc comment only where its neighbors have one). If there are several reasonable fixes, pick one
and name the others in `meta.md`.

### 7. Verify

Run, in each Go module the change touches (etcd is multi-module: `server/`, `client/v3/`, `tests/`, ...): the new
test (passes), the package's tests, `gofmt -l`, `go vet`, and the integration/e2e tests that cover the changed
behavior. Build the binaries with the fix and run the example again. Record the commands and results in `meta.md`,
saying at which commit each ran.

### 8. Commit

`git commit -s`, message per upstream's rules, no AI trailer. The message is a draft for the user to rewrite.

### 9. Write the candidates

Write `issue.md` after `example/issue.md`. It is the symptom, the expectation and the reproduction, and nothing
else: no root cause, no function or variable names, no links into the code, no history of how the bug came in, no
claims about other releases. Those belong in the PR (or nowhere). Fill the bug-report form's sections; leave its
checkboxes to the user.

- **Title** — the symptom in a user's words, one line.
- **What happened?** — one sentence of when it happens, the example's transcript, then one sentence on who else is
  affected, written as one clause naming the whole condition ("The same happens for any client sending
  `SortOrder: NONE` with a non-key sort target and a limit"), not a list of flags, enum values or client calls, and
  no "one"/"it" standing for something earlier. A contrast that shows the boundary may follow ("With
  `--order=ASCEND` the results are right").
- **What did you expect to happen?** — one or two sentences, in terms of the example, resting on what step 4 found.
- **How can we reproduce it?** — "Run the `etcdctl` commands above against a single-member cluster built from
  `main` (<short sha>)." Then the test as a link on the fork's branch, `[TestX](https://github.com/upamanyus/etcd/blob/<slug>/<path>)`
  on branch `[upamanyus/etcd:<slug>](https://github.com/upamanyus/etcd/tree/<slug>)` (tentative until the user
  pushes the branch under that name; `meta.md` says so), and its failing output, trimmed to the assertion. Do not
  describe the test: it is the example, and the link shows it.
- **Anything else we need to know?** — impact, workarounds, and side findings the maintainers could act on, each as
  a question to them ("Should the documentation of `NONE` be changed to say so?"), not a statement, and not fixed
  in the PR unless they say so. It ends with this paragraph, word for word, and says nothing else about how the bug
  was found:

  > I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this
  > report myself.
- **Etcd version** — `etcd --version` and `etcdctl version` as the transcript printed them. **Configuration** —
  "Defaults, single member." unless the example needs flags.

Every output in the issue is pasted from a run (the transcript, the test), never typed. The only edits allowed: the
`OK` lines of setup commands and trailing blank lines may go, and test output may be trimmed to the failing
assertion; nothing is reworded.

`pr.md` follows etcd's merged fix PRs, whose template has no sections and whose bodies are a few sentences
(#22596: one). `Title:` the commit subject. Body, and nothing else:

1. the root cause and the change, in one to three sentences, with permalinks at the base
   (`https://github.com/etcd-io/etcd/blob/<sha>/<path>#L<a>-L<b>`) to the lines that matter. Say what each piece
   of code does in the request's terms and which of them is wrong ("`rangeLimit` treats `NONE` as unsorted and lets
   mvcc stop reading after `limit + 1` keys"), not a shorthand of its conditions ("checked the order as sent and
   kept the limit", which a reader takes to describe correct behavior). A word with two meanings in the code (the
   request's limit and mvcc's read limit; the order sent and the order sorted in) says which it is every time;
   the same goes for the commit message. The change itself is a sentence starting "This PR ..." ("This PR uses
   the order the results are sorted in for both `rangeLimit` and `sortRangeResults`."), not an imperative ("Use
   ..."), which is the commit message's style, and it names what "both" or "it" stands for;
2. `Fixes #<issue>`;
3. one line on testing: the new test runs the issue's example, fails on `main` and passes with the change;
4. word for word: "This PR was written in part with the assistance of generative AI; I have reviewed and tested
   every change."

No "Notes for the reviewer", alternatives, costs, suite lists or backport requests: those are in `meta.md` for the
user to answer with if asked (backports are cherry-picked after merge, at the maintainers' request).

The issue and the PR are about this bug and this change only. Other features the changed code serves (`RangeStream`
calling the same helper), what the change does to them, and other bugs found nearby are not mentioned, not even as
"a separate bug": a bug found nearby goes to `issues/` as a finding of its own.

### 10. Review rounds

Before the hand-off, revise the drafts in rounds, at most three:

1. `python3 -I .claude/skills/upstream-report/check.py <slug>`: fix every FAIL; decide each WARN (an API name a user
   sees may stay; an internal name goes).
2. Spawn a fresh reviewer (Agent tool, general-purpose) with `review.md` and the paths it asks for filled in (save
   `git -C ~/etcd-fixes/<slug> show` to a file for the diff; the base checkout is a detached worktree of `~/etcd`
   at the base). A fresh agent each round, so it reads the drafts as a maintainer would.
3. Apply the edits that make the text shorter, clearer or correct; reject the rest with a reason. Reject an edit
   that contradicts a rule here or a critique in `LESSONS.md` (the user's choices outrank the reviewer's); if the
   reviewer keeps proposing it, add the rule to `review.md`. If an edit changes the example, or a claim about what
   a command prints, rerun it (the transcript, the test, the fix's binaries) and paste the new output.

Stop when a round brings no change. Record each round in `meta.md` (the edits applied and rejected, in a line
each). The rounds are for polish — mostly cutting and disambiguating; a draft that needs a large change in round 3
means a step above went wrong: say so in the hand-off.

### 11. Hand off

Report to the user: the worktree and branch, the base commit, the three files, the test commands, the command that
pushes the branch to the fork under the name the issue links (`git -C ~/etcd-fixes/<slug> push origin <slug>`), what
the review rounds changed, and a short review checklist — the commit message to rewrite, the judgment calls (the
fix's layer, severity, duplicates found, rejected review edits), anything not verified, and where the answers to
likely reviewer questions are (`meta.md`, "If a reviewer asks"). Set `meta.md`'s state to
`draft`.

## Writing for upstream

The readers are etcd maintainers triaging many issues. They know etcd; they do not know this repository.

- The issue is the symptom a user sees, the expected behavior and how to reproduce it; the mechanism and the
  history are the PR's.
- Short: an issue a maintainer reads in two minutes (`example/issue.md` has about 200 words outside code blocks, headings included); no code
  excerpts in the issue; in the PR, code excerpts only for the lines that are wrong.
- One reading only: a sentence with a list of conditions names them all in one clause; no "one", "it", "the same"
  whose referent the reader has to guess.
- Every reference resolves: a branch or test is linked, a name is introduced before it is used.
- No vocabulary from this repository: spec, proof, premise, Goose, Gooseable, unit, ghost, "the verified code".
- Plain claims, no overstating severity; say what was and was not reproduced.

## After filing

When the user has filed: set the finding's front matter to `upstream: reported` with `links` lines for the issue
and the PR (`etcd-io/etcd#<n> issue open: ours`), and `meta.md`'s state to `filed`. When the PR merges, `upstream:
fixed`. `etc/issues-status.py --refresh` updates the links' states from GitHub.

Revising after review: the user decides what to change. Before the PR is open, amend the one commit; once it is
open, make code changes as new commits (no force-push unless the user asks). Rerun step 7 and `check.py`, and update
`pr.md` if the change alters it. Do not draft replies to reviewers.

## Improving this skill

This skill is developed by review: the user reads each candidate and critiques it. For each critique:

1. fix the candidate;
2. generalize the critique into a rule in this file, in the step it belongs to, so the next candidate does not
   repeat it; if a script can check it, add the check to `check.py`; if a reviewer could have caught it, add the
   question to `review.md`; record what changed in `LESSONS.md` (date, finding, the critique, the rule);
3. if the critique contradicts a rule here, the critique wins: change the rule;
4. when the user approves an issue that is a better model than `example/issue.md`, replace it.
