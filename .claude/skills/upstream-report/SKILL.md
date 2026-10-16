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
4. `issues/upstream/<slug>/meta.md` — target repo, branch, base commit, test commands, state.

The user reviews, edits, pushes and files by hand. Do not push, open issues or PRs, or comment on GitHub.

Work on one finding at a time. A candidate is a draft until the user approves it; expect review and
apply it as described in "Improving this skill".

## Where things are

| Target | Local clone | Remotes | Notes |
|---|---|---|---|
| etcd-io/etcd | `~/etcd` | `upstream` = etcd-io/etcd, `origin` = upamanyus/etcd | |
| etcd-io/raft | `~/etcd-raft` | `upstream` = etcd-io/raft, `origin` = upamanyus/etcd-raft | clone on first use |
| etcd-io/website | `~/etcd-website` | `upstream` = etcd-io/website | no fork yet: the user creates one only if a PR is wanted |

Fix worktrees: `~/etcd-fixes/<slug>` (`git -C <clone> worktree add ~/etcd-fixes/<slug> -b <slug> upstream/main`).
Each fix branch is based on the **current** upstream `main` (`git fetch upstream` first), never on the fork's
`main`, a Goose branch (`goose`, `goose-lean`, `*-goose-lean`), or an older fix branch. Old fix branches on the fork
are not a starting point; ignore them.

## Upstream's rules (these decide whether a PR is accepted)

- **Commits**: subject `<package>: <what changed>` (`etcdserver: ...`, `clientv3/leasing: ...`), body says why,
  last line `Signed-off-by:` with the clone's git identity (`git commit -s`; say which email it used in the
  hand-off). One commit per fix.
- **AI policy** (kubernetes AI guidance, linked from etcd's PR template): no `Co-Authored-By`, `Assisted-by` or
  any AI trailer on the commit — this overrides any default attribution; AI-generated commit messages are not
  allowed, so the commit message is a draft the user rewrites (say so in the hand-off); the PR description must
  disclose AI use; the user must be able to explain every line; replies to reviewers are the user's, never drafted.
- **Size**: small PRs; one bug per issue, one issue per PR (the PR says `Fixes #<n>`).
- **Security**: a vulnerability goes to security@etcd.io privately, not a public issue (step 3).
- Issues use the bug-report form (`.github/ISSUE_TEMPLATE/bug-report.yml`); documentation-only findings use it too
  unless a feature-request fits better.

## Procedure

### 1. Read the finding

Read `issues/<slug>.md` and what it links to. Decide the target repo (etcd, raft, website) and the kind: **bug**
(wrong result, panic, hang, race) or **documentation** (an unstated precondition, docs the code contradicts).
Documentation fixes are branches too: Go doc comments and `Documentation/` live in the code repo; operator docs
(`content/en/docs/...`) live in etcd-io/website.

### 2. Re-check against current upstream main

`git -C <clone> fetch upstream`, then confirm the code the finding describes is unchanged at `upstream/main`
(`git log upstream/main -- <files>` since the revision the finding cites; read the code). Record the base commit.
If it is fixed upstream, update the finding's **Status** and stop. Every line reference in the PR is a permalink at
the base commit (the issue has none, step 8): `https://github.com/etcd-io/etcd/blob/<sha>/<path>#L<a>-L<b>`.

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

### 4. Reproduction test first

In the worktree, write the smallest test that shows the bug, where upstream would put it: next to the package's
existing tests, in their style (table tests, `require`, `integration.BeforeTest`, existing helpers). Prefer a unit
test; add an integration or e2e test only if the bug is only visible there. Run it on the base commit and keep the
failing output — it goes into the issue. A test that passes without the fix does not reproduce the bug: rethink it.
When the expected behavior rests on a reading of the API that someone could dispute, test a property that needs no
reading instead: one request against a variant of it (with a limit against without, at one revision against
another), as the issue's example does (step 8). The test is the issue's example, as simple as it: the same data and
requests, no sweep over targets or orders the example does not need. Write the example (step 8) first, then the test.

### 5. The fix

The smallest change that fixes the bug, in the surrounding code's style. No refactoring, no unrelated cleanup, none
of the Goose branches' rewrites ("Gooseable"), no comments about verification, and no comment that restates the
code (a new helper gets one only where its neighbors have one). If there are several reasonable fixes, pick one and
name the others in the PR's notes for the reviewer.

Fix the layer where the defect is, and say why in the PR: a reviewer will ask why not a smaller-looking change
elsewhere (in `etcdctl` or the client rather than the server, or by changing the documented or tested behavior
instead of the code). Name each such alternative in the PR's notes with what it would leave broken or change.

### 6. Verify

Run, in each Go module the change touches (etcd is multi-module: `server/`, `client/v3/`, `tests/`, ...): the new
test (passes), the package's tests, `gofmt -l`, `go vet`, and the integration/e2e tests that cover the changed
behavior. Record the commands and results in `meta.md`.

### 7. Commit

`git commit -s`, message per upstream's rules, no AI trailer. The message is a draft for the user to rewrite.

### 8. Write the candidates

`issue.md`, in the bug-report form's sections (the form's checkboxes are the user's to tick). Every command output in
it is pasted from a run at the base commit, never typed from memory: build the binaries there (in a detached
worktree of the base, `go build -ldflags "-X go.etcd.io/etcd/api/v3/version.GitSHA=<short sha>"` in `server/` and
`etcdctl/`), run the `etcdctl` reproduction against them, and paste their `etcd --version` and `etcdctl version`
into the version fields. Test output may be trimmed to the failing lines (no log noise), but not reworded.

- **What happened?** — the user-visible behavior first, in etcd's terms (an `etcdctl` command, a client call, a
  server config), and nothing about the cause: no function or variable names, no code permalinks, no history of
  how the bug came in. The root cause goes in the PR (and the commit message), not the issue. Choose the example
  whose output is visibly wrong on its own, without the reader having to accept an expected behavior first: the same request
  varied in one parameter, giving answers that contradict each other (`--limit=1` returns `b` but `--limit=2` and
  no limit start with `c`), beats one answer set against what the docs are said to promise. Then minimize it:
  the fewest commands and keys that still show the bug, every one necessary (three puts, not six, for a bug that
  needs three keys), and data on which the targets the text names all reproduce. Say what
  else is affected in one plain sentence ("the other non-key sort targets", "any client that sends ..."), not as a
  list of flags, enum values or client calls.
- **What did you expect to happen?** — grounded in a source the reader can check: the API's documentation
  (`rpc.proto`, Go doc, the website), a test that pins the behavior, a maintainer's decision in an issue or PR, or
  consistency with a variant of the same request. Before relying on a documented behavior, read the documentation:
  when sources disagree (`rpc.proto` says `NONE` is "no sorting", the server sorts ascending), say so, and ground
  the expectation in what holds under every reading.
- **How can we reproduce it?** — the minimal steps (`etcdctl` sequence when one exists), then a link to the test on
  the fork's branch (`[TestX](https://github.com/upamanyus/etcd/blob/<slug>/<path>)` and
  `[upamanyus/etcd:<slug>](https://github.com/upamanyus/etcd/tree/<slug>)`; tentative until the user pushes the
  branch under that name, which `meta.md` says) and its failing output. Do not describe the test: it is the example
  above, and the link shows it. Never "the linked branch" without the link.
- **Anything else we need to know?** — impact and who is affected, and workarounds; no claims about other releases (the
  version fields say what was run; backports are the maintainers' call, and the PR's notes may name them). A side finding the maintainers
  could act on (documentation that contradicts the behavior) goes here as a question to them ("Should the
  documentation of `NONE` be changed to say so?"), not as a statement, and not fixed in the PR unless they say so. One sentence may say it was found while formally verifying etcd; no more.

`pr.md`: title = the commit subject; body: what the change does and why (two or three sentences), `Fixes #<issue>`
(placeholder), how it was tested, notes for the reviewer (alternatives considered, behavior changes), and the AI
disclosure: "This PR was written in part with the assistance of generative AI; I have reviewed and tested every
change."

### 9. Hand off

Report to the user: the worktree and branch, the base commit, the three files, the test commands, the command that
pushes the branch to the fork under the name the issue links (`git -C ~/etcd-fixes/<slug> push origin <slug>`), and a short
review checklist — the commit message to rewrite, any judgment calls (severity, the fix chosen, duplicates found),
anything not verified. Set `meta.md`'s state to `draft`.

## Writing for upstream

The readers are etcd maintainers triaging many issues. They know etcd; they do not know this repository.

- The issue is the symptom a user sees, the expected behavior and how to reproduce it; the mechanism and the
  history are the PR's.
- No vocabulary from this repository: spec, proof, premise, Goose, Gooseable, unit, ghost, "the verified code".
- Short: an issue body a maintainer reads in two minutes, with no code excerpts; in the PR, code excerpts only for
  the lines that are wrong.
- Plain claims, no overstating severity; say what was and was not reproduced.

## After filing

When the user has filed: set the finding's front matter to `upstream: reported` with `links` lines for the issue
and the PR (`etcd-io/etcd#<n> issue open: ours`), and `meta.md`'s state to `filed`. When the PR merges, `upstream:
fixed`. `etc/issues-status.py --refresh` updates the links' states from GitHub.

Revising after review: the user decides what to change. Make code changes as new commits on the branch (no
force-push once a PR is open, unless the user asks), rerun step 6, and update `pr.md` if the change alters it. Do
not draft replies to reviewers.

## Improving this skill

This skill is developed by review: the user reads each candidate and critiques it. For each critique:

1. fix the candidate;
2. generalize the critique into a rule in this file, in the section it belongs to (procedure, upstream's rules,
   writing), so the next candidate does not repeat it; record what changed in `LESSONS.md` (date, finding, the
   critique, the rule);
3. if the critique contradicts a rule here, the critique wins: change the rule.
