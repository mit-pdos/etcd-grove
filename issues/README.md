# Issues

`issues/` holds the bugs found while verifying etcd, raft, bbolt and the code around them that
etcd's developers would want fixed: each has a **Go test that fails** at a recorded upstream
commit, reaching the bug the way etcd (or a documented user of a public package) uses the code.
One file per bug, `issues/<project>-<short-slug>.md`; the test in `issues/<slug>/`.

Everything else found goes to [`../nonissues/`](../nonissues/README.md), in the same format minus
the report: findings with no test (code reading), unstated preconditions etcd meets, documentation
findings, behavior etcd does not guarantee, tests that fail only by using an internal API in a way
no etcd caller does. Move a file to `issues/` when someone writes a valid failing test for it, and
to `nonissues/` when its test is shown not to be valid. Bugs in this repository's own specs and
proofs go in `notes/`; bugs only in an unmerged pull request's code go with that work
(`notes/pr-verify/<repo>-<n>.md`).

`INDEX.md` (here and in `nonissues/`) is generated from the files: `etc/issues-status.py --index`
rewrites both, `--check` fails if they or a file's front matter are out of date. Do not edit it.

## Front matter

```
---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#22614 issue open: this bug
  - etcd-io/etcd#22619 pr merged: the fix
blocks-proof: no
---
```

- `upstream`: where the bug stands upstream. `none` (searched: nothing upstream, not reported),
  `reported` (we filed it), `known` (someone else's issue or PR covers it), `fixed` (fixed upstream;
  the PR or commit in `links`).
- `checked`: when upstream was last searched, or the links refreshed (`etc/issues-status.py
  --refresh` reads the linked issues' and PRs' states from GitHub).
- `links`: one line per related upstream issue, PR or commit: `<repo>#<n> <issue|pr> <state>: <how it
  relates>` (state `open`, `closed`, `merged`), or `<repo>@<sha>: ...`. Related but different ones
  too, saying so.
- `blocks-proof`: `yes` when the theorem this repository proves for the code, or would state for it
  (the package's intended spec), is false at the code as etcd uses it: the proof needed a fix in
  the verified fork, or a premise etcd does not meet. `no` otherwise: the proof goes through with
  no premise, or with one etcd meets; liveness, performance and metrics are outside the safety
  theorems. The `## Proof` section says which.

## An issue: the report

The file is the bug report we would file, in the shape etcd's maintainers act on (what the
2026-10 survey of etcd, raft and bbolt issues found; the `upstream-report` skill turns it into the
filed text, keeping its content):

````markdown
# <component>: <API or condition> <bad outcome>

<What happens, one to three sentences: the bad outcome first, in user terms, with the
configuration and the operations that trigger it. No code names a user would not know.>

**Expected:** <one sentence, "X should Y">, as <the Go doc, documentation or guarantee, linked>.

**Impact:** <who hits it and how a real deployment reaches it: default configuration or not,
cluster size, which client operations; the releases affected. Plain, not overstated.>

**Reproduction:** `TestX` in [`issues/<slug>/x_test.go`](<slug>/x_test.go), copied into
`<module>/<package dir>` at etcd-io/<repo>@<sha> (<date>), <go version>:

```
$ go test ./<package dir> -run TestX
<the failing output of a run, trimmed to the assertion>
```

**Cause:** <two to four sentences: what the code does and which assumption fails, with
permalinks at the same sha>.

## Proof

<yes|no>: <one line: the fork fix or the premise the proof needed, with its file; or why the
proof is unaffected>.

## Fix

**Branch**: `fix/<slug>` in `~/etcd-fixes/<slug>` (upamanyus/<fork>, pushed|not pushed): <short
sha> test, <short sha> fix
**Base**: etcd-io/<repo>@<full sha>

**PR draft**:

Title: <the fix commit's subject>

<the PR text, a few plain sentences: the root cause with permalinks, "This PR ...",
"Fixes #<issue>" once filed>

**If a reviewer asks**: <optional, short: the alternatives considered and why not>.

## Notes

<optional, short: what someone deciding about this issue needs and the sections above do not say>.
````

- **Title**: the component, the condition and the bad outcome, in a user's terms ("MemberUpdate
  forgets that the member is a learner"). One bug per file: a second root cause, trigger or
  workaround is a second file.
- **The test** is valid when:
  1. it fails at the base commit, with the output pasted from a run (current upstream `main`, or
     the release branch the bug is on; a bug fixed upstream keeps the commit before the fix);
  2. it reaches the bug as etcd does: through the call sequence of an etcd caller, or a public API
     used as documented, in the package's own harness (etcd: an integration test through the
     client for a server bug, which etcd's maintainers trust over a unit test on internals; raft:
     `raft_test.go`/`rawnode_test.go` through `network`; bbolt: a test or a `main` program). A test
     calling an internal function in a way no etcd caller does shows an unstated precondition,
     which is a non-issue;
  3. it asserts the guarantee that breaks, not incidental details (which index, how many
     responses).

  `issues/<slug>/` holds the test files (each a whole `_test.go` file for the package directory
  named on the Reproduction line), or a patch adding the test when it needs code the upstream
  commit does not have (`k8s-daemonset-ambiguous-create-duplicate-pod`: an unmerged framework), and,
  when no fix branch holds it, `fix.patch`.
- **`## Fix`** is optional. With a fix branch, its first lines are exactly `**Branch**:` and
  `**Base**:` as above (the `upstream-report` skill's `check.py` reads them), and `**PR draft**:`
  holds the PR text until the PR is open. Without one, a sentence saying what would change.
- **Filed issues** (`reported`, `known`, `fixed`): the write-up is on GitHub. The file keeps the
  title, the first paragraph, the Reproduction line and `## Proof`.
- **Not in the report**: this repository's vocabulary (spec, proof, premise, Goose, unit, ghost);
  placeholders or template lines left unfilled.

`.claude/skills/upstream-report/` is how an issue is filed: the fix branch, the issue and PR texts
for each repository's norms, and the check before filing.

## A non-issue

````markdown
---
<front matter as above>
---
# <title: the behavior, as for an issue>

<What happens, one to three sentences.>

**Why not an issue:** <one line: no test, found by code reading; a precondition etcd meets (its
caller); documentation only; not a guarantee etcd makes; a test helper; ...>.

## Proof

<yes|no>: <one line>.

## Notes

<optional, short>.
````

A non-issue's tests, if any, are in `nonissues/<slug>/`.

## Reporting privately

etcd's threat model trusts its clients (2026-10-21): a crash a client can cause with a request it
is allowed to send is a robustness bug, not a security issue, and does not go to
security@etcd.io on that ground alone. A bug that crosses a permission line (with auth enabled, a
user allowed to write one key crashes every member: `etcd-txn-delete-then-ignore-put`) is the
user's decision; that one went through the private process (2026-10-21).
