#!/usr/bin/env python3
"""Check an issue (issues/<slug>.md) before filing it, and print the texts to file.

Usage: check.py <slug> [--worktree DIR] [--base SHA] [--fork OWNER/REPO] [--print issue|pr]

The issue file is the report (issues/README.md): check.py renders from it the GitHub issue, in the
target repository's form (etcd's bug-report sections; plain paragraphs for raft and bbolt, raft's
with the cause), and the PR text (its `## Fix` section's `**PR draft**:`), each ending with the AI
disclosure. `--print` prints one of them, ready to paste. The worktree and base default to the `## Fix`
section's `**Branch**:` and `**Base**:` lines. Prints FAIL lines (a rule is broken: fix it) and WARN
lines (a judgment call: look at each and decide), and exits 1 if there is a FAIL. It does not judge
the writing; the user does.
"""

import argparse
import os
import re
import subprocess
import sys

ISSUE_DISCLOSURE = (
    "Found while formally verifying etcd. "
    "Written with the assistance of generative AI; I reproduced the bug and reviewed the report."
)
PR_DISCLOSURE = "Written with the assistance of generative AI; I reviewed and tested every change."
# Vocabulary of this repository that means nothing upstream.
LOCAL_WORDS = r"\b(specs?|proofs?|premises?|Goose|Gooseable|ghost|verified code|Lean|Rocq|Perennial|Iris)\b"
MAX_PROSE_WORDS = 250
MAX_RAFT_ISSUE_WORDS = 380  # a raft issue also explains the cause
MAX_PR_WORDS = 90

failures = 0


def fail(msg):
    global failures
    failures += 1
    print(f"FAIL {msg}")


def warn(msg):
    print(f"WARN {msg}")


def git(wt, *args):
    return subprocess.run(["git", "-C", wt, *args], check=True, capture_output=True, text=True).stdout


def prose(md):
    """The text outside code blocks and <details> sections."""
    md = re.sub(r"```.*?```", "", md, flags=re.S)
    md = re.sub(r"<details>.*?</details>", "", md, flags=re.S)
    return md


def show(wt, rev, path):
    r = subprocess.run(["git", "-C", wt, "show", f"{rev}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def go_code(src):
    """Go source without its comments, whitespace normalized: equal for two versions that differ only in comments."""
    tokens = re.findall(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\\n])*"|`[^`]*`|\'(?:\\.|[^\'\\\n])*\'|\S', src, flags=re.S)
    return " ".join(t for t in tokens if not t.startswith(("//", "/*")))


def norm(s):
    return " ".join(s.split())


class Issue:
    """The parts of issues/<slug>.md (issues/README.md, "An issue: the report")."""

    def __init__(self, path):
        text = open(path).read()
        if text.startswith("---\n"):
            text = text.split("\n---\n", 1)[1]
        self.text = text
        m = re.search(r"^# (.+)$", text, re.M)
        self.title = m.group(1).strip() if m else ""
        rest = text[m.end():] if m else text
        self.sections = {}
        for sm in re.finditer(r"^## (\w[\w ]*)\n(.*?)(?=^## |\Z)", rest, re.M | re.S):
            self.sections[sm.group(1).strip()] = sm.group(2).strip()
        report = re.split(r"^## ", rest, maxsplit=1, flags=re.M)[0]
        self.fields = {}
        parts = re.split(r"^\*\*(\w[\w ]*):\*\*\s*", report, flags=re.M)
        self.what = parts[0].strip()
        for name, value in zip(parts[1::2], parts[2::2]):
            value = value.strip()
            self.fields[name] = value[:1].upper() + value[1:]
        fix = self.sections.get("Fix", "")
        self.fix = {}
        for name in ("Branch", "Base", "Reproduction branch"):
            fm = re.search(r"^\*\*" + name + r"\*\*:\s*(.+)$", fix, re.M)
            if fm:
                self.fix[name] = fm.group(1)
        pm = re.search(r"^\*\*PR draft\*\*:\s*\n(.*?)(?=^\*\*|\Z)", fix, re.M | re.S)
        self.pr = pm.group(1).strip() if pm else None


def test_link(issue, fork, branch, slug, wt, base):
    """The Reproduction paragraph for upstream: the local test link becomes the test on the fork's branch,
    with its lines, or, without a branch, the test inlined."""
    repro = issue.fields.get("Reproduction", "")
    m = re.search(r"\[`?([^\]`]+)`?\]\(([^)]+_test\.go)\)", repro)
    if not m:
        return repro
    local, name = m.group(2), os.path.basename(m.group(2))
    tm = re.search(r"`(Test\w+)`", repro)
    if fork and wt:
        # the branch's test file: the one it changes that declares the test, else one of the same name
        changed = git(wt, "diff", "--name-only", f"{base}..HEAD").split() if base else []
        files = [f for f in changed if f.endswith("_test.go") and tm
                 and f"func {tm.group(1)}(" in show(wt, "HEAD", f)]
        files = files or [f for f in git(wt, "ls-tree", "-r", "--name-only", "HEAD").split()
                          if f.endswith("/" + name) or f == name]
        if files:
            src = show(wt, "HEAD", files[0]).splitlines()
            a = b = None
            if tm:
                for i, line in enumerate(src):
                    if line.startswith(f"func {tm.group(1)}("):
                        a = i
                        while a > 0 and src[a - 1].startswith("//"):
                            a -= 1
                        b = next(j for j in range(i, len(src)) if src[j] == "}")
                        break
            url = f"https://github.com/{fork}/blob/{branch}/{slug}/{files[0]}"
            if a is not None:
                url += f"#L{a + 1}-L{b + 1}"
            return repro.replace(m.group(0), f"[`{files[0]}`]({url})")
    path = os.path.join(ROOT, "issues", local)
    code = open(path).read() if os.path.exists(path) else ""
    return (repro.replace(m.group(0), f"`{name}`")
            + f"\n\n<details><summary>{name}</summary>\n\n```go\n{code.rstrip()}\n```\n\n</details>")


def render_issue(issue, target, repro):
    f = issue.fields
    if target == "etcd":
        version = re.search(r"etcd-io/etcd@([0-9a-f]{7,40})", f.get("Reproduction", ""))
        return "\n\n".join([
            f"Title: {issue.title}",
            "### What happened?", issue.what,
            "### What did you expect to happen?", f.get("Expected", ""),
            "### How can we reproduce it (as minimally and precisely as possible)?", repro,
            "### Anything else we need to know?", f.get("Impact", ""), ISSUE_DISCLOSURE,
            "### Etcd version (please run commands below)",
            f"The reproduction runs at `main` {version.group(1)[:9] if version else '(no commit)'}.",
        ]) + "\n"
    parts = [f"Title: {issue.title}", issue.what, f.get("Expected", "")]
    if target == "raft":
        parts.append(f.get("Cause", ""))
    parts += [repro, f.get("Impact", ""), ISSUE_DISCLOSURE]
    return "\n\n".join(p for p in parts if p) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("slug")
    ap.add_argument("--worktree")
    ap.add_argument("--base")
    ap.add_argument("--fork", default=None, help="OWNER/REPO of the fork (default: from the worktree's origin)")
    ap.add_argument("--print", choices=["issue", "pr"], dest="show")
    a = ap.parse_args()

    path = os.path.join(ROOT, "issues", a.slug + ".md")
    if not os.path.exists(path):
        sys.exit(f"{path}: no such issue")
    issue = Issue(path)
    repo = re.search(r"etcd-io/(etcd|raft|bbolt)@", issue.fields.get("Reproduction", "") + issue.fix.get("Base", ""))
    target = repo.group(1) if repo else "etcd"
    raft, bbolt = target == "raft", target == "bbolt"

    wt = a.worktree
    m = re.search(r"in `(~/etcd-fixes/[^`]+)`", issue.fix.get("Branch", ""))
    if not wt and m:
        wt = os.path.expanduser(m.group(1))
    base = a.base
    m = re.search(r"@([0-9a-f]{7,40})", issue.fix.get("Base", ""))
    if not base and m:
        base = m.group(1)
    fork = a.fork
    if not fork and wt:
        url = git(wt, "remote", "get-url", "origin").strip()
        m = re.search(r"github\.com[:/](.+?)(\.git)?$", url)
        fork = m.group(1) if m else None

    # A documentation-only fix (SKILL.md, step 7): one commit, the reproduction on a branch repro/<slug> of its own.
    m = re.search(r"`repro/" + re.escape(a.slug) + r"`\s+in\s+`(~/etcd-fixes/[^`]+)`", issue.fix.get("Reproduction branch", ""))
    repro_wt = os.path.expanduser(m.group(1)) if m else None
    branch = "repro" if repro_wt else "fix"

    repro = test_link(issue, fork, branch, a.slug, repro_wt or wt, base)
    issue_text = render_issue(issue, target, repro)
    pr = issue.pr
    pr_text = (pr.rstrip() + "\n\n" + PR_DISCLOSURE + "\n") if pr else None
    if a.show:
        text = issue_text if a.show == "issue" else pr_text
        if text is None:
            sys.exit("no **PR draft**: in the issue's ## Fix section")
        sys.stdout.write(text)
        return

    for name in ("Expected", "Impact", "Reproduction", "Cause"):
        if name not in issue.fields:
            fail(f"file: no **{name}:** paragraph")
    if not issue.what:
        fail("file: no paragraph saying what happens after the title")

    diff = code_diff = ""
    if wt and base:
        revs = git(wt, "rev-list", "--reverse", f"{base}..HEAD").split()

        def names(rev, w=wt):
            return git(w, "diff-tree", "--no-commit-id", "--name-only", "-r", rev).split()

        # the tests, the fix, and optionally the changelog entry in a commit of its own
        code_revs = revs[:2] if len(revs) == 3 and all(f.startswith("CHANGELOG/") for f in names(revs[2])) else revs
        if repro_wt:
            code_revs = revs
            if len(revs) != 1:
                fail(f"commit: {len(revs)} commits on top of the base {base[:9]}; a documentation-only fix is one commit")
            go_files = [f for f in git(wt, "diff", "--name-only", f"{base}..HEAD").split() if f.endswith(".go")]
            if any(f.endswith("_test.go") for f in go_files) or any(
                    go_code(show(wt, base, f)) != go_code(show(wt, "HEAD", f)) for f in go_files):
                fail("commit: the issue names a reproduction branch, but the fix changes code or tests, not only "
                     "documentation; a code fix has the tests commit on fix/<slug>")
            if subprocess.run(["git", "-C", repro_wt, "merge-base", "--is-ancestor", base, "HEAD"]).returncode:
                fail(f"repro: the reproduction branch is not off the base {base[:9]}")
            else:
                rrevs = git(repro_wt, "rev-list", f"{base}..HEAD").split()
                if not rrevs or any(not f.endswith("_test.go") for r in rrevs for f in names(r, repro_wt)):
                    fail("repro: the reproduction branch should add only tests (*_test.go) on top of the base")
                diff = git(repro_wt, "diff", f"{base}..HEAD")
        elif len(code_revs) != 2:
            fail(f"commit: {len(revs)} commits on top of the base {base[:9]}; want the tests, then the fix, then "
                 "optionally the changelog entry")
        else:
            tests = names(code_revs[0])
            if not tests or any(not f.endswith("_test.go") for f in tests):
                fail(f"commit: the first commit should add only the tests (*_test.go), not {tests}")
            if any(f.startswith("CHANGELOG/") for f in names(code_revs[1])):
                warn("commit: the changelog entry goes in a commit of its own, after the fix")
        if fork and fork.endswith(("/etcd", "/bbolt")) and any(f.startswith("CHANGELOG/") for r in revs for f in names(r)):
            warn("commit: etcd's and bbolt's changelogs are updated separately; leave them out of the fix PR")
        for rev in revs:
            msg = git(wt, "log", "-1", "--format=%B", rev)
            if re.search(r"^(Co-Authored-By|Assisted-by|Generated-by):", msg, flags=re.M | re.I):
                fail(f"commit {rev[:9]}: an AI trailer (Co-Authored-By/Assisted-by); upstream's AI policy forbids it")
            if not re.search(r"^Signed-off-by: ", msg, flags=re.M):
                fail(f"commit {rev[:9]}: no Signed-off-by (git commit -s)")
            if len(msg.splitlines()[0]) > 72:
                warn(f"commit {rev[:9]}: subject longer than 72 characters")
            body = [l for l in msg.split("\n\n", 1)[1:2] for l in l.splitlines() if l and not l.startswith("Signed-off-by:")]
            if len(body) > 4:
                warn(f"commit {rev[:9]}: {len(body)} lines of message body; upstream's are mostly none, at most a "
                     "few sentences")
        subject = git(wt, "log", "-1", "--format=%s", code_revs[-1] if code_revs else "HEAD").strip()
        if not repro_wt:
            diff = git(wt, "diff", f"{base}..HEAD")
        code_diff = git(wt, "diff", f"{base}..HEAD", "--", ".", ":(exclude)*_test.go")
        files = [f for f in git(wt, "diff", "--name-only", f"{base}..HEAD").split() if f.endswith(".go")]
        if files:
            out = subprocess.run(["gofmt", "-l", *files], cwd=wt, capture_output=True, text=True).stdout.strip()
            if out:
                fail(f"commit: not gofmt'ed: {out}")
        for line in [] if repro_wt else code_diff.splitlines():  # a documentation fix adds only comments
            if re.match(r"^\+\s*//", line):
                warn(f"fix: added comment, keep it only if it says what the code does not: {line[1:].strip()}")
    else:
        warn("no **Branch**/**Base** in the issue's ## Fix section: commit checks skipped, the test inlined")
        subject = None

    text = issue_text
    p = prose(text)
    code_links = re.findall(r"github\.com/etcd-io/[^/\s]+/blob/([^/\s]+)/", text)
    if raft:
        # A raft issue explains the cause, linking the code at the base (SKILL.md, "The issue").
        for rev in sorted(set(code_links)):
            if not (re.fullmatch(r"[0-9a-f]{40}", rev) and (not base or rev.startswith(base[:7]))):
                fail(f"issue: links the code at {rev}, not by a permalink at the base")
        if not code_links:
            warn("issue: no permalink at the base; a raft issue explains the cause, linking the code")
    elif code_links:
        fail("issue: links into the code outside **Cause:**; the root cause and code links belong in the PR")
    if re.search(r"release-\d", p):
        fail("issue: mentions a release branch; no claims about other releases in the issue")
    if re.search(LOCAL_WORDS, p):
        fail(f"issue: this repository's vocabulary: {sorted(set(re.findall(LOCAL_WORDS, p)))}")
    if fork and not re.search(rf"github\.com/{re.escape(fork)}/(blob|tree)/{branch}/{re.escape(a.slug)}\b", text):
        fail(f"issue: no link to the test on {fork}'s branch {branch}/{a.slug}")
    for link in re.findall(r"github\.com/[^/\s]+/[^/\s]+/blob/(?:fix|repro)/[^\s)#]+_test\.go[^\s)]*", text):
        if "#L" not in link:
            fail(f"issue: the link to the test does not name its lines (#L<a>-L<b>): {link}")
    for t in set(re.findall(r"\bTest\w+", p)):
        if diff and t not in diff:
            fail(f"issue: names {t}, which the branch does not add")
    if base and base[:7] not in text:
        fail(f"issue: does not name the base commit {base[:9]} the reproduction ran on")
    words = len(re.sub(r"\]\([^)]*\)", "]", p).split())  # link targets are not words
    limit = MAX_RAFT_ISSUE_WORDS if raft else MAX_PROSE_WORDS
    if words > limit:
        warn(f"issue: {words} words of prose (outside code and <details>); aim for under {limit}")
    if code_diff and not raft:
        idents = set()
        for line in code_diff.splitlines():
            if line.startswith(("+", "-", " ", "@@")) and not line.startswith(("+++", "---")):
                idents |= set(re.findall(r"\bfunc (?:\([^)]*\) )?(\w+)", line))
                idents |= {i for i in re.findall(r"\b[a-z]+[A-Z]\w*\b", line)}
        found = sorted(i for i in idents if re.search(rf"\b{re.escape(i)}\b", p))
        if found:
            warn(f"issue: names code the fix touches, keep only API names a user sees: {found}")

    if wt:
        for name, t in (("issue", issue_text), ("pr", pr or "")):
            for fpath in set(re.findall(r"`([\w./-]+/[\w.-]+\.(?:go|proto|md|yml|yaml))`", t)):
                if not os.path.exists(os.path.join(wt, fpath)):
                    fail(f"{name}: names `{fpath}`, which is not a path in the repository")

    if pr is None:
        if wt:
            fail("pr: no **PR draft**: in the issue's ## Fix section")
    else:
        if not re.search(r"github\.com/etcd-io/[^/\s]+/blob/[0-9a-f]{40}/", pr):
            warn("pr: no permalink at the base; the root cause should link the lines that matter")
        if not pr.startswith("Title: "):
            fail("pr: first line is not 'Title: <commit subject>'")
        elif subject and pr.splitlines()[0][len("Title: "):] != subject:
            fail(f"pr: title is not the commit subject ({subject!r})")
        body = norm(pr.split("\n", 1)[1] if "\n" in pr else "")
        body = re.sub(r"\]\([^)]*\)", "]", body)  # link targets are not words
        if len(body.split()) > MAX_PR_WORDS:
            warn(f"pr: {len(body.split())} words; etcd fix PRs are a few sentences (aim for under {MAX_PR_WORDS})")
        if re.search(r"^\*\*|^#+ ", pr, flags=re.M):
            fail("pr: has sections (headings or bold labels); etcd fix PRs are a few plain sentences")
        if not re.search(r"\bThis PR (?!was written in part)", pr):
            fail("pr: no 'This PR ...' sentence saying what the change does (not an imperative 'Use ...')")
        if "Fixes #" not in pr:
            warn("pr: no 'Fixes #<issue>' (add it once the issue is filed)")

    for leftover in ("paste output here", "#<", "pull/TODO", "TODO:"):
        for name, t in (("issue", issue_text), ("pr", pr_text or "")):
            if leftover in t:
                fail(f"{name}: an unfilled placeholder or template line: {leftover!r}")

    sys.exit(1 if failures else 0)


ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))

if __name__ == "__main__":
    main()
