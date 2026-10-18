#!/usr/bin/env python3
"""Check an upstream candidate (issues/upstream/<slug>/) against the rules of SKILL.md that a script can check.

Usage: check.py <slug> [--dir DIR] [--worktree DIR] [--base SHA] [--fork OWNER/REPO]

The worktree and base default to the ones `meta.md` names. Prints FAIL lines (a rule is broken: fix it) and WARN
lines (a judgment call: look at each and decide), and exits 1 if there is a FAIL. It does not judge the writing;
the user does.
"""

import argparse
import os
import re
import subprocess
import sys

ISSUE_DISCLOSURE = (
    "I found this while formally verifying etcd, working with AI tools. "
    "I reproduced the bug and reviewed this report myself."
)
PR_DISCLOSURE = (
    "This PR was written in part with the assistance of AI; I have reviewed and tested every change."
)
# Vocabulary of this repository that means nothing upstream.
LOCAL_WORDS = r"\b(specs?|proofs?|premises?|Goose|Gooseable|ghost|verified code|Lean|Rocq|Perennial|Iris)\b"
MAX_PROSE_WORDS = 250
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


def section(md, title):
    m = re.search(r"^### " + re.escape(title) + r".*?$(.*?)(?=^### |\Z)", md, flags=re.S | re.M)
    return m.group(1).strip() if m else None


def norm(s):
    return " ".join(s.split())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("slug")
    ap.add_argument("--worktree")
    ap.add_argument("--base")
    ap.add_argument("--dir", help="the candidate's directory (default: issues/upstream/<slug>)")
    ap.add_argument("--fork", default=None, help="OWNER/REPO of the fork (default: from the worktree's origin)")
    a = ap.parse_args()

    root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
    d = a.dir or os.path.join(root, "issues", "upstream", a.slug)
    read = lambda f: open(os.path.join(d, f)).read() if os.path.exists(os.path.join(d, f)) else None
    issue, pr, meta = read("issue.md"), read("pr.md"), read("meta.md") or ""

    wt = a.worktree
    if not wt:
        m = re.search(r"in `(~/etcd-fixes/[^`]+)`", meta)
        wt = os.path.expanduser(m.group(1)) if m else None
    base = a.base
    if not base:
        m = re.search(r"\*\*Base\*\*: upstream `main` ([0-9a-f]{7,40})", meta)
        base = m.group(1) if m else None
    fork = a.fork
    if not fork and wt:
        url = git(wt, "remote", "get-url", "origin").strip()
        m = re.search(r"github\.com[:/](.+?)(\.git)?$", url)
        fork = m.group(1) if m else None

    diff = code_diff = ""
    if wt and base:
        n = int(git(wt, "rev-list", "--count", f"{base}..HEAD"))
        if n != 1:
            fail(f"commit: {n} commits on top of the base {base[:9]}, not one")
        msg = git(wt, "log", "-1", "--format=%B")
        if re.search(r"^(Co-Authored-By|Assisted-by|Generated-by):", msg, flags=re.M | re.I):
            fail("commit: an AI trailer (Co-Authored-By/Assisted-by); upstream's AI policy forbids it")
        if not re.search(r"^Signed-off-by: ", msg, flags=re.M):
            fail("commit: no Signed-off-by (git commit -s)")
        subject = msg.splitlines()[0]
        diff = git(wt, "diff", f"{base}..HEAD")
        code_diff = git(wt, "diff", f"{base}..HEAD", "--", ".", ":(exclude)*_test.go")
        files = [f for f in git(wt, "diff", "--name-only", f"{base}..HEAD").split() if f.endswith(".go")]
        if files:
            out = subprocess.run(["gofmt", "-l", *files], cwd=wt, capture_output=True, text=True).stdout.strip()
            if out:
                fail(f"commit: not gofmt'ed: {out}")
        for line in code_diff.splitlines():
            if re.match(r"^\+\s*//", line):
                warn(f"fix: added comment, keep it only if it says what the code does not: {line[1:].strip()}")
    else:
        warn("no worktree/base found in meta.md: commit checks skipped")
        subject = None

    if issue is None:
        fail("issue.md missing")
    else:
        p = prose(issue)
        if re.search(r"github\.com/etcd-io/[^/\s]+/blob/", issue):
            fail("issue: links into the code; the root cause and code links belong in the PR")
        if re.search(r"release-\d", p):
            fail("issue: mentions a release branch; no claims about other releases in the issue")
        if re.search(LOCAL_WORDS, p):
            fail(f"issue: this repository's vocabulary: {sorted(set(re.findall(LOCAL_WORDS, p)))}")
        if re.search(r"linked branch|the branch\b", p) and not fork:
            fail("issue: refers to a branch without a link to it")
        if fork and not re.search(rf"github\.com/{re.escape(fork)}/(blob|tree)/fix/{re.escape(a.slug)}\b", issue):
            fail(f"issue: no link to the test on {fork}'s branch fix/{a.slug}")
        for t in set(re.findall(r"\bTest\w+", p)):
            if diff and t not in diff:
                fail(f"issue: names {t}, which the branch does not add")
        if base and base[:7] not in issue:
            fail(f"issue: does not name the base commit {base[:9]} the reproduction ran on")
        other = section(issue, "Anything else we need to know?")
        if other is None:
            fail("issue: no 'Anything else we need to know?' section")
        elif not norm(other).endswith(norm(ISSUE_DISCLOSURE)):
            fail("issue: 'Anything else' does not end with the standard disclosure, word for word")
        words = len(p.split())
        if words > MAX_PROSE_WORDS:
            warn(f"issue: {words} words of prose (outside code and <details>); aim for under {MAX_PROSE_WORDS}")
        if code_diff:
            idents = set()
            for line in code_diff.splitlines():
                if line.startswith(("+", "-", " ", "@@")) and not line.startswith(("+++", "---")):
                    idents |= set(re.findall(r"\bfunc (?:\([^)]*\) )?(\w+)", line))
                    idents |= {i for i in re.findall(r"\b[a-z]+[A-Z]\w*\b", line)}
            found = sorted(i for i in idents if re.search(rf"\b{re.escape(i)}\b", p))
            if found:
                warn(f"issue: names code the fix touches, keep only API names a user sees: {found}")

    if wt:
        for name, text in (("issue", issue or ""), ("pr", pr or "")):
            for path in set(re.findall(r"`([\w./-]+/[\w.-]+\.(?:go|proto|md|yml|yaml))`", text)):
                if not os.path.exists(os.path.join(wt, path)):
                    fail(f"{name}: names `{path}`, which is not a path in the repository")

    if pr is None:
        fail("pr.md missing")
    else:
        if not re.search(r"github\.com/etcd-io/[^/\s]+/blob/[0-9a-f]{40}/", pr):
            warn("pr: no permalink at the base; the root cause should link the lines that matter")
        if not pr.startswith("Title: "):
            fail("pr: first line is not 'Title: <commit subject>'")
        elif subject and pr.splitlines()[0][len("Title: "):] != subject:
            fail(f"pr: title is not the commit subject ({subject!r})")
        body = norm(pr.split("\n", 1)[1] if "\n" in pr else "").replace(PR_DISCLOSURE, "")
        body = re.sub(r"\]\([^)]*\)", "]", body)  # link targets are not words
        if len(body.split()) > MAX_PR_WORDS:
            warn(f"pr: {len(body.split())} words; etcd fix PRs are a few sentences (aim for under {MAX_PR_WORDS})")
        if re.search(r"^\*\*|^#+ ", pr, flags=re.M):
            fail("pr: has sections (headings or bold labels); etcd fix PRs are a few plain sentences")
        if not re.search(r"\bThis PR (?!was written in part)", pr):
            fail("pr: no 'This PR ...' sentence saying what the change does (not an imperative 'Use ...')")
        if "Fixes #" not in pr:
            fail("pr: no 'Fixes #<issue>'")
        if PR_DISCLOSURE not in norm(pr):
            fail("pr: no standard AI disclosure, word for word")

    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
