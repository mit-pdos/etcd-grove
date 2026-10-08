#!/usr/bin/env python3
"""Land the current branch on `lean` (notes/collaboration.md, "Landing").

  etc/land.py [--task ID] [--then done|review|keep] [--dry-run]

1. Rebase HEAD onto `origin/lean` (dropping empty heartbeat commits) and regenerate
   `EtcdGrove/Raft/Link.lean` (etc/gen-link.py), committing it if it changed.
2. Refuse a change to `manual-notes.txt` (people's file). If `notes/tasks/` changed,
   `etc/tasks.py check`. If anything outside `notes/` changed: `lake build`, then
   `etc/tcb-report.py --check`. Any failure stops the landing.
3. If a protected path (etc/protected-paths.txt) changed: push the branch, open a PR
   to `lean` for a person to merge (with `gh`; otherwise print the compare URL), set
   the task to `needs-human`, and stop.
4. Otherwise push HEAD to `lean`; a push that loses a race goes back to 1.
5. Set the task's state (`--then`; by default `review` if a `Spec/` file, an axiom or
   the TCB baseline changed, else `done`), recording the landed range, and delete the
   task's branch from origin.

The task is --task, or ID from a branch named task/ID; without one, steps 1-4 only.

  etc/land.py --check-protected BEFORE AFTER

For CI: fail if a commit on `lean`'s first-parent history in BEFORE..AFTER changes a
protected path, was not committed by GitHub (a PR merge) and has no `Approved-by:`
trailer (a person pushing directly).
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import tasks as board  # noqa: E402  (etc/tasks.py)

ROOT = board.ROOT
LEAN = board.LEAN
PEOPLE_ONLY = ["manual-notes.txt"]
GITHUB_COMMITTER = "noreply@github.com"


def git(*args, check=True):
    return board.git(*args, check=check)


def protected_globs():
    pats = []
    for line in open(os.path.join(HERE, "protected-paths.txt")):
        line = line.split("#", 1)[0].strip()
        if line:
            pats.append(line)
    return pats


def glob_re(pat):
    out, i = "", 0
    while i < len(pat):
        if pat.startswith("**/", i):
            out, i = out + "(?:.*/)?", i + 3
        elif pat.startswith("**", i):
            out, i = out + ".*", i + 2
        elif pat[i] == "*":
            out, i = out + "[^/]*", i + 1
        elif pat[i] == "?":
            out, i = out + "[^/]", i + 1
        else:
            out, i = out + re.escape(pat[i]), i + 1
    return re.compile(out + r"\Z")


def protected(paths):
    res = [glob_re(p) for p in protected_globs()]
    return [p for p in paths if any(r.match(p) for r in res)]


def run(cmd, what):
    """Run a check, streaming its output; stop the landing if it fails."""
    print(f"land: {what}: {' '.join(cmd)}", flush=True)
    env = dict(os.environ)
    elan = os.path.expanduser("~/.elan/bin")
    if os.path.isdir(elan):
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    if subprocess.run(cmd, cwd=ROOT, env=env).returncode != 0:
        sys.exit(f"land: {what} failed; nothing was pushed. Fix it on this branch and rerun.")


def changed_files(base):
    return [p for p in git("diff", "--name-only", f"{base}..HEAD").stdout.splitlines() if p]


def adds_axiom(base):
    diff = git("diff", "-U0", f"{base}..HEAD", "--", "*.lean").stdout
    return any(re.match(r"\+\s*(private\s+)?axiom\s", l) for l in diff.splitlines())


def check_protected(before, after):
    zero = re.fullmatch(r"0*", before or "")
    if zero or git("merge-base", "--is-ancestor", before, after, check=False).returncode != 0:
        rng = [after, "-1"]
    else:
        rng = [f"{before}..{after}"]
    commits = git("rev-list", "--first-parent", *rng).stdout.split()
    bad = []
    for c in commits:
        email, msg = git("show", "-s", "--format=%ce%x00%B", c).stdout.split("\x00", 1)
        if email.strip() == GITHUB_COMMITTER or re.search(r"^Approved-by:\s*\S", msg, re.M):
            continue
        parents = git("show", "-s", "--format=%P", c).stdout.split()
        files = git("diff", "--name-only", parents[0], c).stdout.split() if parents else \
            git("diff-tree", "--root", "--no-commit-id", "--name-only", "-r", c).stdout.split()
        hits = protected(files)
        if hits:
            bad.append((c, hits))
    for c, hits in bad:
        print(f"{c[:9]} changes protected paths outside a PR: {', '.join(hits)}", file=sys.stderr)
    if bad:
        print("A protected path (etc/protected-paths.txt) changes through a PR that a person "
              "merges, or in a commit with an `Approved-by: <person>` trailer.", file=sys.stderr)
        sys.exit(1)
    print(f"{len(commits)} commits checked, no protected path changed outside a PR")


def open_pr(branch, tid, hits):
    board.push_task_branch(branch)
    title = git("log", "-1", "--format=%s").stdout.strip()
    body = (f"Task: `{tid or '-'}`\n\nThis change touches protected paths (etc/protected-paths.txt), "
            f"so a person merges it:\n\n" + "".join(f"- `{h}`\n" for h in hits) +
            "\nOpened by `etc/land.py`.")
    try:
        p = subprocess.run(["gh", "pr", "create", "--base", "lean", "--head", branch,
                            "--title", title, "--body", body],
                           cwd=ROOT, capture_output=True, text=True)
        if p.returncode == 0:
            return p.stdout.strip().splitlines()[-1]
        print(f"land: gh pr create failed: {p.stderr.strip()}", file=sys.stderr)
    except OSError:
        pass
    url = git("remote", "get-url", "origin").stdout.strip()
    m = re.search(r"github\.com[:/](.+?)(?:\.git)?$", url)
    return f"https://github.com/{m.group(1)}/compare/lean...{branch}?expand=1" if m else branch


def land(a):
    if git("status", "--porcelain", "--untracked-files=no").stdout.strip():
        sys.exit("land: the working tree has uncommitted changes; commit them first")
    branch = git("branch", "--show-current").stdout.strip()
    tid = a.task or board.current_task()
    for attempt in range(a.tries):
        board.fetch()
        base = git("rev-parse", LEAN).stdout.strip()
        # --force-rebase replays every commit, so that --no-keep-empty drops the empty
        # heartbeat commits even when HEAD is already on origin/lean.
        if git("rebase", "-q", "--force-rebase", "--no-keep-empty", LEAN, check=False).returncode != 0:
            git("rebase", "--abort", check=False)
            sys.exit(f"land: rebasing onto origin/lean ({base[:9]}) conflicts. Run "
                     f"`git rebase origin/lean`, resolve, `git rebase --continue`, then rerun. "
                     f"(Never merge EtcdGrove/Raft/Link.lean: take either side and rerun "
                     f"etc/gen-link.py.)")
        subprocess.run([sys.executable, os.path.join(HERE, "gen-link.py")], cwd=ROOT, check=True)
        if git("status", "--porcelain", "--untracked-files=no").stdout.strip():
            git("commit", "-q", "-am", "Regenerate EtcdGrove/Raft/Link.lean (etc/gen-link.py)")
        files = changed_files(base)
        if not files:
            print("land: nothing to land (HEAD is already on origin/lean)")
            break
        people = [f for f in files if f in PEOPLE_ONLY]
        if people:
            sys.exit(f"land: {', '.join(people)} is written by people only; drop that change")
        if any(f.startswith(board.TASKS + "/") for f in files):
            run([sys.executable, os.path.join(HERE, "tasks.py"), "check"], "task board check")
        code = [f for f in files if not f.startswith("notes/")]
        if code and not a.dry_run:
            run(["lake", "build"], "build")
            run([sys.executable, os.path.join(HERE, "tcb-report.py"), "--check"], "trust base check")
        hits = protected(files)
        if hits:
            if a.dry_run:
                print(f"land: --dry-run: would open a PR (protected: {', '.join(hits)})")
                return
            pr_branch = f"task/{tid}" if tid else branch
            url = open_pr(pr_branch, tid, hits)
            print(f"land: protected paths changed ({', '.join(hits)}): PR for a person to merge: {url}")
            if tid:
                board.change_task(tid, lambda t, ts: (
                    t.__setitem__("state", "needs-human"),
                    t.__setitem__("owner", t["owner"] or board.me()),
                    t.history(f"QUESTION from {board.me()}: merge {url} (protected: {', '.join(hits)}); "
                              f"then `etc/tasks.py done {tid}` or `review {tid}`")),
                    f"ask: {tid} (PR)")
            return
        if a.dry_run:
            print(f"land: --dry-run: would push {len(files)} changed files to lean")
            return
        p = git("push", "-q", "origin", "HEAD:refs/heads/lean", check=False)
        if p.returncode == 0:
            print(f"land: pushed to lean: {base[:9]}..{git('rev-parse', '--short=9', 'HEAD').stdout.strip()}")
            break
        if not re.search(r"rejected|fetch first|non-fast-forward", p.stderr):
            sys.exit(f"land: push failed: {p.stderr.strip()}")
        print("land: lost the race to push; rebasing again", flush=True)
    else:
        sys.exit(f"land: lost the race {a.tries} times; rerun")
    if not tid or a.then == "keep":
        return
    head = git("rev-parse", "--short=9", "HEAD").stdout.strip()
    then = a.then or ("review" if any("/Spec/" in f for f in files) or "etc/tcb-baseline.txt" in files
                      or adds_axiom(base) else "done")
    board.set_state(tid, then, f"landed {base[:9]}..{head}")
    br = f"task/{tid}"
    if git("rev-parse", "-q", "--verify", f"refs/remotes/origin/{br}", check=False).returncode == 0:
        git("push", "-q", "origin", "--delete", br, check=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    ap.add_argument("--task")
    ap.add_argument("--then", choices=["done", "review", "keep"])
    ap.add_argument("--dry-run", action="store_true", help="rebase and check the board, build nothing, push nothing")
    ap.add_argument("--tries", type=int, default=10)
    ap.add_argument("--check-protected", nargs=2, metavar=("BEFORE", "AFTER"))
    a = ap.parse_args()
    try:
        if a.check_protected:
            check_protected(*a.check_protected)
        else:
            land(a)
    except board.Error as e:
        sys.exit(f"etc/land.py: {e}")


if __name__ == "__main__":
    main()
