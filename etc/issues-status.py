#!/usr/bin/env python3
"""Where each finding in issues/ stands upstream.

Reads the front matter of every issues/*.md (format: issues/README.md) and prints one row per
finding: its upstream state, when it was last checked, and its links.

  --refresh   re-read the state of every linked GitHub issue and PR (open, closed, merged) and
              write it back into the front matter, setting `checked` to today for the files whose
              links were all read. Uses the unauthenticated GitHub API (60 requests an hour) unless
              $GITHUB_TOKEN is set.
  --state S   only the findings in state S (repeatable).
  --check     exit 1 if a file has no front matter or an unknown state.
"""

import argparse
import datetime
import glob
import json
import os
import re
import sys
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATES = ["unchecked", "none", "known", "reported", "fixed", "not-filing"]
LINK = re.compile(r"^(\s*-\s*)([\w.-]+/[\w.-]+)#(\d+)(\s+)(issue|pr)(\s+)(\w+)(:.*)$")


def parse(path):
    """Returns (front-matter dict, list of lines of the block, or None)."""
    with open(path) as f:
        lines = f.read().split("\n")
    if not lines or lines[0] != "---":
        return None, lines
    try:
        end = lines.index("---", 1)
    except ValueError:
        return None, lines
    fm = {"links": []}
    key = None
    for line in lines[1:end]:
        if line.startswith("  - ") and key == "links":
            fm["links"].append(line[4:])
        elif ":" in line and not line.startswith(" "):
            key, _, val = line.partition(":")
            if key != "links":
                fm[key] = val.strip()
    fm["_end"] = end
    return fm, lines


def gh_state(repo, num):
    req = urllib.request.Request(f"https://api.github.com/repos/{repo}/issues/{num}")
    tok = os.environ.get("GITHUB_TOKEN")
    if tok:
        req.add_header("Authorization", f"Bearer {tok}")
    with urllib.request.urlopen(req, timeout=30) as r:
        d = json.load(r)
    if "pull_request" in d:
        return "pr", "merged" if d["pull_request"].get("merged_at") else d["state"]
    return "issue", d["state"]


def refresh(path, fm, lines):
    ok = True
    for i in range(1, fm["_end"]):
        m = LINK.match(lines[i])
        if not m:
            continue
        try:
            kind, state = gh_state(m.group(2), int(m.group(3)))
        except Exception as e:  # rate limit, network
            print(f"{os.path.basename(path)}: {m.group(2)}#{m.group(3)}: {e}", file=sys.stderr)
            ok = False
            continue
        lines[i] = "".join([m.group(1), m.group(2), "#", m.group(3), m.group(4), kind, m.group(6),
                            state, m.group(8)])
    if ok:
        today = datetime.date.today().isoformat()
        for i in range(1, fm["_end"]):
            if lines[i].startswith("checked:"):
                lines[i] = f"checked: {today}"
    with open(path, "w") as f:
        f.write("\n".join(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("--state", action="append")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    bad = 0
    rows = []
    for path in sorted(glob.glob(os.path.join(ROOT, "issues", "*.md"))):
        name = os.path.basename(path)[:-3]
        if name in ("README", "RANKING"):  # the format, and the triage of all of them
            continue
        fm, lines = parse(path)
        if fm is None or fm.get("upstream") not in STATES:
            print(f"{name}: no front matter or unknown state", file=sys.stderr)
            bad += 1
            continue
        if args.refresh and any(LINK.match(lines[i]) for i in range(1, fm["_end"])):
            refresh(path, fm, lines)
            fm, lines = parse(path)
        if args.state and fm["upstream"] not in args.state:
            continue
        rows.append((name, fm["upstream"], fm.get("checked", ""), fm["links"]))

    if not args.check:
        w = max((len(r[0]) for r in rows), default=0)
        for name, state, checked, links in rows:
            print(f"{name:<{w}}  {state:<10}  {checked:<10}  {links[0] if links else ''}")
            for link in links[1:]:
                print(f"{'':<{w}}  {'':<10}  {'':<10}  {link}")
        counts = {s: sum(1 for r in rows if r[1] == s) for s in STATES}
        print("\n" + ", ".join(f"{s}: {n}" for s, n in counts.items() if n))
    sys.exit(1 if bad and args.check else 0)


if __name__ == "__main__":
    main()
