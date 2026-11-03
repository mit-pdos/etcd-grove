#!/usr/bin/env python3
"""Where each finding in issues/ and nonissues/ stands upstream, and their indexes.

Reads the front matter of every issues/*.md and nonissues/*.md (format: issues/README.md) and prints
one row per finding: its directory, upstream state, whether it blocks the proof, when upstream was
last checked, and its links.

  --refresh   re-read the state of every linked GitHub issue and PR (open, closed, merged) and
              write it back into the front matter, setting `checked` to today for the files whose
              links were all read. Uses the unauthenticated GitHub API (60 requests an hour) unless
              $GITHUB_TOKEN is set; each link is read once a run, a merged PR not again (it stays
              merged), and a file checked today is skipped, so a run cut short by the rate limit
              is finished by running it again after the limit resets.
  --state S   only the findings in upstream state S (repeatable).
  --issues    only issues/; --nonissues only nonissues/.
  --index     rewrite issues/INDEX.md and nonissues/INDEX.md from the files.
  --check     exit 1 if a file's front matter or sections do not follow issues/README.md, an issue
              has no test in issues/<slug>/, or an INDEX.md differs from what --index writes.
"""

import argparse
import datetime
import glob
import json
import os
import re
import sys
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ["issues", "nonissues"]
STATES = ["none", "reported", "known", "fixed"]
FILED = ("reported", "known", "fixed")
BLOCKS = ["yes", "no"]
SKIP = ("README", "INDEX")
LINK = re.compile(r"^(\s*-\s*)([\w.-]+/[\w.-]+)#(\d+)(\s+)(issue|pr)(\s+)(\w+)(:.*)$")
# Leftovers of templates and drafts that must not reach a report.
LEFTOVERS = ["paste output here", "#<", "pull/TODO", "TODO:"]


def parse(path):
    """Returns (front-matter dict, list of lines of the file), the dict None without front matter."""
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


def body(lines, fm):
    return "\n".join(lines[fm["_end"] + 1:])


def title(text):
    m = re.search(r"^# (.+)$", text, re.M)
    return m.group(1).strip() if m else ""


def field(text, name):
    """The text of a `**Name:**` paragraph, up to the next blank line."""
    m = re.search(r"^\*\*" + re.escape(name) + r":\*\*\s*(.*?)(?:\n\s*\n|\Z)", text, re.M | re.S)
    return " ".join(m.group(1).split()) if m else None


def problems(d, name, fm, text):
    """What --check reports for one file."""
    out = []
    if fm.get("upstream") not in STATES:
        out.append(f"upstream: {fm.get('upstream')!r} is not one of {', '.join(STATES)}")
    if fm.get("blocks-proof") not in BLOCKS:
        out.append(f"blocks-proof: {fm.get('blocks-proof')!r} is not yes or no")
    if not title(text):
        out.append("no `# title` line")
    if "## Proof" not in text:
        out.append("no `## Proof` section")
    if d == "issues":
        need = ["Reproduction"]
        if fm.get("upstream") not in FILED:
            need += ["Expected", "Impact", "Cause"]
        out += [f"no **{n}:** paragraph" for n in need if field(text, n) is None]
        tests = glob.glob(os.path.join(ROOT, d, name, "*.go")) + [
            p for p in glob.glob(os.path.join(ROOT, d, name, "*.patch")) if "_test.go" in open(p).read()]
        if not tests:
            out.append(f"no test in issues/{name}/")
    else:
        if field(text, "Why not an issue") is None:
            out.append("no **Why not an issue:** line")
    out += [f"contains {s!r}" for s in LEFTOVERS if s in text]
    return out


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


SEEN = {}  # (repo, number) -> (kind, state), or None after a failed read
LIMITED = []  # non-empty once the API refused a request for the rate limit


def refresh(path, fm, lines):
    ok = True
    for i in range(1, fm["_end"]):
        m = LINK.match(lines[i])
        if not m:
            continue
        key = (m.group(2), int(m.group(3)))
        if m.group(5) == "pr" and m.group(7) == "merged":
            continue
        if key not in SEEN and LIMITED:
            SEEN[key] = None
        if key not in SEEN:
            try:
                SEEN[key] = gh_state(*key)
            except Exception as e:  # rate limit, network
                SEEN[key] = None
                if isinstance(e, urllib.error.HTTPError) and e.code in (403, 429):
                    LIMITED.append(key)
                print(f"{os.path.basename(path)}: {key[0]}#{key[1]}: {e}", file=sys.stderr)
        if SEEN[key] is None:
            ok = False
            continue
        kind, state = SEEN[key]
        lines[i] = "".join([m.group(1), m.group(2), "#", m.group(3), m.group(4), kind, m.group(6),
                            state, m.group(8)])
    if ok:
        today = datetime.date.today().isoformat()
        for i in range(1, fm["_end"]):
            if lines[i].startswith("checked:"):
                lines[i] = f"checked: {today}"
    with open(path, "w") as f:
        f.write("\n".join(lines))


def cell(s):
    return s.replace("|", "\\|")


def index(d, rows):
    """The text of <d>/INDEX.md for the findings rows of directory d."""
    out = ["<!-- Generated by etc/issues-status.py --index from the files; do not edit. -->", ""]
    if d == "issues":
        out += ["# Issues", "",
                "The bugs with a valid failing Go test (format: [README.md](README.md)); the findings "
                "without one are in [../nonissues/](../nonissues/INDEX.md).", ""]
        groups = [("Not reported", ["none"]), ("Reported by us", ["reported"]),
                  ("Reported by others", ["known"]), ("Fixed upstream", ["fixed"])]
        for head, states in groups:
            sel = [r for r in rows if r["upstream"] in states]
            if not sel:
                continue
            out += [f"## {head} ({len(sel)})", "",
                    "| Issue | Blocks proof | Upstream links |", "|---|---|---|"]
            for r in sorted(sel, key=lambda r: (r["blocks"] != "yes", r["name"])):
                links = "; ".join(l.split(":")[0] for l in r["links"])
                out.append(f"| [{cell(r['title'])}]({r['name']}.md) | {r['blocks']} | {cell(links)} |")
            out.append("")
    else:
        out += ["# Non-issues", "",
                "Findings without a valid failing Go test: found by code reading, preconditions "
                "etcd meets, documentation, behavior etcd does not guarantee "
                "([../issues/README.md](../issues/README.md), \"A non-issue\").", "",
                "| Finding | Why not an issue | Blocks proof | Upstream |", "|---|---|---|---|"]
        for r in sorted(rows, key=lambda r: r["name"]):
            out.append(f"| [{cell(r['title'])}]({r['name']}.md) | {cell(r['why'] or '')} | "
                       f"{r['blocks']} | {r['upstream']} |")
        out.append("")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("--state", action="append")
    ap.add_argument("--issues", action="store_true")
    ap.add_argument("--nonissues", action="store_true")
    ap.add_argument("--index", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    bad = 0
    rows = {d: [] for d in DIRS}
    for d in DIRS:
        for path in sorted(glob.glob(os.path.join(ROOT, d, "*.md"))):
            name = os.path.basename(path)[:-3]
            if name in SKIP:
                continue
            fm, lines = parse(path)
            if fm is None:
                print(f"{d}/{name}.md: no front matter", file=sys.stderr)
                bad += 1
                continue
            if (args.refresh and fm.get("checked") != datetime.date.today().isoformat()
                    and any(LINK.match(lines[i]) for i in range(1, fm["_end"]))):
                refresh(path, fm, lines)
                fm, lines = parse(path)
            text = body(lines, fm)
            if args.check:
                for p in problems(d, name, fm, text):
                    print(f"{d}/{name}.md: {p}", file=sys.stderr)
                    bad += 1
            rows[d].append({"name": name, "upstream": fm.get("upstream", ""),
                            "blocks": fm.get("blocks-proof", ""), "checked": fm.get("checked", ""),
                            "links": fm["links"], "title": title(text) or name,
                            "why": field(text, "Why not an issue")})

    for d in DIRS:
        path = os.path.join(ROOT, d, "INDEX.md")
        want = index(d, rows[d])
        if args.index:
            with open(path, "w") as f:
                f.write(want)
        elif args.check:
            have = open(path).read() if os.path.exists(path) else None
            if have != want:
                print(f"{d}/INDEX.md: out of date (etc/issues-status.py --index)", file=sys.stderr)
                bad += 1

    if not args.check and not args.index:
        shown = [d for d in DIRS if not (args.issues or args.nonissues)
                 or (d == "issues" and args.issues) or (d == "nonissues" and args.nonissues)]
        sel = [(d, r) for d in shown for r in rows[d] if not args.state or r["upstream"] in args.state]
        w = max((len(r["name"]) for _, r in sel), default=0)
        for d, r in sel:
            links = r["links"] or [""]
            print(f"{d:<9}  {r['name']:<{w}}  {r['upstream']:<8}  blocks:{r['blocks']:<3}  "
                  f"{r['checked']:<10}  {links[0]}")
            for link in links[1:]:
                print(f"{'':<9}  {'':<{w}}  {'':<8}  {'':<10}  {'':<10}  {link}")
        for d in shown:
            counts = {s: sum(1 for r in rows[d] if r["upstream"] == s) for s in STATES}
            blocks = sum(1 for r in rows[d] if r["blocks"] == "yes")
            print(f"\n{d}: {len(rows[d])}; " + ", ".join(f"{s}: {n}" for s, n in counts.items() if n)
                  + f"; blocks the proof: {blocks}")
    sys.exit(1 if bad and args.check else 0)


if __name__ == "__main__":
    main()
