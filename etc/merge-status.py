#!/usr/bin/env python3
"""Git merge drivers for notes/STATUS.md and notes/status-history.md.

Nearly every merge of `lean` (both directions with origin/lean, and every branch re-merging lean)
conflicted only on STATUS.md's "Last updated" line and on status-history.md's tail. These drivers
merge both files the way CLAUDE.md says to by hand ("Before you finish, update notes/STATUS.md").
Set them up in a clone with `etc/setup-merge-drivers.sh` (`.gitattributes` names them; a clone
without the configuration gets git's normal merge).

  merge-status.py status  %O %A %B %P    STATUS.md: everything but the "Last updated" line is merged
                                         by `git merge-file` (a real conflict there keeps its markers
                                         and exits 1); the line is the union of both sides' entries
                                         (an entry is its text; an entry one side edited, same
                                         date and title, is the edited text), minus the ones either
                                         side moved to status-history (in its history, or dropped
                                         by one side relative to the base), newest first (on a date,
                                         new entries, ours then theirs, ahead of the common ones),
                                         the ten newest kept.
  merge-status.py history %O %A %B %P    status-history.md, append-only: the base, with the lines
                                         each side inserted (ours, then theirs' not inserted by ours
                                         too; a side that only moved lines or dropped duplicate
                                         copies: theirs' extra lines appended), plus the entries the
                                         STATUS merge evicts; exits 1 (git merge-file's result) if a
                                         side dropped the last copy of a line or edited one.
  merge-status.py --selftest             replays this week's real merges of the two files and some
                                         synthetic cases.

The entries beyond ten (and base entries a side dropped that no history has) go to
status-history.md only where the history driver runs: a driver writes only its own file, and git
runs the history driver only when both sides changed the history differently. Both drivers compute
the same plan (`plan`) from the three commits (under `git merge`: ours HEAD, theirs the one
`GITHEAD_<oid>` variable git sets, the base their merge-base, each checked against the driver's
input files). Otherwise (both sides moved the same entries, the common case; theirs' history wins;
a rebase or cherry-pick) the evicted entries stay on the "Last updated" line, beyond ten, with a
warning, and the next STATUS update moves them (CLAUDE.md keeps ten).
"""

import os
import re
import subprocess
import sys
import tempfile

STATUS_PATH = "notes/STATUS.md"
HISTORY_PATH = "notes/status-history.md"
PREFIX = "**Last updated:** "
KEEP = 10
SPLIT = re.compile(r"; (?=\d{4}-\d{2}-\d{2} \()")
KEY = re.compile(r"(\d{4}-\d{2}-\d{2}) \((\*\*.*?\*\*)")
MASK = "@@etcd-merge-status: the Last updated line@@"


def warn(msg):
    print(f"merge-status: {msg}", file=sys.stderr)


# ---------------------------------------------------------------- entries


def find_lu(lines):
    for i, l in enumerate(lines[:20]):
        if l.startswith(PREFIX):
            return i
    return None


def entries_of(line):
    body = line.rstrip("\n")[len(PREFIX):]
    return [e for e in SPLIT.split(body) if e] if body else []


def date_of(e):
    m = re.match(r"\d{4}-\d{2}-\d{2}", e)
    return m.group(0) if m else ""


def key_of(e):
    m = KEY.match(e)
    return (m.group(1), m.group(2)) if m else None


def hist_line(e):
    return "- " + e


def normalize_edits(base, side):
    """Map a side's edits of base entries (same date and title, other text) back: returns the side
    with each such edit replaced by its base entry, and {base entry: edited text}."""
    bset = set(base)
    gone = [b for b in base if b not in set(side)]
    bykey = {}
    for b in gone:
        k = key_of(b)
        if k is not None:
            bykey.setdefault(k, []).append(b)
    out, edits = [], {}
    for e in side:
        k = key_of(e)
        if e not in bset and k in bykey and bykey[k]:
            b = bykey[k].pop(0)
            edits[b] = e
            out.append(b)
        else:
            out.append(e)
    return out, edits


def merge_entries(base, ours, theirs, history_lines):
    """The merged "Last updated" entries, newest first, and the base entries a side dropped that
    no history has (lost by that side: they go to the history with the entries evicted)."""
    ours, ed_o = normalize_edits(base, ours)
    theirs, ed_t = normalize_edits(base, theirs)
    hist = set(history_lines)
    bset, oset, tset = set(base), set(ours), set(theirs)
    moved = {b for b in base if b not in oset or b not in tset}

    def final(e):
        if e in ed_o and e in ed_t and ed_o[e] != ed_t[e]:
            return [ed_o[e], ed_t[e]]
        return [ed_o.get(e, ed_t.get(e, e))]

    new = [e for e in ours if e not in bset] + [e for e in theirs if e not in bset and e not in oset]
    common = [e for e in ours if e in bset and e not in moved]
    # newest first; stable: on a date, new entries (ours, then theirs) ahead of the common ones,
    # each in its side's order (an older new entry does not push out a newer common one)
    merged = sorted(new + common, key=date_of, reverse=True)
    out, seen = [], set()
    for e in merged:
        for f in final(e):
            if f in seen or hist_line(f) in hist:
                continue
            seen.add(f)
            out.append(f)
    lost = [f for b in base if b in moved and hist_line(b) not in hist
            for f in final(b) if hist_line(f) not in hist and f not in seen]
    return out, lost


# ---------------------------------------------------------------- git helpers


def git(*args, input=None, check=True):
    r = subprocess.run(["git", *args], input=input, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r


def show(commit, path):
    r = git("show", f"{commit}:{path}", check=False)
    return r.stdout if r.returncode == 0 else None


def merge_file(o, a, b, labels=("ours", "base", "theirs")):
    """git merge-file -p on three texts: (text, clean)."""
    with tempfile.TemporaryDirectory(prefix="merge-status.") as d:
        ps = []
        for n, t in zip("oab", (o, a, b)):
            p = os.path.join(d, n)
            with open(p, "w") as f:
                f.write(t)
            ps.append(p)
        r = subprocess.run(["git", "merge-file", "-p", "-L", labels[0], "-L", labels[1],
                            "-L", labels[2], ps[1], ps[0], ps[2]], capture_output=True, text=True)
        if r.returncode < 0 or r.returncode > 127:
            raise RuntimeError(f"git merge-file: {r.stderr.strip()}")
        return r.stdout, r.returncode == 0


def merge_commits():
    """(ours, theirs, base) of a `git merge` in progress, or None."""
    heads = [k[len("GITHEAD_"):] for k in os.environ if k.startswith("GITHEAD_")]
    if len(heads) != 1:
        return None
    r = git("merge-base", "HEAD", heads[0], check=False)
    if r.returncode != 0 or not r.stdout.strip():
        return None
    return ("HEAD", heads[0], r.stdout.split()[0])


# ---------------------------------------------------------------- the two merges


def merge_history(o, a, b):
    """Append-only union: (text, clean). Lines a side inserted go in at their place (ours first,
    then theirs' not inserted by ours too); if a side moved lines or dropped a duplicate copy (every
    base line still there, in another order), theirs' lines that ours lacks (as a multiset) are
    appended at the end. A side that dropped the last copy of a base line, or edited one, conflicts
    (git merge-file's result)."""
    import difflib
    from collections import Counter
    o, a, b = terminate(o), terminate(a), terminate(b)
    if a.startswith(o) and b.startswith(o):
        ta, tb = a[len(o):].splitlines(True), b[len(o):].splitlines(True)
        added = {l for l in ta if l.strip()}
        return terminate(o + "".join(ta) + "".join(l for l in tb if not (l.strip() and l in added))), True
    ol, al, bl = o.splitlines(True), a.splitlines(True), b.splitlines(True)
    if any(not set(ol) <= set(side) for side in (al, bl)):
        return merge_file(o, a, b)[0], False
    ins = []
    for side in (al, bl):
        hunks = {}
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, ol, side, autojunk=False).get_opcodes():
            if tag == "equal":
                continue
            if tag != "insert":
                hunks = None
                break
            hunks.setdefault(i1, []).extend(side[j1:j2])
        ins.append(hunks)
    if None in ins:
        extra = Counter(bl) - Counter(al)
        tail = []
        for l in reversed(bl):  # the last occurrences: the lines theirs appended
            if extra[l] > 0:
                extra[l] -= 1
                tail.append(l)
        return terminate(a) + "".join(reversed(tail)), True
    ours_added = {l for ls in ins[0].values() for l in ls if l.strip()}
    out = []
    for i in range(len(ol) + 1):
        out.extend(ins[0].get(i, []))
        out.extend(l for l in ins[1].get(i, []) if not (l.strip() and l in ours_added))
        if i < len(ol):
            out.append(ol[i])
    return terminate("".join(out)), True


def terminate(text):
    return text + "\n" if text and not text.endswith("\n") else text


def append_history(text, entries):
    """text with the entries appended (those it lacks), oldest first."""
    have = set(text.splitlines())
    es = sorted(reversed([e for e in entries if hist_line(e) not in have]), key=date_of)
    return terminate(text) + "".join(hist_line(e) + "\n" for e in dict.fromkeys(es))


def status_entries(o, a, b, history_text):
    """merge_entries of three STATUS texts, or (None, []) if a version has no "Last updated" line."""
    vs = [t.splitlines(True) for t in (o, a, b)]
    idx = [find_lu(v) for v in vs]
    if None in idx:
        return None, []
    return merge_entries(*(entries_of(v[i]) for v, i in zip(vs, idx)), history_text.splitlines())


def plan(st, hi):
    """What the merge of the commits with STATUS texts st and history texts hi (base, ours, theirs
    each) does: a dict with
      history  the history the merge commits (git's trivial result, or the history driver's, which
               holds the evicted entries);
      hclean   the history merged without conflict;
      entries  the merged "Last updated" entries, newest first (None: no such line);
      evicted  the entries beyond KEEP that no history has yet;
      lost     the base entries a side dropped that no history has;
      where    where the evicted and lost entries go: "history" (the history driver appended
               them), "line" (no history driver runs: the evicted kept on the line; the lost ones
               are left out, as the side that dropped them did)."""
    ho, ha, hb = hi
    driver = not (ha == hb or ho == hb or ho == ha)
    if driver:
        h, hclean = merge_history(ho, ha, hb)
    else:
        h, hclean = (hb if ho == ha and ha != hb else ha), True
    es, lost = status_entries(*st, h) if st is not None else (None, [])
    have = set(h.splitlines())
    evicted = [e for e in (es or [])[KEEP:] if hist_line(e) not in have]
    where = None
    if evicted or lost:
        if driver and hclean:
            h, where = append_history(h, evicted + lost), "history"
        else:
            where = "line"
    return {"history": h, "hclean": hclean, "entries": es, "evicted": evicted, "lost": lost, "where": where}


def merge_status(o, a, b, entries, extra=()):
    """The merged STATUS text: (text, clean). entries: the merged "Last updated" entries (None:
    merge the whole file with git merge-file); the first KEEP and extra are written."""
    if entries is None:
        return merge_file(o, a, b)
    masked = []
    for t in (o, a, b):
        ls = t.splitlines(True)
        ls[find_lu(ls)] = MASK + "\n"
        masked.append("".join(ls))
    text, clean = merge_file(*masked)
    return text.replace(MASK, PREFIX + "; ".join(list(entries[:KEEP]) + list(extra)), 1), clean


# ---------------------------------------------------------------- the drivers


def read(p):
    with open(p, encoding="utf-8", newline="") as f:
        return f.read()


def write(p, t):
    with open(p, "w", encoding="utf-8", newline="") as f:
        f.write(t)


def driver(mode, po, pa, pb, path):
    o, a, b = read(po), read(pa), read(pb)
    commits = merge_commits()
    other = HISTORY_PATH if mode == "status" else STATUS_PATH
    triple = None
    if commits is not None:
        ours, theirs, base = commits
        if [show(base, path), show(ours, path), show(theirs, path)] == [o, a, b]:
            triple = [show(base, other), show(ours, other), show(theirs, other)]
            if None in triple:
                triple = None
    if mode == "history":
        if triple is not None:
            p = plan(triple, (o, a, b))
            out, ok = p["history"], p["hclean"]
        else:
            out, ok = merge_history(o, a, b)
        if not ok:
            warn(f"{path}: a side deleted or edited lines (it is append-only); merged by git merge-file")
        write(pa, out)
        return 0 if ok else 1
    if triple is not None:
        p = plan((o, a, b), triple)
    else:  # no commits (rebase, cherry-pick): ours' history, from the working tree
        try:
            hist = read(HISTORY_PATH)
        except OSError:
            hist = ""
        es, lost = status_entries(o, a, b, hist)
        have = set(hist.splitlines())
        ev = [e for e in (es or [])[KEEP:] if hist_line(e) not in have]
        p = {"entries": es, "evicted": ev, "lost": lost, "where": "line" if ev or lost else None}
    extra = []
    if p["where"] == "line":
        extra = p["evicted"]
        if p["lost"]:
            warn(f"{path}: {len(p['lost'])} entries dropped by one side are in no {HISTORY_PATH}: left out")
        if extra:
            warn(f"{path}: {len(extra)} entries beyond {KEEP} kept on the \"Last updated\" line (the merged "
                 f"{HISTORY_PATH} would not have them): move them to {HISTORY_PATH} by hand")
    out, ok = merge_status(o, a, b, p["entries"], extra)
    if not ok:
        warn(f"{path}: conflict outside the \"Last updated\" line")
    write(pa, out)
    return 0 if ok else 1


# ---------------------------------------------------------------- selftest


REPLAY_BRANCHES = ["lean", "merge-origin7", "k8s-7g", "auth-lease-s4"]
# (2026-11-21) explicit times: git reads a bare date as that day at the current time of day, so the
# window grew past midnight and took in that night's merges (ea5de40e16, resolved by hand at the time;
# its two entries are in the history since), failing every landing from 00:15 on
REPLAY_SINCE, REPLAY_UNTIL = "2026-11-18 00:00:00 -0500", "2026-11-21 00:00:00 -0500"
# Merges whose replay finds a problem the driver is right about (the merge's own inputs), with why:
# (2026-11-21, backend-snapshot's landing) cf54600750 merged `lean` while it held the k8s-authz revert
# (037b2e926d), which had taken the two KEP-5681 history entries out on purpose; the merge kept the
# revert (so dropped them), and 1e08dd38e7 (the revert reverted) put them back on `lean`.
REPLAY_KNOWN = {"cf54600750": ("history lost lines",
                               "the k8s-authz revert 037b2e926d; restored by 1e08dd38e7")}


def side_entries(t):
    ls = t.splitlines(True)
    i = find_lu(ls)
    return entries_of(ls[i]) if i is not None else []


def check_result(st, hi, s, h, evicted, where):
    """The selftest's checks of a merged STATUS s and committed history h: a list of problems."""
    pr = []
    if "<<<<<<<" in s or "<<<<<<<" in h:
        pr.append("conflict markers")
    got = side_entries(s)
    if (len(got) > KEEP and where != "line") or (len(got) < KEEP and evicted):
        pr.append(f"the line has {len(got)} entries")
    hl = set(h.splitlines())
    for t in st[1:]:
        for e in side_entries(t):
            if e not in got and hist_line(e) not in hl and \
                    not any(key_of(e) is not None and key_of(g) == key_of(e) for g in got):
                pr.append(f"entry lost: {e[:60]}")
    for side in hi[1:]:
        if not set(side.splitlines()) <= hl:
            pr.append("history lost lines")
            break
    return pr


def replay(m):
    """Replays merge commit m: None if git would not run the STATUS driver, else a dict."""
    ps = git("rev-list", "--parents", "-n1", m).stdout.split()[1:]
    if len(ps) != 2:
        return None
    r = git("merge-base", ps[0], ps[1], check=False)
    if r.returncode != 0:
        return None
    base = r.stdout.split()[0]
    st = [show(c, STATUS_PATH) for c in (base, ps[0], ps[1])]
    hi = [show(c, HISTORY_PATH) for c in (base, ps[0], ps[1])]
    if None in st or None in hi or st[1] == st[2] or st[0] in (st[1], st[2]):
        return None
    p = plan(st, hi)
    h = p["history"]
    s, sclean = merge_status(*st, p["entries"], p["evicted"] if p["where"] == "line" else [])
    res = {"m": m[:10], "where": p["where"], "sconflict": not sclean, "hconflict": not p["hclean"]}
    if not p["hclean"]:
        res["problems"] = []
        return res
    res["problems"] = check_result(st, hi, s, h, p["evicted"], p["where"]) if sclean else []
    res["short"] = len(side_entries(s)) < KEEP
    res["over"] = len(side_entries(s)) > KEEP
    res["committed"] = side_entries(show(m, STATUS_PATH))
    res["got"] = side_entries(s)
    return res


def synthetic():
    fails = []
    E = [f"2026-11-{d:02d} (**e{d}**: text {d})" for d in range(1, 20)]
    body = "a\nb\nc\nd\ne\n"

    def st(es, body=body):
        return "# Status\n\n" + PREFIX + "; ".join(es) + "\n" + body

    def hist(es, pre=""):
        return "# History\n\n" + pre + "".join(hist_line(e) + "\n" for e in es)

    def run(sts, his):
        p = plan(sts, his)
        h = p["history"]
        s, c = merge_status(*sts, p["entries"], p["evicted"] if p["where"] == "line" else [])
        return p, s, c, h

    base = list(reversed(E[0:10]))       # e10 .. e1
    ours = [E[10]] + base[:9]            # e11, e10..e2 (e1 moved)
    theirs = [E[11]] + base[:9]          # e12, e10..e2 (e1 moved)
    want = [E[11], E[10]] + base[:8]
    # both add one and move the same entry: identical histories, so no history driver runs
    p, s, c, h = run((st(base), st(ours), st(theirs)), (hist([]), hist([E[0]]), hist([E[0]])))
    if not (c and side_entries(s) == want + [base[8]] and p["where"] == "line" and h == hist([E[0]])):
        fails.append(f"both add one, same move: {p['where']} {side_entries(s)}")
    # ... with otherwise different histories: the history driver appends the evicted entry
    p, s, c, h = run((st(base), st(ours), st(theirs)), (hist([]), hist([E[0]], "x\n"), hist([E[0]], "y\n")))
    if not (c and side_entries(s) == want and p["where"] == "history" and h.count(hist_line(E[0])) == 1
            and h.splitlines()[-1] == hist_line(E[1])):
        fails.append(f"both add one, histories differ: {p['where']} {h!r}")
    # theirs' history wins (ours did not change it): the evicted entry stays on the line
    p, s, c, h = run((st(base), st(ours), st(theirs)), (hist([]), hist([]), hist([E[0]])))
    if not (c and p["where"] == "line" and side_entries(s) == want + [base[8]]):
        fails.append(f"theirs' history: {p['where']} {len(side_entries(s))}")
    # an entry one side dropped is moved, even if no history has it
    p, s, c, h = run((st(base), st(base[:9]), st(theirs)), (hist([]), hist([]), hist([E[0]])))
    if base[9] in side_entries(s):
        fails.append("an entry dropped by one side came back")
    # a real conflict elsewhere still conflicts, with the line composed
    hi = (hist([]), hist([E[0]]), hist([E[0]]))
    p, s, c, h = run((st(base), st(ours, "a\nB1\nc\nd\ne\n"), st(theirs, "a\nB2\nc\nd\ne\n")), hi)
    if c or "<<<<<<<" not in s or side_entries(s) != want + [base[8]]:
        fails.append("a real conflict elsewhere was not kept")
    # changes elsewhere on both sides merge cleanly
    p, s, c, h = run((st(base), st(ours, "a\nB1\nc\nd\ne\n"), st(theirs, "a\nb\nc\nd\nE2\n")), hi)
    if not c or not s.endswith("a\nB1\nc\nd\nE2\n"):
        fails.append("a clean change elsewhere was not merged")
    # an edited entry (same date and title) replaces the base text
    ed = base[3].replace("text", "edited text")
    p, s, c, h = run((st(base), st(base[:3] + [ed] + base[4:]), st(theirs)), (hist([]), hist([]), hist([E[0]])))
    if ed not in side_entries(s) or base[3] in side_entries(s):
        fails.append("an edited entry was not taken")
    # history: a deletion conflicts; insertions in the middle and at the end merge; a move appends
    if merge_history("a\nb\nc\n", "a\nc\n", "a\nb\nc\nd\n")[1]:
        fails.append("a history deletion did not conflict")
    if merge_history("a\nb\nc\n", "a\nB\nc\n", "a\nb\nc\nd\n")[1]:
        fails.append("a history edit did not conflict")
    t, c = merge_history("a\nb\n", "a\nX\nb\nY\n", "a\nb\nY\nZ\n")
    if not c or t != "a\nX\nb\nY\nZ\n":
        fails.append(f"history insertions: {t!r}")
    t, c = merge_history("a\nb\nc\n", "b\na\nc\nX\n", "a\nb\nc\nX\nY\n")
    if not c or t != "b\na\nc\nX\nY\n":
        fails.append(f"history move: {t!r}")
    return fails


def selftest():
    fails = synthetic()
    print(f"merge-status selftest: synthetic cases: {'ok' if not fails else 'FAILED'}")
    for f in fails:
        print("  " + f)
    refs = [b for b in REPLAY_BRANCHES if git("rev-parse", "--verify", "-q", b, check=False).returncode == 0]
    ms = git("log", "--merges", "--format=%H", f"--since={REPLAY_SINCE}", f"--until={REPLAY_UNTIL}",
             *(refs or ["HEAD"]), "--", STATUS_PATH).stdout.split()
    seen, rs = set(), []
    for m in ms:
        if m not in seen:
            seen.add(m)
            r = replay(m)
            if r is not None:
                rs.append(r)
    # merges whose replay problem is the merge's own input, not the driver's (`REPLAY_KNOWN`)
    bad = [r for r in rs if r["problems"] and
           not (r["m"] in REPLAY_KNOWN and set(r["problems"]) <= {REPLAY_KNOWN[r["m"]][0]})]
    for r in bad:
        print(f"  {r['m']}: " + "; ".join(r["problems"]))
    hconf = [r["m"] for r in rs if r["hconflict"]]
    sconf = [r["m"] for r in rs if r["sconflict"] and not r["hconflict"]]
    diff = [r for r in rs if not r["hconflict"] and not r["sconflict"] and r["got"] != r["committed"]]
    from collections import Counter
    wh = Counter(r["where"] or "none evicted" for r in rs if not r["hconflict"])
    over = [r for r in rs if not r["hconflict"] and r.get("over")]
    print(f"merge-status selftest: {len(rs)} real merges replayed ({', '.join(refs) or 'HEAD'}): "
          f"{len(bad)} with problems; {len(hconf)} history conflicts (a side edited or dropped history lines)"
          f"{': ' + ' '.join(hconf) if hconf else ''}; {len(sconf)} conflicts outside the line"
          f"{': ' + ' '.join(sconf) if sconf else ''}; evicted entries: {dict(wh)}; "
          f"{len(over)} lines beyond {KEEP} entries (left for the next STATUS update); "
          f"{len(diff)} lines differ from the committed one")
    if os.environ.get("MERGE_STATUS_VERBOSE"):
        for r in diff:
            c, g = r["committed"], r["got"]
            print(f"  {r['m']}: committed {len(c)}; only committed: {[e[:50] for e in c if e not in g]}; "
                  f"only driver: {[e[:50] for e in g if e not in c]}"
                  f"{'; same set, other order' if set(c) == set(g) else ''}")
    return 0 if not fails and not bad else 1


def main(argv):
    if argv[1:] == ["--selftest"]:
        return selftest()
    if len(argv) == 6 and argv[1] in ("status", "history"):
        try:
            return driver(*argv[1:])
        except Exception as e:  # never leave a half-written file without saying so
            warn(f"failed ({e}); falling back to git merge-file")
            o, a, b = (read(p) for p in argv[2:5])
            t, c = merge_file(o, a, b)
            write(argv[3], t)
            return 0 if c else 1
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
