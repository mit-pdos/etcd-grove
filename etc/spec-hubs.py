#!/usr/bin/env python3
"""Spec hubs from the git log: which statements reach into many packages, and how often they change
(notes/spec-first-plan.md, "Hubs: the statements that churn").

Usage, from the repository root: python3 -I etc/spec-hubs.py [--ref REF] [--top N] [--json FILE]
(about a minute)

Unit: a declaration of the statement surface, as in etc/spec-churn.py (Spec/ and the shared Proof/
modules: Inv*, Api*, Defs, Base*, ...; RaftWitness's too); the parsing is the same as there.
A declaration's statement: a theorem's/axiom's/instance's type, a definition's whole text, comments
and attributes stripped. Key: (directory, name).

At REF:
- fan-out: the directories, other than its own, whose declarations its statement mentions;
- fan-in: the directories, other than its own, whose statements mention it.
A mention is a whole identifier, or a dotted suffix of one, equal to a declaration's name; names
declared in more than three directories, and names of three characters or fewer, are ignored (too
generic to attribute). This is a name match, not Lean's resolution: the counts are approximate.

Over the whole history: changes, the number of commits that changed the declaration's statement.

Tables: churn by fan-out and by fan-in bucket; the declarations with the widest fan-out
(aggregators: a change to any package they reach changes them); the widest fan-in (vocabulary);
and the cost ranking, changes x fan-in directories (a change there is edited or rebuilt in that
many places).
"""
import re, subprocess, collections, os, argparse, json

ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
ap.add_argument("--ref", default="lean")
ap.add_argument("--top", type=int, default=25)
ap.add_argument("--json", help="write every declaration's counts to this file")
A = ap.parse_args()


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout


log = git("log", A.ref, "--no-merges", "--reverse", "-M", "--name-status", "--format=@@%H|%at|%s",
          "--", "Spec", "Proof", "RaftWitness/Spec", "RaftWitness/Proof")
commits = []
cur = None
for line in log.splitlines():
    if line.startswith("@@"):
        h, t, s = line[2:].split("|", 2)
        cur = {"h": h, "t": int(t), "s": s, "files": []}
        commits.append(cur)
    elif line.strip() and cur:
        p = line.split("\t")
        st = p[0]
        cur["files"].append(("R", p[1], p[2]) if st.startswith("R") else (st[0], p[1], None))

specs_ever = set()
for c in commits:
    for st, p, q in c["files"]:
        for x in (p, q):
            if x and x.endswith(".lean") and x.startswith(("Spec/", "RaftWitness/Spec/")):
                specs_ever.add(x)


def surface_file(p):
    if not p.endswith(".lean") or not p.startswith(("Spec/", "Proof/", "RaftWitness/Spec/", "RaftWitness/Proof/")):
        return False
    if os.path.basename(p) in ("Link.lean", "Results.lean", "Init.lean", "Initialize.lean"):
        return False
    return not ("/Proof/" in "/" + p and p.replace("Proof/", "Spec/", 1) in specs_ever)


cat = subprocess.Popen(["git", "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)


def blob(h, p):
    cat.stdin.write(f"{h}:{p}\n".encode())
    cat.stdin.flush()
    hdr = cat.stdout.readline().decode()
    if hdr.endswith("missing\n"):
        return None
    n = int(hdr.split()[2])
    d = cat.stdout.read(n)
    cat.stdout.read(1)
    return d.decode("utf-8", "replace")


def uncomment(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return "".join(out)


DECL = re.compile(r"^((?:private |protected |noncomputable |partial |nonrec |unsafe )*)"
                  r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\b(.*)")
CONT = re.compile(r"^(\s|\||where\b|deriving\b|$)")


def kw_named(kw, tok):
    return not (kw == "instance" and tok[:1] in (":", "[", "(", "{"))


def decls(src):
    s = re.sub(r"@\[[^\]]*\]", "", uncomment(src))
    res = {}
    curk = None
    buf = []

    def flush():
        if curk is None:
            return
        mods, kw, name = curk
        toks = re.findall(r"\S+", " ".join(buf))
        if kw in ("theorem", "lemma", "instance", "axiom"):
            cut = next((i for i, t in enumerate(toks) if t.startswith(":=")), len(toks))
            toks = toks[:cut]
        if "private" not in mods:
            res[name] = (kw, toks)

    for line in s.split("\n"):
        m = DECL.match(line)
        if m:
            flush()
            rest = m.group(3).split()
            name = rest[0] if rest and kw_named(m.group(2), rest[0]) else "instance:" + " ".join(rest[:8])
            curk = (m.group(1), m.group(2), name)
            buf = [line]
        elif curk and CONT.match(line):
            buf.append(line)
        else:
            flush(); curk = None; buf = []
    flush()
    return res


# replay the history: the statement surface per directory, and each declaration's changes
files = collections.defaultdict(dict)
dirmap = collections.defaultdict(dict)
changes = collections.Counter()
for c in commits:
    aff = set()
    for st, p, q in c["files"]:
        if st == "R":
            files[os.path.dirname(p)].pop(p, None); aff.add(os.path.dirname(p)); path = q
        else:
            path = p
        if not surface_file(path):
            continue
        d = os.path.dirname(path)
        aff.add(d)
        if st == "D":
            files[d].pop(path, None); continue
        src = blob(c["h"], path)
        if src is not None:
            files[d][path] = decls(src)
    for d in aff:
        new = {}
        for p in sorted(files[d]):
            new.update(files[d][p])
        old = dirmap[d]
        for name, (kw, toks) in new.items():
            if name in old and old[name][1] != toks:
                changes[(d, name)] += 1
        dirmap[d] = new

# fan-in and fan-out at REF
ID = re.compile(r"[A-Za-z_][\w'!?.₀-₉]*")
surface = {(d, n): v for d, m in dirmap.items() for n, v in m.items()}
byname = collections.defaultdict(set)
for d, n in surface:
    if not n.startswith("instance:"):
        byname[n].add(d)


def mentions(toks):
    out = set()
    for t in toks:
        for w in ID.findall(t):
            parts = w.split(".")
            for i in range(len(parts)):
                s = ".".join(parts[i:])
                if len(s) > 3 and s in byname and len(byname[s]) <= 3:
                    out.add(s)
    return out


fanout = {}
fanin = collections.defaultdict(set)
for (d, n), (kw, toks) in surface.items():
    tgt = {(dd, s) for s in mentions(toks[1:]) - {n} for dd in byname[s]}
    fanout[(d, n)] = {dd for dd, _ in tgt} - {d}
    for t in tgt:
        if t[0] != d:
            fanin[t].add(d)

rows = [{"dir": d, "name": n, "kw": surface[(d, n)][0], "fanout": len(fanout[(d, n)]),
         "fanin": len(fanin.get((d, n), ())), "changes": changes[(d, n)]} for d, n in surface]
if A.json:
    json.dump(rows, open(A.json, "w"))


def short(d):
    return (d.replace("RaftWitness/", "RW/").replace("Proof/", "P/").replace("Spec/", "S/")
             .replace("go_etcd_io/etcd/server/v3/", "srv/").replace("go_etcd_io/", "")
             .replace("github_com/mit_pdos/etcd_grove/", ""))


def buckets(key):
    print(f"\nchurn by {key} (directories):")
    print(f"{'':>6} {'decls':>7} {'changed':>8} {'chg/decl':>9}")
    for lo, hi, lab in ((0, 0, "0"), (1, 2, "1-2"), (3, 5, "3-5"), (6, 10, "6-10"), (11, 10**9, ">10")):
        sel = [r["changes"] for r in rows if lo <= r[key] <= hi]
        if sel:
            print(f"{lab:>6} {len(sel):7} {100 * sum(1 for x in sel if x) / len(sel):7.1f}% {sum(sel) / len(sel):9.2f}")


def table(title, keyf):
    print(f"\n{title}:")
    print(f"{'out':>4} {'in':>4} {'chg':>4}  {'kind':9} {'name':45} directory")
    for r in sorted(rows, key=keyf)[:A.top]:
        print(f"{r['fanout']:4} {r['fanin']:4} {r['changes']:4}  {r['kw']:9} {r['name'][:45]:45} {short(r['dir'])}")


total = sum(r["changes"] for r in rows)
wide = [r for r in rows if r["fanout"] >= 6]
print(f"{len(rows)} declarations at {A.ref}, {total} statement changes in the history; "
      f"the {len(wide)} with fan-out >= 6 directories carry {sum(r['changes'] for r in wide)} of them")
buckets("fanout")
buckets("fanin")
table("aggregators (widest fan-out)", lambda r: (-r["fanout"], -r["changes"]))
table("vocabulary (widest fan-in)", lambda r: (-r["fanin"], -r["changes"]))
table("cost (changes x fan-in)", lambda r: (-r["changes"] * r["fanin"], -r["changes"]))
table("most changed", lambda r: (-r["changes"], -r["fanout"]))
