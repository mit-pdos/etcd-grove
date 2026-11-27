#!/usr/bin/env python3
"""Refuse an unlisted difference between a distributed-deployment interim axiom and the in-process
spec it copies (M1, 2026-11-26; `notes/axiom-review/dist-axiom-diff.md`).

The interim trust-boundary axioms of the distributed deployment (`*_dist`: `NewServer_dist`,
`KV_Put_dist`, `bootstrap.wp_proof_dist`, ...) restate a proved in-process spec with a few changes
(a network fact replaced by the peer addresses', the client's handle by `kvClientAt`, ...). A copy
drifts when its source changes later: `NewServer.specG` took `etcdURLsFit` (2026-11-24) after
`NewServer.specG_dist` had been copied from it, and the copy, without the premise, claimed more than
the proof does, while its header still said "the rest is its text verbatim". This gate compares the
two texts and fails on any difference not listed, with its reason, in `etc/dist-axiom-diff-allow.txt`:

    pair NAME DISTFILE DISTSPEC SRCFILE SRCSPEC   the axiom NAME's statement `DISTSPEC` (an `abbrev` of
                                                  DISTFILE) is a copy of SRCFILE's `SRCSPEC`: an
                                                  `abbrev` (a spec), or a `theorem` (its statement, up
                                                  to `:= by`: a proved contract with no spec of its
                                                  own, e.g. the auth-on `client.client_put_on`)
    dev NAME <<< MINUS ||| PLUS >>> reason        a listed difference: SRCSPEC's tokens MINUS replaced by
                                                  DISTSPEC's tokens PLUS (either may be empty); it
                                                  accepts every identical difference of NAME's pair
    nosource NAME reason                          NAME restates no in-process spec (why)

The texts (after the `abbrev`'s or `theorem`'s name) are compared as token lists: comments, `«name» ∷` Iris names and layout removed, brackets,
commas, `⌜⌝` and `∗` separate tokens. Every axiom of `Proof/**` (a part's `<Part>/Proof/**` too) whose
name has `_dist` needs a `pair` or `nosource` line. `--check` fails on an unlisted difference, an
axiom with no line, a line for an axiom that no longer exists, a missing file or spec, and a `dev`
line no difference matches (stale). `--show NAME` prints NAME's differences in the `dev` format.
An auth-on axiom (`*On_dist`) is paired with its in-process AUTH-ON contract, not the auth-off spec
of the same call: the auth-off spec claims facts the auth-on contract gives only with auth off (2026-11-27,
`KV_PutOn_dist`'s `kvRevLb`, paired with `kv.Put.spec`, went unseen; `notes/axiom-review/onrevlb-weakening.md`).
`--selftest` checks the gate on `etc/dist-axiom-diff-selftest/`: its listed pair passes, and it is
refused with a `dev` line removed (a dropped premise), with a stale `dev` line added, and with its
`pair` line removed; its theorem-sourced pair passes, and is refused with a conjunct the theorem
does not give added to the copy. Reads the sources only.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOW = ROOT / "etc" / "dist-axiom-diff-allow.txt"
SELFTEST = ROOT / "etc" / "dist-axiom-diff-selftest"
PROG = "dist-axiom-diff"

AXIOM = re.compile(r"^axiom\s+([A-Za-z_][A-Za-z0-9_'.]*_dist[A-Za-z0-9_'.]*)", re.M)
# where an `abbrev`'s body ends: the next top-level declaration, docstring or `end`
END = re.compile(r"^(?:/--|@\[|abbrev\s|def\s|theorem\s|lemma\s|axiom\s|instance\s|end\b|section\b|namespace\b|"
                 r"noncomputable\s|private\s|variable\s|open\s)", re.M)


def tokens(path: Path, name: str) -> list[str]:
    s = path.read_text(encoding="utf-8")
    m = re.search(rf"^(abbrev|theorem)\s+{re.escape(name)}(?=[\s\[(:])", s, re.M)
    if not m:
        raise LookupError(f"no `abbrev {name}` or `theorem {name}` in "
                          f"{path.relative_to(ROOT) if path.is_relative_to(ROOT) else path}")
    rest = s[m.end():]
    if m.group(1) == "theorem":
        # a proved theorem's statement: its binders and type, up to its proof (`:= by`, or `:=`)
        e = re.search(r":=\s*by\b", rest) or re.search(r":=", rest)
    else:
        e = END.search(rest)
    t = rest[:e.start()] if e else rest
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    t = re.sub(r'"[^"\s]*"\s*∷', " ", t)
    t = re.sub(r"([(){}\[\],⌜⌝∗])", r" \1 ", t)
    return t.split()


def hunks(a: list[str], b: list[str]) -> list[tuple[str, str]]:
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    return [(" ".join(a[i1:i2]), " ".join(b[j1:j2]))
            for op, i1, i2, j1, j2 in sm.get_opcodes() if op != "equal"]


def read_allow(lines: list[str]):
    pairs, devs, nosrc, bad = {}, {}, {}, []
    for ln, l in enumerate(lines, 1):
        l = l.rstrip("\n")
        if not l.strip() or l.lstrip().startswith("#"):
            continue
        w = l.split()
        if w[0] == "pair" and len(w) == 6:
            pairs[w[1]] = (w[2], w[3], w[4], w[5], ln)
        elif w[0] == "dev" and len(w) >= 2:
            m = re.match(r"dev\s+(\S+)\s+<<<(.*?)\|\|\|(.*?)>>>\s*(.*)$", l)
            if not m or not m.group(4).strip():
                bad.append(f"line {ln}: not `dev NAME <<< MINUS ||| PLUS >>> reason`")
                continue
            key = (" ".join(m.group(2).split()), " ".join(m.group(3).split()))
            devs.setdefault(m.group(1), {})[key] = ln
        elif w[0] == "nosource" and len(w) >= 3:
            nosrc[w[1]] = ln
        else:
            bad.append(f"line {ln}: not a `pair`, `dev` or `nosource` line: {l[:100]}")
    return pairs, devs, nosrc, bad


def dist_axioms(root: Path) -> dict[str, str]:
    # the sources on disk, not git's index: the gate also runs in a synced copy with no `.git` (the VM)
    files = sorted({str(p.relative_to(root)) for pat in ("Proof/**/*.lean", "*/Proof/**/*.lean")
                    for p in root.glob(pat)
                    if not p.relative_to(root).parts[0].startswith(".") and p.relative_to(root).parts[0] != "old"})
    out = {}
    for f in files:
        txt = (root / f).read_text(encoding="utf-8")
        if "_dist" not in txt:
            continue
        for m in AXIOM.finditer(txt):
            out[m.group(1)] = f
    return out


def judge(root: Path, lines: list[str], axioms: dict[str, str]):
    """(failures, report rows) for the allow file's `lines` against the `axioms` found."""
    pairs, devs, nosrc, fails = read_allow(lines)
    rows = []
    for n in sorted(axioms):
        if n not in pairs and n not in nosrc:
            fails.append(f"{n} ({axioms[n]}): no `pair` or `nosource` line")
    for n in sorted(set(pairs) | set(nosrc) | set(devs)):
        if n not in axioms:
            fails.append(f"{n}: a line names an axiom that no longer exists")
    for n, (df, ds, sf, ss, ln) in sorted(pairs.items()):
        try:
            h = hunks(tokens(root / sf, ss), tokens(root / df, ds))
        except (LookupError, OSError) as e:
            fails.append(f"{n} (line {ln}): {e}")
            continue
        mine = devs.get(n, {})
        used = set()
        unlisted = []
        for k in h:
            if k in mine:
                used.add(k)
            else:
                unlisted.append(k)
        for mi, pl in unlisted:
            fails.append(f"{n}: unlisted difference from {ss}: <<< {mi} ||| {pl} >>>")
        for k, l in sorted(mine.items(), key=lambda x: x[1]):
            if k not in used:
                fails.append(f"{n}: dev line {l} matches no difference (stale)")
        rows.append((n, ss, len(h), len(unlisted)))
    return fails, rows, nosrc


def run(root: Path, allow: Path, axioms=None):
    lines = allow.read_text(encoding="utf-8").splitlines() if allow.exists() else []
    return judge(root, lines, dist_axioms(root) if axioms is None else axioms)


def selftest() -> int:
    allow = (SELFTEST / "allow.txt").read_text(encoding="utf-8").splitlines()
    axioms = {"st_dist": "etc/dist-axiom-diff-selftest/Dist.lean",
              "st_nosrc_dist": "etc/dist-axiom-diff-selftest/Dist.lean",
              "st_on_dist": "etc/dist-axiom-diff-selftest/Dist.lean"}
    root = ROOT
    nfail = 0

    def case(name, lines, want_ok, why=None):
        nonlocal nfail
        f, _, _ = judge(root, lines, axioms)
        ok = (not f) == want_ok and (want_ok or why is None or any(why in x for x in f))
        print(f"  {'ok  ' if ok else 'FAIL'} {name}: {'passed' if not f else '; '.join(f)[:200]}")
        nfail += not ok

    case("the listed pair passes", allow, True)
    drop = [l for l in allow if "etcdURLsFit" not in l]
    assert len(drop) == len(allow) - 1, "the selftest's allow file lists one dropped-premise line"
    case("a dropped premise, unlisted, is refused", drop, False, "unlisted difference")
    case("a stale dev line is refused", allow + ["dev st_dist <<< foo ||| bar >>> nothing matches"], False,
         "stale")
    case("an axiom with no pair line is refused", [l for l in allow if not l.startswith("pair ")], False,
         "no `pair` or `nosource` line")
    case("a line for a removed axiom is refused", allow + ["nosource st_gone_dist gone"], False,
         "no longer exists")
    # (2026-11-27) a theorem-sourced pair (an auth-on contract with no spec, as `client.client_put_on`):
    # the listed copy passes (case 1); a copy claiming a conjunct the theorem does not give is refused
    bad = [l.replace(" st_on_dist.spec ", " st_onbad_dist.spec ") if l.startswith("pair st_on_dist ") else l
           for l in allow]
    case("a theorem-sourced pair's unbacked conjunct is refused", bad, False, "unlisted difference")
    print(f"{PROG} selftest: {nfail} failure(s)")
    return 1 if nfail else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--show", metavar="NAME")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.show:
        pairs, _, _, _ = read_allow(ALLOW.read_text(encoding="utf-8").splitlines())
        df, ds, sf, ss, _ = pairs[a.show]
        for mi, pl in hunks(tokens(ROOT / sf, ss), tokens(ROOT / df, ds)):
            print(f"dev {a.show} <<< {mi} ||| {pl} >>>")
        return 0
    fails, rows, nosrc = run(ROOT, ALLOW)
    for n, ss, nh, nu in rows:
        print(f"  {n}: {nh} difference(s) from {ss}, {nu} unlisted")
    for n in sorted(nosrc):
        print(f"  {n}: no in-process source (see its `nosource` line)")
    if fails:
        print(f"{PROG}: FAILED ({len(fails)})")
        for f in fails:
            print("  " + f)
        return 1 if a.check else 0
    print(f"{PROG}: ok ({len(rows)} interim axioms compared with their in-process specs, every "
          f"difference listed; {len(nosrc)} with no source)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
