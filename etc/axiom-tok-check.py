#!/usr/bin/env python3
"""The `axiom-tok` gate (per-type stage B: the Scope's §5.1; report-only from B0, enforcing from CP3).

Runs `etc/AxiomTokCheck.lean` (see its header for the rules and their approximations) over every
axiom of `.lake/tcb.json` (`etc/tcb-report.py`'s output), on each group of root modules
`etc/proof_roots.py` imports together, and prints each axiom's verdict and the list of axioms that
need an entry (rule 8), with the rule and the reason. Without `--check` it only reports (exit 0);
with `--check` it exits 1 when an axiom has a finding no entry of `--allow` accepts, a walk is
unknown (collapsed by the scenario cap, or truncated: a subterm the walk could not open), an entry
key matches no finding, an entry or pair names an axiom that no longer exists or was not walked,
or an axiom of the trust base is absent from the imported environments. Exit 2 on a usage error or
when a Lean run fails.

    etc/axiom-tok-check.py [--check] [--json TCB.json] [--raw OUT.jsonl] [--reuse-raw OUT.jsonl]
                           [--allow FILE] [--depth N] [--all] [-v]
    etc/axiom-tok-check.py --selftest [--reuse-raw MAIN.jsonl]

`--raw` keeps the Lean runs' output; `--reuse-raw` judges a kept output without running Lean.
`--selftest` elaborates `etc/axiom-tok-selftest/Selftest.lean` over a small import and checks each
toy axiom's verdict against its name (`st_refuse_*` refused, `st_pass_*` passed), the pairs of
`etc/axiom-tok-selftest/allow.txt`, `--check`'s failure on a stale entry, and (with `--reuse-raw`
of a main run) its `real-pass` lines; it exits 1 on any failure.

Never builds: the `.olean`s must be up to date (`lake build --no-build` is checked). `$LAKE_OPTS`
is passed to `lake`. Run it under a memory cap (`systemd-run --scope -p MemoryMax=64G`; a full
run's peak is reported in `etc/gates.sh`'s comment).
"""
import argparse
import collections
import json
import re
import os
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

PROG = "axiom-tok"
SELFTEST = os.path.join(ROOT, "etc", "axiom-tok-selftest", "Selftest.lean")
SELFTEST_ALLOW = os.path.join(ROOT, "etc", "axiom-tok-selftest", "allow.txt")
SELFTEST_MODULES = ["Spec.go_etcd_io.bbolt.DB__Begin_kv"]
DEFAULT_ALLOW = os.path.join(ROOT, "etc", "axiom-tok-allow.txt")


def lean_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    return env


def run_lean(argv, out):
    r = subprocess.run(proof_roots.lake("env", "lean", "--run", "etc/AxiomTokCheck.lean", *argv),
                       cwd=ROOT, env=lean_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       text=True, check=False)
    out.write(r.stdout)
    if r.returncode != 0:
        sys.stderr.write(r.stderr[-4000:])
        sys.exit(f"{PROG}: etc/AxiomTokCheck.lean exited {r.returncode} ({' '.join(argv[:3])} ...)")
    return [json.loads(l) for l in r.stdout.splitlines() if l.startswith("{")]


def olean_present(m, memo={}):
    """Whether `m`'s `.olean` exists in this build or a package's (for `--partial`)."""
    if m in memo:
        return memo[m]
    if m.split(".")[0] in ("Init", "Lean", "Std", "Lake"):
        return True
    parts = [p.strip("«»") for p in m.split(".")]
    dirs = [os.path.join(ROOT, ".lake", "build", "lib", "lean"),
            os.path.join(proof_roots._perennial_dir(), ".lake", "build", "lib", "lean")]
    for base in (os.path.join(ROOT, ".lake", "packages"),
                 os.path.join(proof_roots._perennial_dir(), ".lake", "packages")):
        if os.path.isdir(base):
            dirs += [os.path.join(base, d, ".lake", "build", "lib", "lean") for d in os.listdir(base)]
    memo[m] = any(os.path.exists(os.path.join(d, *parts) + ".olean") for d in dirs)
    return memo[m]


def closure_missing(m, memo={}):
    if m in memo:
        return memo[m]
    memo[m] = set()
    r = set() if olean_present(m) else {m}
    for i in proof_roots._imports(m):
        r |= closure_missing(i)
    memo[m] = r
    return r


def partial_modules(mods):
    """`mods` with each module whose import closure lacks an `.olean` replaced by the largest
    modules below it whose closure is complete; and the modules dropped."""
    out, dropped, seen = [], set(), set()
    todo = list(mods)
    while todo:
        m = todo.pop(0)
        if m in seen:
            continue
        seen.add(m)
        if not closure_missing(m):
            out.append(m)
        else:
            dropped.add(m)
            if olean_present(m) or True:
                todo += proof_roots._imports(m)
    # drop the ones another kept module imports anyway (fewer import roots, same environment)
    return sorted(set(out)), sorted(dropped)


def finding_key(f):
    """The key an entry names to accept the finding `f` (CP1a review M2 and its re-verification:
    entries are finding-specific, so an edit's new finding, or a changed count, is not silently
    accepted). No spaces. Rules 2 and 3 keep the counts and how they arise: `2:<level>:<counts>`,
    `3:<atom>:<counts>`, the counts being the finding's text after the subject with `/` for
    `, ` (`produced1/consumed0`; a persistent production is `produced∞`; a token handed to a
    callback is `handedtoacallback1/supplieddirectly0`), the atom without its `atom:` prefix and `#n` index;
    rule 5 `5:<opaque>` (short name); rule 7 `7:<binder>:<type>` (the `∃` binder and its type,
    spaces removed); rule 4 and notes `<rule>:<text>` (spaces removed)."""
    r, why = f["rule"], f["why"]

    def counts(t):
        return t.replace(", ", "/").replace(",", "/").replace(" ", "")

    if r == "2":
        m = re.match(r"level (\S+): (.*)$", why)
        if m:
            return f"2:{m.group(1)}:{counts(m.group(2))}"
        return f"2:{why.replace(' ', '')}"
    if r == "3":
        m = re.match(r"(.*?): (produced.*)$", why)
        atom, cnt = (m.group(1), m.group(2)) if m else (why, "")
        atom = re.sub(r"#\d+", "", atom)
        if atom.startswith("atom:"):
            atom = atom[5:]
        return f"3:{atom.replace(' ', '')}:{counts(cnt)}"
    if r == "5":
        return "5:" + short(why.rsplit(" ", 1)[-1])
    if r == "7":
        m = re.match(r"transfer of ∃ (\S+) : ", why)
        name = m.group(1) if m else "?"
        return f"7:{name}:{f.get('type', '').replace(' ', '')}"
    return f"{r}:{why.replace(' ', '')}"


def read_allow(path):
    """`entry NAME KEY[,KEY...] reason`: the axiom's findings with these keys (`finding_key`) are
    accepted; any other finding of it is still reported. `pair NAME PARTNER`, `real-pass NAME`,
    `trunc NAME` (the ratchet of truncated walks: NAME's walk truncates today, a known unknown that
    `--check` lets pass until it is decided; a new truncated walk fails, and so does a listed one
    that no longer truncates)."""
    entries, pairs, real_pass, truncs = {}, collections.defaultdict(set), [], set()
    if path and os.path.exists(path):
        for line in open(path, encoding="utf-8"):
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            w = line.split(None, 3)
            if w[0] == "entry":
                if len(w) < 3 or ":" not in w[2]:
                    sys.exit(f"{PROG}: {path}: an entry names the findings it accepts "
                             f"(entry NAME KEY[,KEY...] reason): {line[:120]}")
                e = entries.setdefault(w[1], {"keys": set(), "reason": ""})
                e["keys"] |= set(w[2].split(","))
                e["reason"] = (e["reason"] + " " + (w[3] if len(w) > 3 else "")).strip()
            elif w[0] == "pair" and len(w) >= 3:
                pairs[w[1]].add(w[2].split()[0])
            elif w[0] == "real-pass":
                real_pass.append(w[1])
            elif w[0] == "trunc":
                truncs.add(w[1])
    return entries, pairs, real_pass, truncs


def stale_axioms(allow, known):
    """The entry and pair lines naming an axiom not in `known` (one that no longer exists)."""
    return sorted(n for n in set(allow[0]) | set(allow[1]) | set(allow[3]) if n not in known)


def covered(name, f, entries):
    e = entries.get(name)
    return e is not None and finding_key(f) in e["keys"]


def retaint(axs, entries):
    """Rule 5 again, over every group at once and with the entries: an axiom with an entry does not
    taint what it produces (the Lean runs compute the taint per group, without the entries). The
    rule-5 findings are replaced; returns the tainted predicates. An axiom whose rule-2/3 findings
    all have entries (`covered`) does not taint by itself, but it still passes on a taint it receives,
and gets the rule-5 findings of it (which its entry does not name)."""
    def produced(o):
        # every scenario's (`opqProd`), not only the ones the output lists
        if "opqProd" in o:
            return set(o["opqProd"])
        return {k[4:] for s in o["scenarios"] for k in s["prod"] if k.startswith("opq:")}

    def fails(o, n=None):
        return any(f["rule"] in ("2", "3") and not (n and covered(n, f, entries))
                   for f in o["findings"])

    tainted, changed = set(), True
    while changed:
        changed = False
        for n, o in axs.items():
            if fails(o, n) or produced(o) & tainted:
                new = produced(o) - tainted
                if new:
                    tainted |= new
                    changed = True
    for n, o in axs.items():
        o["findings"] = [f for f in o["findings"] if f["rule"] != "5"]
        if not fails(o, n):
            o["findings"] += [{"rule": "5", "why": f"produces the tainted opaque {c}"}
                              for c in sorted(produced(o) & tainted)]
        o["ok"] = not o["findings"]
    return tainted


def judge(objs, allow, locs):
    """{name: verdict dict}, with pairs resolved; `objs` from one or more Lean runs."""
    entries, pairs = allow[0], allow[1]
    axs = {}
    for o in objs:
        if o["t"] != "ax":
            continue
        old = axs.get(o["name"])
        # the same name in several groups: keep the one with findings
        if old is None or (old["ok"] and not o["ok"]):
            axs[o["name"]] = o
    tainted = retaint(axs, entries)
    objs[:] = [o for o in objs if o["t"] != "tainted"] + [{"t": "tainted", "opq": c}
                                                         for c in sorted(tainted)]
    for name, o in axs.items():
        left, used = [], set()
        for f in o["findings"]:
            if covered(name, f, entries):
                used.add(finding_key(f))
                o.setdefault("accepted", []).append(f)
                continue
            if f["rule"] == "7":
                ok = any(f.get("type") in axs.get(p, {}).get("consumesTypes", [])
                         for p in pairs.get(name, ()))
                if ok:
                    f = dict(f, resolved="pair")
                    o.setdefault("resolved", []).append(f)
                    continue
            left.append(f)
        o["left"] = left
        # a truncation (a subterm the walk could not open: unknown), unless the axiom is in the
        # ratchet's list (`trunc NAME`)
        o["trunc_left"] = [] if name in allow[3] else list(o.get("trunc", []))
        e = entries.get(name)
        o["entry"] = e["reason"] if e else None
        # an entry key no finding has: the statement changed, or the walk did (review it)
        o["stale"] = sorted(e["keys"] - used) if e else []
        mod, line = locs.get(name, ("?", "?"))
        o["loc"] = f"{proof_roots.path_of(mod) if mod != '?' else '?'}:{line}"
    return axs


def short(n):
    for p in ("Perennial.EtcdGrove.", "Perennial."):
        if n.startswith(p):
            return n[len(p):]
    return n


def report(axs, objs, verbose, show_all):
    checked = len(axs)
    skipped = sum(o.get("n", 0) for o in objs if o["t"] == "skipped")
    need = {n: o for n, o in axs.items() if o["left"] and not o.get("capped")}
    capped = {n: o for n, o in axs.items() if o["left"] and o.get("capped")}
    stale = {n: o for n, o in axs.items() if o.get("stale")}
    trunc = {n: o for n, o in axs.items() if o["trunc_left"]}
    mints = {n: o for n, o in axs.items() if o.get("mint")}
    print(f"{PROG}: {checked} Prop axioms walked ({skipped} non-Prop axioms skipped: "
          f"types, values, opaque predicates)")
    print(f"{PROG}: {checked - len(need) - len(capped)} pass (or have an entry), {len(need)} "
          f"need an entry, {len(capped)} unknown (scenario cap: the walk merged its scenarios, so its "
          f"rule-3 counts are not reliable); {len(trunc)} unknown for a truncated subterm (see "
          f"'Truncations')")
    if stale:
        print("\nEntry keys that match no finding (the axiom or the walk changed; review the entry):")
        for n, o in sorted(stale.items()):
            print(f"    {short(n)}  {', '.join(o['stale'])}")
    if mints:
        print("\n*** TOKEN MINT CANDIDATES (produce tokens, consume none: a soundness finding unless "
              "the entry below explains it) ***")
        for n, o in sorted(mints.items()):
            print(f"  {short(n)}  {o['loc']}" + ("  (entry)" if not o["left"] else ""))
            for f in o["left"]:
                print(f"      rule {f['rule']}: {f['why'][:200]}")
    by_rule = collections.defaultdict(list)
    for n, o in sorted(need.items()):
        rules = sorted({f["rule"] for f in o["left"]})
        by_rule[",".join(rules)].append((n, o))
    print("\nAxioms that need an entry (rule 8), by rule:")
    for rules, lst in sorted(by_rule.items()):
        print(f"\n  rule {rules} ({len(lst)}):")
        for n, o in lst:
            print(f"    {short(n)}  {o['loc']}")
            for f in o["left"][:4]:
                print(f"        [{f['rule']}] {f['why'][:220]}")
            if len(o["left"]) > 4:
                print(f"        ... {len(o['left']) - 4} more")
    if capped:
        print(f"\nUnknown, scenario cap ({len(capped)}): too many branch combinations; collapsed to one "
              "worst-case scenario (rules 2/6 on tokens still meaningful, rule 3 not):")
        for n, o in sorted(capped.items()):
            toks = [f for f in o["left"] if f["rule"] == "2"]
            print(f"    {short(n)}  {o['loc']}  ({len(o['left'])} findings{', TOKEN: ' + toks[0]['why'] if toks else ''})")
    # rule 5's roots: the axioms failing rule 2 or 3 (with no entry for it) that produce a tainted predicate
    tainted_set = {o["opq"] for o in objs if o["t"] == "tainted"}
    roots = collections.defaultdict(set)
    for n, o in axs.items():
        if any(f["rule"] in ("2", "3") and f not in o.get("accepted", []) for f in o["findings"]):
            for sc in o["scenarios"]:
                for k in sc["prod"]:
                    if k.startswith("opq:") and k[4:] in tainted_set:
                        roots[k[4:]].add(short(n))
    if roots:
        print("\nRule 5's roots (the failing axioms that taint each predicate; the rule-5 entries above "
              "are their cascade):")
        for opq, ns in sorted(roots.items()):
            print(f"    {short(opq)}  <-  {', '.join(sorted(ns))}")
    holders = [o for o in objs if o["t"] == "holder"]
    tainted = sorted({o["opq"] for o in objs if o["t"] == "tainted"})
    unf = [o["inst"] for o in objs if o["t"] == "modelUnfold"]
    print(f"\nHolders (rule 6): {len(holders)}")
    for h in holders:
        print(f"    {short(h['opq'])} carries {h['carries']}")
    print(f"Tainted opaque predicates (rule 5): {len(tainted)}")
    for t in tainted:
        print(f"    {short(t)}")
    print(f"Model-only names with a FuncUnfold (m2): {len(unf)}")
    for u in unf:
        print(f"    {u}")
    if trunc:
        cnt = collections.Counter(t for o in trunc.values() for t in o["trunc_left"])
        print(f"\nTruncations (counted as nothing, so the walk is unknown; --check fails unless a `trunc` line lists the axiom):")
        for n, o in sorted(trunc.items()):
            print(f"    {short(n)}  {o['loc']}: {'; '.join(o['trunc_left'][:3])[:200]}")
        print("  by note:")
        for t, c in cnt.most_common(25):
            print(f"    {c:5}  {t[:160]}")
    if show_all:
        print("\nAll verdicts:")
        for n, o in sorted(axs.items()):
            v = ("entry" if o.get("accepted") else "ok") if not o["left"] else "NEEDS-ENTRY"
            print(f"  {v:11} {short(n)}  {o['loc']}")
            if verbose:
                for s in o["scenarios"][:3]:
                    print(f"      prod {s['prod']}  cons {s['cons']}  if {s['if']}")


def failures(axs, objs, allow, known, names):
    """What `--check` refuses, counted by kind; and the stale, unwalked and absent axioms.
    `known`: the axioms that exist (the names of the trust base); `names`: those to walk."""
    need = [n for n, o in axs.items() if o["left"] and not o.get("capped")]
    capped = [n for n, o in axs.items() if o["left"] and o.get("capped")]
    stale = [n for n, o in axs.items() if o.get("stale")]
    trunc = [n for n, o in axs.items() if o["trunc_left"]]
    gone = stale_axioms(allow, known)
    unwalked = sorted(n for n in set(allow[0]) | set(allow[1]) | set(allow[3])
                      if n in known and n not in axs)
    trunc_stale = sorted(n for n in allow[3] if n in axs and not axs[n].get("trunc"))
    present = set()
    for o in objs:
        if o["t"] == "present":
            present.update(o["names"])
    absent = [n for n in dict.fromkeys(names) if n not in present]
    bad = {"need an entry": len(need), "unknown (scenario cap)": len(capped),
           "unknown (truncated)": len(trunc), "with stale entry keys": len(stale),
           "stale entries (axiom gone)": len(gone), "entries for unwalked axioms": len(unwalked),
           "absent from the environments": len(absent),
           "trunc lines for walks that no longer truncate": len(trunc_stale)}
    for n in trunc_stale:
        print(f"    trunc line stale (the walk no longer truncates; remove it): {short(n)}")
    return bad, gone, unwalked, absent


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--json", default=os.path.join(ROOT, ".lake", "tcb.json"))
    ap.add_argument("--raw")
    ap.add_argument("--reuse-raw")
    ap.add_argument("--allow", default=DEFAULT_ALLOW)
    ap.add_argument("--depth", type=int)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 on a finding with no entry, an unknown walk or a stale entry")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--partial", action="store_true",
                    help="no build check; a root whose imports lack an .olean is replaced by the "
                         "complete modules below it (report which)")
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    extra = [f"--depth={a.depth}"] if a.depth else []

    if a.selftest:
        return selftest(a, extra)

    locs = {}
    names = []
    with open(a.json, encoding="utf-8") as f:
        for line in f:
            o = json.loads(line)
            if o.get("t") == "axiom":
                names.append(o["name"])
                locs[o["name"]] = (o.get("module", "?"), o.get("line", "?"))
    if a.reuse_raw:
        objs = [json.loads(l) for l in open(a.reuse_raw) if l.startswith("{")]
    else:
        if not a.partial:
            proof_roots.check_built(PROG, lean_env())
        objs = []
        raw = open(a.raw, "w") if a.raw else open(os.devnull, "w")
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False,
                                         dir=os.environ.get("TMPDIR")) as nf:
            nf.write("\n".join(names) + "\n")
            nfile = nf.name
        try:
            for mods in proof_roots.lean_runs():
                if a.partial:
                    roots = [m for m in mods if closure_missing(m)]
                    mods, dropped = partial_modules(mods)
                    for r in roots:
                        print(f"{PROG}: --partial: root {r} not importable (missing: "
                              f"{', '.join(sorted(closure_missing(r))[:4])}...)", file=sys.stderr)
                    print(f"{PROG}: --partial: {len(dropped)} modules dropped, importing "
                          f"{len(mods)}", file=sys.stderr)
                print(f"{PROG}: running on {len(mods)} root modules ({mods[0]}, ...)", file=sys.stderr)
                objs += run_lean([f"--axioms={nfile}", *extra, *proof_roots.lean_args(), *mods], raw)
        finally:
            os.unlink(nfile)
            raw.close()
    allow = read_allow(a.allow)
    axs = judge(objs, allow, locs)
    report(axs, objs, a.v, a.all)
    bad, gone, unwalked, absent = failures(axs, objs, allow, locs, names)
    if gone:
        print(f"\nStale entries: {len(gone)} entry or pair line(s) name an axiom that no longer "
              f"exists (not in {os.path.relpath(a.json)}); remove or rename them:")
        for n in gone:
            print(f"    {short(n)}")
    if unwalked:
        print(f"\nEntries for axioms not walked in this run (in modules not imported): {len(unwalked)}")
        for n in unwalked:
            print(f"    {short(n)}")
    print(f"\n{PROG}: {len(set(names))} axioms in {os.path.relpath(a.json)}; "
          f"{len(set(names)) - len(absent)} found in the imported environments; "
          f"{len(absent)} absent (in modules not imported)")
    for n in absent[:60]:
        mod, line = locs.get(n, ("?", "?"))
        print(f"    absent: {short(n)}  {proof_roots.path_of(mod) if mod != '?' else '?'}:{line}")
    nbad = sum(bad.values())
    if a.check:
        if nbad:
            print(f"\n{PROG}: FAILED: " + ", ".join(f"{v} {k}" for k, v in bad.items() if v))
            return 1
        print(f"\n{PROG}: ok ({len(axs)} Prop axioms walked: "
              f"{sum(1 for o in axs.values() if not o.get('accepted') and not o.get('resolved'))} pass, "
              f"{sum(1 for o in axs.values() if o.get('accepted') or o.get('resolved'))} by an entry or pair)")
    else:
        print(f"\n{PROG}: report-only (--check would " + ("fail: " + ", ".join(f"{v} {k}" for k, v in bad.items() if v) if nbad else "pass") + ")")
    return 0


def selftest(a, extra):
    with tempfile.TemporaryFile("w+") as raw:
        objs = run_lean([f"--selftest={SELFTEST}", *extra, *SELFTEST_MODULES], raw)
    errs = [o for o in objs if o["t"] == "elab-error"]
    for e in errs:
        print(f"{PROG} selftest: elaboration error: {e['msg'][:300]}")
    allow = read_allow(SELFTEST_ALLOW)
    axs = judge(objs, allow, {})
    unf = {o["inst"].split(":")[0] for o in objs if o["t"] == "modelUnfold"}
    fails = len(errs)
    for n, o in sorted(axs.items()):
        s = n.split(".")[-1]
        refused = bool(o["left"]) or n in unf
        if s.startswith("st_refuse_"):
            ok = refused
        elif s.startswith("st_pass_"):
            ok = not refused
        else:
            continue
        why = "; ".join(f"[{f['rule']}] {f['why'][:100]}" for f in o["left"]) or \
            ("modelUnfold" if n in unf else "")
        res = " (pair resolved)" if o.get("resolved") else ""
        print(f"  {'ok  ' if ok else 'FAIL'} {s:28} {'refused' if refused else 'passed'}{res}  {why}")
        fails += not ok
    # an entry naming an axiom that does not exist is reported stale: `st_gone` must be, and only it
    gone = stale_axioms(allow, axs)
    ok = gone == ["AxiomTokSelftest.st_gone"]
    print(f"  {'ok  ' if ok else 'FAIL'} stale entries {', '.join(gone) or '(none)'}")
    fails += not ok
    # `--check`: refuses the whole selftest run (refused toys, the stale `st_gone`), and passes on
    # the `st_pass_*` toys alone with the entries naming them
    names = list(axs)
    bad, _, _, _ = failures(axs, objs, allow, set(names), names)
    ok = bad["need an entry"] > 0 and bad["stale entries (axiom gone)"] == 1
    print(f"  {'ok  ' if ok else 'FAIL'} --check refuses the toys: "
          + ", ".join(f"{v} {k}" for k, v in bad.items() if v))
    fails += not ok
    keep = lambda n: n.split(".")[-1].startswith(("st_pass_", "st_partner_"))
    sub_allow = ({n: e for n, e in allow[0].items() if keep(n)},
                 {n: p for n, p in allow[1].items() if keep(n)}, [], set())
    sub_objs = [o for o in objs if o["t"] != "ax" or keep(o["name"])]
    sub = judge(sub_objs, sub_allow, {})
    sub = {n: o for n, o in sub.items() if keep(n)}
    sub_names = [n for n in sub if n not in unf]
    sub = {n: sub[n] for n in sub_names}
    bad, _, _, _ = failures(sub, [{"t": "present", "names": sub_names}], sub_allow,
                            set(sub_names), sub_names)
    ok = not sum(bad.values())
    print(f"  {'ok  ' if ok else 'FAIL'} --check passes the st_pass_* toys"
          + ("" if ok else ": " + ", ".join(f"{v} {k}" for k, v in bad.items() if v)))
    fails += not ok
    if allow[2]:
        if a.reuse_raw:
            main_objs = [json.loads(l) for l in open(a.reuse_raw) if l.startswith("{")]
            maxs = judge(main_objs, read_allow(a.allow), {})
            for n in allow[2]:
                o = maxs.get(n)
                ok = o is not None and not o["left"]
                why = "absent from the run" if o is None else \
                    "; ".join(f"[{f['rule']}] {f['why'][:100]}" for f in o["left"])
                print(f"  {'ok  ' if ok else 'FAIL'} real-pass {short(n)}  {why}")
                fails += not ok
        else:
            print(f"  (real-pass lines not checked: pass --reuse-raw MAIN.jsonl)")
    print(f"{PROG} selftest: {fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
