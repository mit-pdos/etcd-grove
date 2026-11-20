#!/usr/bin/env python3
"""The client port's access-control table, checked (notes/auth-mediation-scope.md, stage M0).

    etc/auth-mediation-check.py                  check the table against the registrations and the specs
    etc/auth-mediation-check.py --check          ... and against the baseline (no row weaker, none missing)
    etc/auth-mediation-check.py --check --update ... and record the rows that got stronger
    etc/auth-mediation-check.py --regs FILE      read the registrations from FILE instead of running etc/authmed

The registrations: `etc/authmed` (etc/authmed/main.go) lists every gRPC method, hook and HTTP path
registered on etcd's client port, from the Go source of project `etcd` of etc/goose.py at its pinned
revision (`.lake/goose/etcd`, which `etc/goose.py` clones; cloned here if absent) and of grpc at the
version etcd's server module requires (Go's module cache; `go mod download` if absent).

The table, `etc/auth-table.txt` (its header gives the format): one row per registration, with its
class, status, the specs that carry it and the guard vocabulary they must mention. Fails when:

  - a registration has no row, or a row no registration;
  - a row names a spec file that does not exist or declares no `<F>.spec`, or whose proof is not a
    `theorem <F>.wp_proof` without `sorry`, or is not applied by a linking module (`Link.lean`,
    `Results.lean`, `*Linked.lean`; for the statuses that
    claim a proof: e2e, e2e-apply, contract, server, guard, public);
  - a row of status e2e, e2e-apply, contract or server names fewer than two specs (the guard's and
    the handler's: a guard alone is status guard);
  - a row's vocabulary word occurs in none of its specs' text (comments stripped);
  - a row of status none or excluded gives no reason, or a reason naming an issues/, nonissues/ or
    notes/ file that does not exist;
  - when `.lake/tcb.json` is current (as `etc/tcb-report.py --reuse` takes it), a `sorry` it lists is
    declared in one of the rows' proof modules;
  - (--check) a row is weaker than in `etc/auth-mediation-baseline.txt`, or a baseline row is gone.

What it does not do: decide that a spec's post means "no effect without the check" (the vocabulary
test is syntactic; each row's meaning is reviewed once, and the gate keeps it there).
"""
import argparse
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "etc"))

TABLE = os.path.join(ROOT, "etc", "auth-table.txt")
BASELINE = os.path.join(ROOT, "etc", "auth-mediation-baseline.txt")
ABBREV = {
    "S/": "go_etcd_io/etcd/server/v3/etcdserver/",
    "R/": "go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/",
    "A/": "go_etcd_io/etcd/server/v3/etcdserver/apply/",
}
CLASSES = {"public", "authenticated", "rbac", "admin", "mixed", "-"}
# the statuses, weakest first (public: no check is required, ranked with e2e)
RANK = {"excluded": 0, "none": 1, "guard": 2, "server": 3, "contract": 4, "e2e-apply": 5,
        "e2e": 6, "public": 6}
PROVED = {"e2e", "e2e-apply", "contract", "server", "guard", "public"}
NEEDS_SPEC = {"e2e", "e2e-apply", "contract", "server", "guard"}
NEEDS_WHY = {"none", "excluded"}


def strip_comments(t):
    t = re.sub(r"/-.*?-/", "", t, flags=re.S)
    return re.sub(r"--[^\n]*", "", t)


def read_table():
    rows, errs = {}, []
    with open(TABLE) as f:
        for n, line in enumerate(f, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = line.split(None, 5)
            if len(parts) < 5:
                errs.append(f"{TABLE}:{n}: fewer than 5 fields")
                continue
            key, cls, status, specs, vocab = parts[:5]
            why = parts[5] if len(parts) > 5 else "-"
            if key in rows:
                errs.append(f"{TABLE}:{n}: duplicate row {key}")
            if cls not in CLASSES:
                errs.append(f"{TABLE}:{n}: unknown class {cls}")
            if status not in RANK:
                errs.append(f"{TABLE}:{n}: unknown status {status}")
            rows[key] = dict(line=n, cls=cls, status=status,
                             specs=[] if specs == "-" else specs.split(","),
                             vocab=[] if vocab == "-" else vocab.split(","), why=why)
    return rows, errs


def etcd_src():
    """project `etcd` of etc/goose.py at its pin, where etc/goose.py keeps it (fetched if needed)."""
    import goose
    proj = next(p for p in goose.PROJECTS if p.name == "etcd")
    return goose.checkout(proj.repo, proj.rev, os.path.join(goose.WORK, "etcd"))


def go_env():
    env = dict(os.environ)
    env["PATH"] = "/usr/local/go/bin:" + os.path.expanduser("~/go/bin") + ":" + env.get("PATH", "")
    env.setdefault("GOTOOLCHAIN", "go1.27.1")
    env["GOWORK"] = "off"
    env["GOFLAGS"] = "-mod=mod"
    return env


def grpc_src(etcd, env):
    """grpc's source at the version etcd's server module requires (Go's module cache)."""
    ver = None
    with open(os.path.join(etcd, "server", "go.mod")) as f:
        for line in f:
            m = re.match(r"\s*google\.golang\.org/grpc\s+(v\S+)", line)
            if m:
                ver = m.group(1)
    if ver is None:
        sys.exit("auth-mediation: no google.golang.org/grpc in server/go.mod")
    cache = subprocess.run(["go", "env", "GOMODCACHE"], capture_output=True, text=True,
                           env=env).stdout.strip()
    d = os.path.join(cache, "google.golang.org", f"grpc@{ver}")
    if not os.path.isdir(d):
        subprocess.run(["go", "mod", "download", f"google.golang.org/grpc@{ver}"],
                       cwd=os.path.join(ROOT, "etc", "authmed"), env=env, check=True)
    return d


def registrations(regs_file):
    if regs_file:
        text = open(regs_file).read()
    else:
        env = go_env()
        etcd = etcd_src()
        grpc = grpc_src(etcd, env)
        bindir = os.path.join(ROOT, ".lake", "goose", "bin")
        os.makedirs(bindir, exist_ok=True)
        exe = os.path.join(bindir, "authmed")
        subprocess.run(["go", "build", "-o", exe, "."], cwd=os.path.join(ROOT, "etc", "authmed"),
                       env=env, check=True)
        r = subprocess.run([exe, etcd, grpc], capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"auth-mediation: etc/authmed failed:\n{r.stderr}")
        text = r.stdout
    regs = {}
    for line in text.splitlines():
        kind, rest = line.split(" ", 1)
        if kind == "grpc":
            origin, name, _ = rest.split(" ")
            regs[name] = f"{origin} ({line.rsplit(' ', 1)[1]})"
        else:
            origin, what = rest.split(" ", 1)
            regs[f"{kind}:{origin}:{what}"] = origin
    return regs


def spec_path(s):
    for a, full in ABBREV.items():
        if s.startswith(a):
            s = full + s[len(a):]
    return s


_links = None


def links_text():
    global _links
    if _links is None:
        parts = []
        for dp, dns, fns in os.walk(ROOT):
            dns[:] = [d for d in dns if d not in (".lake", ".git", "old", "SpecPlan", "interface")]
            for fn in fns:
                if fn in ("Link.lean", "Results.lean") or fn.endswith("Linked.lean"):
                    parts.append(strip_comments(open(os.path.join(dp, fn)).read()))
        _links = "\n".join(parts)
    return _links


def check_spec(key, s, need_proof):
    """The spec file's text (comments stripped), the proof module's name, and the errors."""
    errs = []
    rel = spec_path(s)
    sf = os.path.join(ROOT, "Spec", rel + ".lean")
    if not os.path.isfile(sf):
        return "", None, [f"{key}: no spec file Spec/{rel}.lean"]
    text = strip_comments(open(sf).read())
    m = re.search(r"\b(?:abbrev|def)\s+(\S+)\.spec\b", text)
    if not m:
        return text, None, [f"{key}: Spec/{rel}.lean declares no `<F>.spec`"]
    name = m.group(1)
    pf = os.path.join(ROOT, "Proof", rel + ".lean")
    pmod = "Proof." + rel.replace("/", ".")
    if need_proof:
        if not os.path.isfile(pf):
            errs.append(f"{key}: no proof file Proof/{rel}.lean")
        else:
            pt = strip_comments(open(pf).read())
            if not re.search(r"\btheorem\s+" + re.escape(name) + r"\.wp_proof\b", pt):
                errs.append(f"{key}: Proof/{rel}.lean has no `theorem {name}.wp_proof`")
            if re.search(r"\bsorry\b", pt):
                errs.append(f"{key}: Proof/{rel}.lean has a `sorry`")
            if not re.search(r"\b" + re.escape(name) + r"\.wp_proof\b", links_text()):
                errs.append(f"{key}: no Link.lean (or Results.lean, *Linked.lean) applies {name}.wp_proof")
    return text, pmod, errs


def tcb_sorry_modules():
    """The modules of the `sorry`s of `.lake/tcb.json`, or None when it is not current."""
    j = os.path.join(ROOT, ".lake", "tcb.json")
    if not os.path.isfile(j):
        return None
    import proof_roots
    mods = set()
    with open(j) as f:
        first = json.loads(f.readline())
        if first.get("t") != "meta" or first.get("modules") != proof_roots.root_modules():
            return None
        for line in f:
            o = json.loads(line)
            if o.get("t") == "sorry":
                mods.add(o.get("module"))
    return mods


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--regs")
    args = ap.parse_args()

    rows, errs = read_table()
    regs = registrations(args.regs)
    for k in sorted(regs):
        if k not in rows:
            errs.append(f"{k}: registered ({regs[k]}) but has no row in etc/auth-table.txt")
    for k in sorted(rows):
        if k not in regs:
            errs.append(f"{k}: a row of etc/auth-table.txt (line {rows[k]['line']}) but not registered")

    proof_mods = set()
    for k, r in rows.items():
        st = r["status"]
        if st in NEEDS_SPEC and not r["specs"]:
            errs.append(f"{k}: status {st} names no spec")
        if st in NEEDS_SPEC - {"guard"} and len(r["specs"]) < 2:
            errs.append(f"{k}: status {st} names fewer than two specs (the guard's and the handler's)")
        if st in NEEDS_WHY and r["why"] in ("", "-"):
            errs.append(f"{k}: status {st} gives no reason")
        for f in re.findall(r"\b((?:issues|nonissues|notes)/[\w./-]+\.md)", r["why"]):
            if not os.path.isfile(os.path.join(ROOT, f)):
                errs.append(f"{k}: names {f}, which does not exist")
        texts = []
        for s in r["specs"]:
            text, pmod, e = check_spec(k, s, st in PROVED)
            errs += e
            texts.append(text)
            if pmod and st in PROVED:
                proof_mods.add(pmod)
        for w in r["vocab"]:
            if not any(re.search(r"(?<![\w.])(?:[\w]+\.)*" + re.escape(w) + r"(?![\w])", t)
                       for t in texts):
                errs.append(f"{k}: `{w}` occurs in none of its specs")

    sm = tcb_sorry_modules()
    if sm is None:
        tcb_note = "tcb.json half skipped (.lake/tcb.json absent or not of the current roots)"
    else:
        for m in sorted(sm & proof_mods):
            errs.append(f"a sorry of .lake/tcb.json is declared in {m}")
        tcb_note = "tcb.json half checked"

    stronger = []
    if args.check:
        base = {}
        if os.path.isfile(BASELINE):
            for line in open(BASELINE):
                line = line.strip()
                if line and not line.startswith("#"):
                    k, st = line.split()
                    base[k] = st
        for k, st in base.items():
            if k not in rows:
                errs.append(f"{k}: in the baseline ({st}) but has no row")
            elif RANK[rows[k]["status"]] < RANK[st]:
                errs.append(f"{k}: status {rows[k]['status']}, weaker than the baseline's {st}")
        for k, r in rows.items():
            if k not in base or RANK[r["status"]] > RANK[base[k]] or \
                    (RANK[r["status"]] == RANK[base[k]] and r["status"] != base[k]):
                stronger.append(k)
        if args.update and not errs:
            with open(BASELINE, "w") as f:
                f.write("# etc/auth-mediation-check.py --check --update: each row's status in "
                        "etc/auth-table.txt (shrink-only: a row may only get stronger)\n")
                for k in sorted(rows):
                    f.write(f"{k} {rows[k]['status']}\n")

    if errs:
        for e in errs:
            print(f"auth-mediation: {e}")
        print(f"auth-mediation: FAILED ({len(errs)} problems)")
        return 1
    counts = {}
    for r in rows.values():
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    summary = ", ".join(f"{s} {counts[s]}" for s in sorted(counts, key=lambda s: -RANK[s]))
    if stronger and args.check and not args.update:
        print(f"auth-mediation: {len(stronger)} rows stronger than the baseline "
              f"(record with --check --update): {', '.join(stronger[:5])}")
    if args.update and stronger:
        print(f"auth-mediation: baseline updated ({len(stronger)} rows)")
    print(f"auth-mediation: ok ({len(rows)} rows: {summary}; {tcb_note})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
