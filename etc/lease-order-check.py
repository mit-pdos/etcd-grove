#!/usr/bin/env python3
"""The lease axioms' ordering gate (#50 F2/F7; `notes/axiom-review/f7-combined.md`, section 3, "Caveat").

Six interim lease axioms of the no-crash line read the view's lessor name `Γ.ls mid`:
`Lease_Grant_dist`, `Lease_GrantLive_dist`, `Lease_LeasesGranted_dist`, `Lease_LeasesLive_dist`,
`Client_LeaseTimeToLive_dist`, `Client_LeaseLeases_dist`. They are sound only while every axiom that
serves etcd's table at a view `Γ` for a member `mid` ties that member's lessor to `Γ.ls mid` (P-L1: the
proposed `Serve_dist`, whose member resources `memberUpL`/`memberUpOnL` say `mvccLeases E.γ = Γ.ls mid`).
Beside a serve axiom without the tie (the `Serve_dist` of before P-L1, `memberUp`), a start owning
`Γ.ls mid`'s names and a real Grant refute them (the review's attack). So:

  a serve axiom of etcd's table that does not tie `Γ.ls` must not coexist with a linked use of the six.

The check (source text only, no build): every `axiom ... .wp_proof` whose `.spec` names `etcdAddrAt`
in a precondition together with `etcdstart.memberUp`/`memberUpOn` (a serve axiom) must mention
`Γ.ls mid` in that spec; if one does not, no module of the repository may import (directly or not) a
module declaring one of the six axioms. "Reaches" is by import: the six are axioms that no proof
imports, only a `Link` would (their users take their specs as hypotheses), so an import is a link.

usage: etc/lease-order-check.py [-v]       exit 1 on a violation
       etc/lease-order-check.py --selftest checks that the rule fires on a synthetic violation
"""
from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKIP_DIRS = {".lake", ".claude", ".git", "old", "examples", "third_party", "notes", "issues",
             "nonissues", "interface", "etc"}
LEASE_AXIOMS = ["Lease_Grant_dist", "Lease_GrantLive_dist", "Lease_LeasesGranted_dist",
                "Lease_LeasesLive_dist", "Client_LeaseTimeToLive_dist", "Client_LeaseLeases_dist"]
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)
AXIOM = re.compile(r"^\s*axiom\s+(\S+)\.wp_proof\b", re.M)
SPEC = r"^\s*(?:abbrev|def)\s+{name}\.spec\b(.*?)(?=^\s*(?:abbrev|def|theorem|axiom|end|section|/--)\b)"


def load():
    mods = {}
    for dirpath, dirs, files in os.walk(ROOT):
        if os.path.relpath(dirpath, ROOT) == ".":
            dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                with open(p, errors="replace") as fh:
                    mods[m] = COMMENT.sub("", fh.read())
    return mods


def spec_text(mods, name):
    pat = re.compile(SPEC.format(name=re.escape(name)), re.M | re.S)
    for text in mods.get("__addr__", ()):
        if f"{name}.spec" not in text:
            continue
        m = pat.search(text)
        if m:
            return m.group(1)
    return None


def check(mods, verbose=False):
    errs = []
    mods = dict(mods)
    mods["__addr__"] = [t for t in mods.values() if "etcdAddrAt" in t]
    axiom_mod = {}   # lease axiom -> its module
    serve = []       # (axiom, module, tied?)
    for mod, text in mods.items():
        if mod == "__addr__":
            continue
        for ax in AXIOM.findall(text):
            short = ax.split(".")[-1]
            if short in LEASE_AXIOMS:
                axiom_mod[short] = mod
                continue
            spec = spec_text(mods, ax.split(".")[-1])
            if spec and "etcdAddrAt" in spec and re.search(r"memberUp(On)?\b", spec):
                serve.append((ax, mod, "Γ.ls mid" in spec))
    untied = [(a, m) for a, m, t in serve if not t]
    if verbose:
        for a, m, t in serve:
            print(f"  serve axiom {a} ({m}): {'ties' if t else 'does NOT tie'} Γ.ls")
        for a in LEASE_AXIOMS:
            print(f"  lease axiom {a}: {axiom_mod.get(a, '(not found)')}")
    if not untied:
        return errs
    imports = {m: set(IMPORT.findall(t)) for m, t in mods.items() if m != "__addr__"}
    targets = set(axiom_mod.values())
    reach = {}

    def reaches(m, seen):
        if m in reach:
            return reach[m]
        if m in seen:
            return False
        seen.add(m)
        r = any(i in targets or reaches(i, seen) for i in imports.get(m, ()) if i in imports)
        reach[m] = r
        return r

    for m in sorted(imports):
        if m not in targets and reaches(m, set()):
            errs.append(m)
    if errs:
        print("lease-order: FAILED: a serve axiom without the Γ.ls tie ("
              + ", ".join(a for a, _ in untied) + ") coexists with linked lease axioms; importers:")
        for m in errs:
            print(f"  {m}")
    return errs


def main():
    if "--selftest" in sys.argv:
        mods = {
            "Spec.S": "abbrev Serve_x.spec : Prop := etcdAddrAt a Γ mid ∗ etcdstart.memberUp s\nend spec",
            "Proof.S": "axiom Serve_x.wp_proof : Serve_x.spec",
            "Proof.L": "axiom Lease_Grant_dist.wp_proof : Lease_Grant_dist.spec",
            "Proof.Link": "public import Proof.L",
        }
        bad = check(mods)
        mods["Spec.S"] = mods["Spec.S"].replace("memberUp s", "memberUpL s (Γ.ls mid)")
        good = check(mods)
        ok = bad == ["Proof.Link"] and good == []
        print("lease-order selftest:", "ok" if ok else "FAILED")
        return 0 if ok else 1
    mods = load()
    errs = check(mods, "-v" in sys.argv)
    if errs:
        return 1
    print("lease-order: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
