#!/usr/bin/env python3
"""Re-derive the plan's inventory (notes/bbolt-port-plan.md, section 1) from an extracted tree.

Usage: inventory.py ROOT   (ROOT holds Proof/go_etcd_io/bbolt and Spec/go_etcd_io/bbolt of origin/lean,
e.g. `git archive origin/lean Proof/go_etcd_io/bbolt Spec/go_etcd_io/bbolt | tar -x -C ROOT`)

Classifies every .lean file by what of the v1 OS layer it mentions:
  resource: a file resource or its fields (osMeta, osBytes, osSlot, osFd, OsMeta, osGrown, pwBytes, ...)
  byname:   an os/syscall/unix spec or module by name, no resource
  variable: only the section variable / osN / osInv
  none
and prints counts, the resource files, and the occurrence counts of each pattern.
"""
import os
import re
import sys

root = sys.argv[1]
RES = ["osMeta", "osBytes", "osSlot", "osFd", "OsMeta", "OsFd", "osGrown", "pwBytes", "pwSize",
       "MapsBelow", "openMeta", "syncedBytes", "osTree", "osFile", "WriteChunks", "CrashFile",
       "osBytes_halves", "fmtErrorOk", "IsPointerError", r"\.maps\b"]
NAME = [r"\bos\.[A-Z]\w*\.spec", r"\bsyscall\.\w+\.spec", r"\bunix\.\w+\.spec", r"Spec\.os\.",
        r"Proof\.os\.", r"Spec\.syscall\.", r"Proof\.syscall\.", r"golang_org\.x\.sys", r"wp_os",
        r"\bos\.\w+\.wp_proof"]
VAR = [r"osFsExt", r"\bosN\b", r"\bosInv\b", r"GooseLang\.Ext\.OsFs"]

def has(pats, s):
    return [p for p in pats if re.search(p, s)]

counts = {}
cls = {"resource": [], "byname": [], "variable": [], "none": []}
lines = {}
for d, _, fs in os.walk(root):
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        s = open(p, encoding="utf-8").read()
        rel = os.path.relpath(p, root)
        lines[rel] = s.count("\n")
        for pat in RES + NAME + VAR:
            counts[pat] = counts.get(pat, 0) + len(re.findall(pat, s))
        if has(RES, s):
            cls["resource"].append((rel, has(RES, s)))
        elif has(NAME, s):
            cls["byname"].append((rel, has(NAME, s)))
        elif has(VAR, s):
            cls["variable"].append((rel, has(VAR, s)))
        else:
            cls["none"].append((rel, []))

total = sum(len(v) for v in cls.values())
print(f"files: {total}")
for k, v in cls.items():
    print(f"{k}: {len(v)} files, {sum(lines[r] for r, _ in v)} lines")
print("\n== resource files")
for r, pats in sorted(cls["resource"]):
    print(f"{lines[r]:6d} {r}  [{', '.join(pats)}]")
print("\n== byname files")
for r, pats in sorted(cls["byname"]):
    print(f"{lines[r]:6d} {r}  [{', '.join(pats)}]")
print("\n== occurrences")
for pat in RES + NAME + VAR:
    print(f"{counts[pat]:6d} {pat}")
