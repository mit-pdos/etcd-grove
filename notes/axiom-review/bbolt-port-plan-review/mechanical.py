#!/usr/bin/env python3
"""Check the plan's "mechanical" class: among the files that mention only the section variable
(`osFsExt`, `osN`, `osInv`, the OsFs imports) and no file resource, count those that still name what
the port changes indirectly: the context's file path `K.p`, `fileHolds`, a `(p : GoString)` binder
(the file's path, which becomes an inode), `osInv`/`osN` uses in proofs.

Usage: mechanical.py ROOT   (ROOT as for inventory.py)
"""
import os
import re
import sys

root = sys.argv[1]
RES = re.compile(r"osMeta|osBytes|osSlot|osFd|OsMeta|OsFd|osGrown|pwBytes|pwSize|openMeta|fmtErrorOk|"
                 r"IsPointerError|\.maps\b|CrashFile|WriteChunks")
VAR = re.compile(r"osFsExt|\bosN\b|\bosInv\b|GooseLang\.Ext\.OsFs")
PATS = {
    "K.p": re.compile(r"\bK\.p\b"),
    "fileHolds": re.compile(r"fileHolds"),
    "(p : GoString)": re.compile(r"\(p : GoString\)"),
    "osInv": re.compile(r"\bosInv\b"),
    "osN": re.compile(r"\bosN\b"),
}
n = 0
hits = {k: [] for k in PATS}
for d, _, fs in os.walk(root):
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        s = open(p, encoding="utf-8").read()
        if RES.search(s) or not VAR.search(s):
            continue
        n += 1
        for k, r in PATS.items():
            c = len(r.findall(s))
            if c:
                hits[k].append((c, os.path.relpath(p, root)))
print(f"variable-only files: {n}")
for k, v in hits.items():
    v.sort(reverse=True)
    print(f"{k}: {len(v)} files, {sum(c for c, _ in v)} occurrences; top: " +
          ", ".join(f"{r} ({c})" for c, r in v[:8]))
