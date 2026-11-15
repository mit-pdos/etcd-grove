#!/usr/bin/env python3
"""The mechanical part of porting real bbolt from the v1 file extension (`GooseLang/Ext/OsFs`) to
the per-byte one (`GooseLang/Ext/Fs`), `notes/bbolt-port-plan.md` §1(a), §5.6: the section
variable and instance binders `HasExt osFsExt` become the per-byte clients' `[ExtSemantics fsExt]
[FsSemOk] [HasExt fsExt]`, imports of `GooseLang.Ext.OsFs.*` become `GooseLang.Ext.Fs.*`, and
`open Fs` is added after the first `namespace bbolt` (the new extension's names live in
`Perennial.Fs`). It does not rename file names (`p : GoString` to `i : Ino`) or change resource
shapes (`osMeta p q (some m)` to `osMeta i q m`): those are by hand (§1(a'), §1(c)).

Usage: etc/fs-port/bbolt-rename.py FILE...  (rewrites in place; prints the lines that still
mention the v1 extension)."""
import re
import sys


def port(s):
    s = s.replace("[hos : HasExt osFsExt]", "[ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]")
    s = s.replace("[HasExt osFsExt]", "[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]")
    s = s.replace("GooseLang.Ext.OsFs.", "GooseLang.Ext.Fs.")
    if "open Fs" not in s:
        s = re.sub(r"(^namespace bbolt\n)", r"\1\nopen Fs\n", s, count=1, flags=re.M)
    return s


def main():
    left = 0
    for p in sys.argv[1:]:
        s = open(p).read()
        t = port(s)
        if t != s:
            open(p, "w").write(t)
        for n, line in enumerate(t.split("\n"), 1):
            if "osFsExt" in line or "OsFs" in line:
                left += 1
                print(f"{p}:{n}: {line.strip()[:120]}")
    print(f"{left} lines still mention the v1 extension", file=sys.stderr)


if __name__ == "__main__":
    main()
