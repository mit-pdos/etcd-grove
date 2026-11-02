#!/usr/bin/env python3
"""Check that only the listed modules `import all` a sealed module (the backend-auth-split stage's
Q6, 2026-11-02; in `etc/gates.sh` and CI).

A sealed definition (`@[no_expose]`) and a `private` law are visible to any module that imports
their file with `import all`; `etc/api-check.py` forbids that outside a package but not inside it.
Some sealed facts are part of the trust base: the backend's pending flags (`rbSide`, sealed in
`InvBackend.lean`; `rbSide_idle`, private to `TrackedLemmas.lean`) are cleared only by `Unlock`'s
proof, which the trusted readers of the tracked buckets rely on. This check pins who may
`import all` each such module. It cannot check that the allowed importers export no law that
clears a flag (a public theorem of `TrackedLemmas`, `NewAlloc` or `Unlock`'s proof): that is the
interface diff's (`etc/gen-interface.py etc/api/backend.txt`).

The configuration (`etc/import-all.txt`), one directive per line, `#` comments:

    sealed MODULE         a module whose `import all`s are restricted
    allow MODULE IMPORTER IMPORTER may `import all` MODULE

usage: etc/import-all-check.py [CONFIG] [--check]
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC_DIRS = ("Code", "TrustedCode", "GeneratedProof", "ManualProof", "Spec", "Proof", "RaftWitness",
            "EtcdDeps", "GooseLang")
IMP = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+all\s+([A-Za-z0-9_.']+)", re.M)


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    cfg = pathlib.Path(args[0]) if args else ROOT / "etc" / "import-all.txt"
    sealed, allow = set(), set()
    for line in cfg.read_text().splitlines():
        line = line.split("#", 1)[0].split()
        if not line:
            continue
        if line[0] == "sealed" and len(line) == 2:
            sealed.add(line[1])
        elif line[0] == "allow" and len(line) == 3:
            allow.add((line[1], line[2]))
        else:
            print(f"{cfg}: bad directive: {' '.join(line)}", file=sys.stderr)
            return 2
    bad = []
    for d in SRC_DIRS:
        for f in sorted((ROOT / d).rglob("*.lean")) if (ROOT / d).exists() else []:
            mod = ".".join(f.relative_to(ROOT).with_suffix("").parts)
            for m in IMP.findall(f.read_text()):
                if m in sealed and (m, mod) not in allow:
                    bad.append(f"{mod}: `import all {m}` (not allowed by {cfg.name})")
    for b in bad:
        print(b)
    print(f"import-all: {'FAILED' if bad else 'ok'} ({len(sealed)} sealed module(s), "
          f"{len(bad)} violation(s))")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
