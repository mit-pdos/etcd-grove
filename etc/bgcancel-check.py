#!/usr/bin/env python3
"""Fail if the pinned Perennial specifies `context.WithCancelCause` (k8s 7f-4, Addendum T-i review, m2).

`context.bgCancelChild` (`Proof/context/BgCancel.lean`: a `*cancelCtx` whose parent field is
`Background()`) is what net/http's round trippers take of a request's context (`http.reqCtxBg`);
its soundness rests on such a context's cause being `context.Canceled`. Go's `WithCancelCause(Background())`
makes the same shape with a caller-chosen cause, which `RoundTrip` would return. Perennial has no
spec of it today, so a verified program cannot make one. A pin bump that brings one (a
`wp_WithCancelCause` whose post gives `ctxField c ↦□ parent`, as `wp_WithCancel_gen`'s does) would
make the RoundTrip axioms false: this check makes such a bump stop for a re-review of
`bgCancelChild` (then add a ghost fact that only `WithCancel` gives, and update the allowance below).

Perennial's directory: the `perennial` entry of the manifest `$LAKE_PACKAGES` when it is a path,
else `.lake/packages/perennial`. Reads the sources only.
"""
import json, os, pathlib, re, sys

def perennial_dir():
    m = os.environ.get("LAKE_PACKAGES")
    if m:
        for p in json.load(open(m)).get("packages", []):
            if p.get("name") == "perennial" and p.get("type") == "path":
                return pathlib.Path(p["dir"])
    return pathlib.Path(".lake/packages/perennial")

def main():
    d = perennial_dir()
    root = d / "Perennial"
    if not root.is_dir():
        print(f"bgcancel: no Perennial sources at {root}", file=sys.stderr)
        return 1
    pat = re.compile(r"WithCancelCause")
    hits = []
    for sub in ("Spec", "Proof"):
        for f in sorted((root / sub).rglob("*.lean")):
            for i, line in enumerate(f.read_text(errors="replace").splitlines(), 1):
                if pat.search(line):
                    hits.append(f"{f.relative_to(d)}:{i}: {line.strip()[:120]}")
    if hits:
        print("bgcancel: FAILED: the pinned Perennial mentions WithCancelCause in its specs or proofs;"
              " re-review context.bgCancelChild (Proof/context/BgCancel.lean, etc/bgcancel-check.py):")
        for h in hits[:10]:
            print("  " + h)
        return 1
    print("bgcancel: ok (no WithCancelCause spec in the pinned Perennial)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
