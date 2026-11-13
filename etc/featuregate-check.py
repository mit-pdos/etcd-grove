#!/usr/bin/env python3
"""The default feature gate's environment assumption, checked over the programs' compiled closures
(sweep repairs 1, B5, and k8s 7f-5, T5-c; `Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`).

`k8sfeature.featureGateOk` (Gate.lean) specifies `Enabled` and `Set` of the default gate under the
assumption that no code of the program mutates the gate but the driver's `Set`s of the values
`k8sfeature.k8sSetValue` fixes. This script greps the non-test Go files of each program's compiled
closure (`go list -deps`, GoFiles and CgoFiles) for every feature-gate mutator (`MUTATOR` below)
and compares the hits with the allow-list `etc/featuregate-allow.txt`, where each hit has its verdict:

  inert    a hit that mutates nothing at run time (a definition, a doc comment, an interface
           method, a helper the program never calls, another gate, the registration in
           `k8s.io/apiserver/pkg/features`' `init` that `features.init_0_ok` models);
  driver   one of the verified driver's `Set` calls, of a feature and its table value (the line's
           text includes the value: another value is another line, so not allowed);
  outside  a mutation in a program the assumption is not claimed of (`OUTSIDE`).

The programs the assumption is claimed of (`INSIDE`): the k8s etcd3 driver and the compactor, the
programs of the closed theorems that use `featureGateOk`. `OUTSIDE`: the DaemonSet controller's
program (`examples/k8s/daemonset/dsmain`), a separate process with its own adequacy theorem, which
mutates the gate (`SetFromMap` of three client-side features; `k8s.io/kubernetes/pkg/features`'
registration). For it the check is that no Lean module of its tree uses the gate's specs
(`LEAN_OUTSIDE`): if its proof ever needs them, the assumption must be re-examined for it first.

The order (`Set` before any `Enabled` of the feature) is not checked here: `notes/k8s-7f5-freeze.md`
§S0.4.

Fails on a hit with no entry, an `outside` hit in an inside program, an entry no program hits
(stale), or a Lean module of an outside program that names the gate's specs. Needs `go` (and the
module cache the examples' builds fill). Prints one line on success.
"""
import os, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOW = ROOT / "etc/featuregate-allow.txt"

# (name, module directory, package pattern)
INSIDE = [
    ("etcd3", "examples/k8s/etcd3", "."),
    ("compactor", "examples/k8s/compactor", "."),
]
OUTSIDE = [
    ("dsmain", "examples/k8s/daemonset", "./dsmain"),
]
LEAN_OUTSIDE = [
    "Proof/github_com/mit_pdos/etcd_grove/examples/k8s/daemonset",
    "Spec/github_com/mit_pdos/etcd_grove/examples/k8s/daemonset",
]
LEAN_GATE = re.compile(r"k8sfeature|featureGateOk|featuresInit|featureInit\b")

MUTATOR = re.compile(
    r"DefaultMutableFeatureGate\.(Set|SetWithLogger|SetFromMap|SetFromMapWithLogger|OverrideDefault"
    r"|SetEmulationVersion|Add|AddVersioned|AddDependencies|AddFlag|ResetFeatureValueToDefault)\b"
    r"|\.SetFromMap(WithLogger)?\(|OverrideDefault(AtVersion)?(WithLogger)?\(|SetEmulationVersion"
    r"|DeepCopyAndReset|featuregatetesting|ReplaceFeatureGates|AddFeaturesToExistingFeatureGates"
    r"|AddFeatureGates\(|ResetFeatureValueToDefault|AddDependencies\("
    r"|DefaultMutableFeatureGate *=|DefaultFeatureGate *=")

CLASSES = ("inert", "driver", "outside")


def go_env():
    env = dict(os.environ)
    env["GOWORK"] = "off"  # the examples' own modules (this subprocess only)
    env["PATH"] = "/usr/local/go/bin:" + os.path.expanduser("~/go/bin") + ":" + env.get("PATH", "")
    env.setdefault("GOTOOLCHAIN", "go1.27.1")
    return env


def closure(moddir, pkg, env):
    out = subprocess.run(
        ["go", "list", "-deps", "-f",
         "{{.Dir}}{{range .GoFiles}}\t{{.}}{{end}}{{range .CgoFiles}}\t{{.}}{{end}}", pkg],
        cwd=ROOT / moddir, env=env, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"go list in {moddir}: {out.stderr.strip()[:500]}")
    files = []
    for line in out.stdout.splitlines():
        parts = line.split("\t")
        files += [pathlib.Path(parts[0]) / f for f in parts[1:]]
    return files


def norm(path, modcache, goroot):
    p = str(path)
    for prefix, tag in ((modcache, "mod"), (goroot, "goroot"), (str(ROOT), "repo")):
        if prefix and p.startswith(prefix + "/"):
            return f"{tag}:{p[len(prefix) + 1:]}"
    return p


def hits_of(files, modcache, goroot):
    hits = set()
    for f in files:
        try:
            text = f.read_text(errors="replace")
        except OSError:
            continue
        for line in text.splitlines():
            if MUTATOR.search(line):
                hits.add((norm(f, modcache, goroot), " ".join(line.split())))
    return hits


def load_allow():
    allow = {}
    for i, line in enumerate(ALLOW.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4 or parts[0] not in CLASSES:
            raise RuntimeError(f"{ALLOW.name}:{i}: want <class>\\t<path>\\t<text>\\t<reason>")
        allow[(parts[1], parts[2])] = parts[0]
    return allow


def main():
    env = go_env()
    q = lambda v: subprocess.run(["go", "env", v], env=env, capture_output=True, text=True).stdout.strip()
    modcache, goroot = q("GOMODCACHE"), q("GOROOT")
    try:
        allow = load_allow()
    except RuntimeError as e:
        print(f"featuregate: FAILED: {e}")
        return 1
    bad, seen, nfiles = [], set(), 0
    for inside, progs in ((True, INSIDE), (False, OUTSIDE)):
        for name, moddir, pkg in progs:
            try:
                files = closure(moddir, pkg, env)
            except RuntimeError as e:
                print(f"featuregate: FAILED: {e}")
                return 1
            nfiles += len(files)
            for h in sorted(hits_of(files, modcache, goroot)):
                seen.add(h)
                cls = allow.get(h)
                if cls is None:
                    bad.append(f"{name}: no entry: {h[0]}\t{h[1]}")
                elif inside and cls == "outside":
                    bad.append(f"{name}: an `outside` mutation in a program the assumption is claimed of: {h[0]}\t{h[1]}")
    for h in sorted(set(allow) - seen):
        bad.append(f"stale entry (no program hits it): {h[0]}\t{h[1]}")
    for d in LEAN_OUTSIDE:
        for f in sorted((ROOT / d).rglob("*.lean")) if (ROOT / d).is_dir() else []:
            for i, line in enumerate(f.read_text(errors="replace").splitlines(), 1):
                if LEAN_GATE.search(line):
                    bad.append(f"{f.relative_to(ROOT)}:{i}: an outside program's proof names the gate's specs")
    if bad:
        print("featuregate: FAILED (Gate.lean's environment assumption, etc/featuregate-allow.txt):")
        for b in bad:
            print("  " + b)
        return 1
    print(f"featuregate: ok ({len(seen)} mutator hits in {nfiles} Go files of "
          f"{len(INSIDE)} programs and {len(OUTSIDE)} outside, all with their verdict)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
