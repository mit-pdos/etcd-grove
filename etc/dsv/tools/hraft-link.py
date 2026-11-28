#!/usr/bin/env python3
"""The `Link.lean` of hashicorp/raft's two proved packages, `raft` and `raft/examples/snapstore`
(notes/dsv-hraft.md, P5): dsverify-lab's `examples/hraft/proof/etc/gen-link.py` (241f27e), ported.

Every Go function `F` of a package `P` (a directory under `Dsverify/Spec/github_com/hashicorp/`) has
its spec `Dsverify/Spec/github_com/hashicorp/P/F.lean` (`<F>.spec`) and its proof, the same path under
`Dsverify/Proof/` (`theorem <F>.wp_proof (callee specs) : <F>.spec`). The Link instantiates every proof
with its callees' results, in dependency order (`theorem <pre>.wp_<f> : <pre>.<f>.spec := ...wp_proof
<callees' results>`). The callees are read from the hypotheses of `wp_proof`, `(name : <G>.spec ...)`:

* a spec of the same package: its result in this Link;
* a spec of the other package: its result in that package's Link;
* a spec of Perennial (`Perennial/Spec/<pkg>/`): `Perennial.Proof.<pkg>.Link`'s result;
* a spec of this repository's main tree (`Spec/<pkg>/`): the result `<pre>.wp_<f>` declared in
  `Proof/<pkg>/Link.lean`, or `<G>.wp_proof` of `Proof/<pkg>/<F>.lean` applied to its callees'
  Perennial results (`io.Copy_Discard.wp_proof sync.Pool.wp_Get sync.Pool.wp_Put`);
* `(name : <G>.spec_<v> ...)`, a variant of a callee's spec (`fmt.Errorf.spec_tnErr`): the theorem
  `<result of G>_<v>` (`fmt.wp_Errorf_tnErr`) of a shared Proof file of the package. (The lab's were
  axioms; here they must be theorems: an axiom is refused.)

The results are declared in `Perennial.EtcdGrove` (every Link's results are under it,
etc/proof_roots.py), named by the package's qualifier (`raft.Raft.wp_run`,
`snapstore.Store.wp_Create`: etc/verified-code.py's reading); a callee's result outside it is written from the root
(`_root_.Perennial.fmt.wp_Errorf`).

A callee in `PENDING` has no result yet: the proofs that need it (transitively) are left out of the
Link, and listed on stderr. Any other callee without a result is an error.

It also checks the imports: a Spec file, a Proof file or a shared file of a package imports no Proof
file of a Go function, no `Link.lean`.

usage: etc/dsv/tools/hraft-link.py            regenerate both Link.lean files
       etc/dsv/tools/hraft-link.py --check    exit 1 if one is out of date (nothing is written)
       etc/dsv/tools/hraft-link.py --stdout P print package P's Link (`raft`, `raft/examples/snapstore`;
                                              what `etc/gen-link.py --hraft`/`--hraft-snapstore` run)
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
SPEC = os.path.join(ROOT, "Dsverify", "Spec", "github_com", "hashicorp")
PROOF = os.path.join(ROOT, "Dsverify", "Proof", "github_com", "hashicorp")
sys.dont_write_bytecode = True  # no etc/__pycache__
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402  (Perennial's checkout as Lake resolves it)
PERENNIAL = proof_roots.PERENNIAL
EXT_SPECS = [("perennial", os.path.join(PERENNIAL, "Perennial", "Spec"), PERENNIAL),
             ("main", os.path.join(ROOT, "Spec"), ROOT)]
# the proved packages (directories under SPEC/PROOF); the kit (raft/examples/hraftnet) has its own
PACKAGES = ["raft", os.path.join("raft", "examples", "snapstore")]
# callees with no result yet (notes/dsv-hraft.md, P5): the proofs reaching them are not linked
PENDING = set()

NAME = r"[A-Za-z_«][A-Za-z0-9_'.«»!?]*"
SPEC_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:abbrev|def)\s+(" + NAME + r")\.spec\b", re.M)
PROOF_DECL = re.compile(r"^\s*(theorem|axiom)\s+(" + NAME + r")\.wp_proof\b", re.M)
HYP = re.compile(r"\(\s*(" + NAME + r")\s*:\s*(" + NAME + r")\.spec\b")
# a variant of a callee's spec, `(h : <G>.spec_<v> ...)`: a project-level trusted spec of a call form
# the callee's own spec excludes, whose result is the axiom `<result of G>_<v>` in a shared Proof file
VARIANT_HYP = re.compile(r"\(\s*(" + NAME + r")\s*:\s*(" + NAME + r")\.(spec_[A-Za-z0-9_']+)\b")
AXIOM_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?axiom\s+(" + NAME + r")", re.M)
THM_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?theorem\s+(" + NAME + r")", re.M)
VAR_BINDER = re.compile(r"[({\[]\s*([A-Za-z_][\w'\s]*?)\s*:")
IMPORT = re.compile(r"^(?:public )?import (Dsverify\.Proof\.\S+)", re.M)

errors = []


def err(msg, pkg=None):
    errors.append((pkg, msg))


def rel(path):
    return os.path.relpath(path, ROOT)


def lean_files(base):
    for d, _, fs in os.walk(base):
        for f in sorted(fs):
            if f.endswith(".lean"):
                yield os.path.join(d, f)


def module_of(path):
    return ".".join(os.path.relpath(path[: -len(".lean")], ROOT).split(os.sep))


def binder_groups(line):
    """The bracketed binders of a `variable` line (`[…]`, `{…}`, `(…)`, nesting allowed)."""
    body, out, depth, cur = line[len("variable"):], [], 0, ""
    for c in body:
        if depth == 0 and c.isspace():
            continue
        cur += c
        if c in "[{(":
            depth += 1
        elif c in "]})":
            depth -= 1
            if depth == 0:
                out.append(cur)
                cur = ""
    return out if not cur.strip() else None


def binder_key(g):
    """An instance binder's class (its name dropped); other binders as written."""
    g = " ".join(g.split())
    if g.startswith("["):
        return re.sub(r"^\[\s*[A-Za-z_][\w']*\s*:\s*", "[", g)
    return g


def canonical_vars(ctx, canon):
    """`ctx` (a proof file's `open`/`variable` lines) with each instance binder already declared
    in the package (`canon`: class -> the line declaring it) replaced by that line."""
    out = []
    for v in ctx:
        groups = binder_groups(v) if v.startswith("variable ") else None
        if groups is None:
            if v not in out:
                out.append(v)
            continue
        keep, earlier = [], []
        for g in groups:
            k = binder_key(g)
            if g.startswith("[") and k in canon and canon[k] != v:
                if canon[k] not in earlier:
                    earlier.append(canon[k])
            elif g.startswith("[") and any(binder_key(x) == k for x in keep):
                pass
            else:
                keep.append(g)
        line = v if len(keep) == len(groups) else ("variable " + " ".join(keep) if keep else None)
        for e in earlier:
            if e not in out:
                out.append(e)
        if line is not None:
            for g in keep:
                if g.startswith("["):
                    canon.setdefault(binder_key(g), line)
            if line not in out:
                out.append(line)
    return out


def strip_guillemets(s):
    return s.replace("«", "").replace("»", "")


def components(name):
    """A Lean name's components (dots inside «» do not split)."""
    out, cur, quoted = [], "", False
    for c in name:
        if c == "«":
            quoted = True
        elif c == "»":
            quoted = False
        if c == "." and not quoted:
            out.append(cur)
            cur = ""
        else:
            cur += c
    out.append(cur)
    return out


def check_file_name(path, name, pkg):
    """`F` (the file name) is the last components of `name`, joined by `__`."""
    f = os.path.basename(path)[: -len(".lean")]
    parts = [strip_guillemets(c) for c in components(name)]
    if parts[-1] == "initialize'":
        parts[-1] = "initialize"
    # a trailing `_` keeps apart names that differ only in case (`asType_.lean` next to
    # `AsType.lean`), for case-insensitive file systems
    want = (f[:-1] if f.endswith("_") and not f.endswith("__") else f).split("__")
    if parts[-len(want):] != want:
        err(f"{rel(path)}: the file of `{name}` should be named after it "
            f"(`{'__'.join(parts[-2:])}.lean` for a method, `{parts[-1]}.lean` for a "
            f"function)", pkg)


# a result of the packages' own, named by the package's qualifier (`raft.Raft.wp_run`,
# `snapstore.Store.wp_Create`), as etc/verified-code.py reads a Link's results
OWN_PREFIXES = [("github_com.hashicorp.raft.examples.snapstore.", "snapstore."),
                ("github_com.hashicorp.raft.", "raft.")]


def own_result(spec):
    r = result_name(spec)
    for long, short in OWN_PREFIXES:
        if r.startswith(long):
            return short + r[len(long):]
    return r


def result_name(spec):
    cs = components(spec)
    # `wp_` + a quoted keyword is an ordinary identifier (`sort.«Sort»` -> `sort.wp_Sort`)
    return ".".join(cs[:-1] + ["wp_" + strip_guillemets(cs[-1])])


def proof_signature(text, start):
    """The text from `theorem X.wp_proof` to its `:=` (or the end of the axiom's statement)."""
    # the `:=` outside brackets (not the `(GF := GF)` of a hypothesis)
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and (text.startswith(":=", i) or text.startswith("\n\n", i)):
            return text[start:i]
    return text[start:]


def pkg_files(base, pkg):
    """The `.lean` files directly in `base/pkg` (a package's subdirectories are its shared modules')."""
    d = os.path.join(base, pkg)
    return [os.path.join(d, f) for f in sorted(os.listdir(d)) if f.endswith(".lean")] if os.path.isdir(d) else []


def link_path(pkg):
    return os.path.join(PROOF, pkg, "Link.lean")


def ext_specs():
    """Specs of other libraries: name -> (kind, modules of the result, the result's term)."""
    ext, main = {}, []
    for kind, base, _ in EXT_SPECS:
        for path in lean_files(base):
            text = open(path, encoding="utf-8").read()
            names = SPEC_DECL.findall(text)
            # Perennial: one spec per file; the main tree's may hold a few (`Spec/io/Copy.lean`)
            if (len(names) != 1 if kind == "perennial" else not names):
                continue
            if kind == "main" and re.search(r"^namespace EtcdGrove\b", text, re.M):
                continue  # `Perennial.EtcdGrove.<name>`, not the name a hraft proof writes
            pkg = os.path.relpath(os.path.dirname(path), base)
            for name in names:
                if name in ext or any(m[0] == name for m in main):
                    continue  # Perennial's first
                if kind == "perennial":
                    ext[name] = (kind, ["Perennial.Proof." + ".".join(pkg.split(os.sep)) + ".Link"],
                                 "_root_.Perennial." + result_name(name))
                else:
                    main.append((name, pkg, path, base))
    # the main tree's (in `namespace Perennial`): the package's Link's result, or the function's
    # proof `<G>.wp_proof` of `Proof/<pkg>/<F>.lean` applied to its callees' Perennial results
    for name, pkg, path, base in main:
        res = result_name(name)
        lk = os.path.join(ROOT, "Proof", pkg, "Link.lean")
        if os.path.exists(lk) and re.search(r"^theorem\s+" + re.escape(res) + r"\b",
                                            open(lk, encoding="utf-8").read(), re.M):
            ext[name] = ("main", ["Proof." + ".".join(pkg.split(os.sep)) + ".Link"], "_root_.Perennial." + res)
            continue
        pf = os.path.join(ROOT, "Proof", os.path.relpath(path, base))
        if os.path.exists(pf):
            t = open(pf, encoding="utf-8").read()
            d = re.search(r"^\s*theorem\s+" + re.escape(name) + r"\.wp_proof\b", t, re.M)
            if d:
                sig = proof_signature(t, d.start())
                callees = [m.group(2) for m in HYP.finditer(sig)]
                if VARIANT_HYP.search(sig) or any(ext.get(c, ("",))[0] != "perennial" for c in callees):
                    ext[name] = ("main", None, None)  # a callee this script does not resolve
                    continue
                mods = [module_of(pf)] + [m for c in callees for m in ext[c][1]]
                term = "_root_.Perennial." + name + ".wp_proof"
                if callees:
                    term = "(" + " ".join([term] + [ext[c][2] for c in callees]) + ")"
                ext[name] = ("main", mods, term)
                continue
        ext[name] = ("main", None, None)  # no result (yet)
    return ext


def generate():
    """{Link path: content}, the skipped proofs {pkg: [(name, why)]}; errors go to `errors`."""
    # specs: name -> (package dir, file)
    specs = {}
    for pkg in PACKAGES:
        for path in pkg_files(SPEC, pkg):
            text = open(path, encoding="utf-8").read()
            names = SPEC_DECL.findall(text)
            if len(names) != 1:
                err(f"{rel(path)}: a Spec file holds exactly one `<fn>.spec` (found {len(names)})", pkg)
                continue
            name = names[0]
            check_file_name(path, name, pkg)
            specs[name] = (pkg, path)

    # proofs, by package: name -> (file, hypotheses, open/variable lines)
    packages = {}
    for pkg in PACKAGES:
        for path in pkg_files(PROOF, pkg):
            text = open(path, encoding="utf-8").read()
            decls = list(PROOF_DECL.finditer(text))
            if not decls:
                continue
            if len(decls) != 1:
                err(f"{rel(path)}: a Proof file holds exactly one `<fn>.wp_proof` "
                    f"(found {len(decls)})", pkg)
                continue
            d = decls[0]
            if d.group(1) == "axiom":
                err(f"{rel(path)}: `{d.group(2)}.wp_proof` is an axiom (dsv-hraft adds none)", pkg)
            name = d.group(2)
            spec_path = os.path.join(SPEC, os.path.relpath(path, PROOF))
            if specs.get(name, (None, None))[1] != spec_path:
                err(f"{rel(path)}: `{name}.wp_proof` has no spec `{name}.spec` in "
                    f"{rel(spec_path)}", pkg)
            sig = proof_signature(text, d.start())
            hyps = sorted([(m.start(), (m.group(1), m.group(2))) for m in HYP.finditer(sig)]
                          + [(m.start(), (m.group(1), m.group(2), m.group(3)[len("spec"):]))
                             for m in VARIANT_HYP.finditer(sig)])
            hyps = [h for _, h in hyps]
            context = [l for l in re.findall(r"^open .*$|^variable .*$", text, re.M)
                       if not l.rstrip().endswith(" in")]
            packages.setdefault(pkg, {})[name] = (path, hyps, context)

    ext = ext_specs()

    # the theorems of the packages' shared Proof files (not a function's proof): name -> module
    trusted = {}
    for pkg in PACKAGES:
        for path in lean_files(os.path.join(PROOF, pkg)):
            text = open(path, encoding="utf-8").read()
            if PROOF_DECL.search(text) or os.path.basename(path) == "Link.lean":
                continue
            for a in AXIOM_DECL.findall(text):
                trusted[a] = None  # an axiom: refused below
            for a in THM_DECL.findall(text):
                trusted.setdefault(a, module_of(path))

    for name, (pkg, path) in specs.items():
        if name not in packages.get(pkg, {}):
            err(f"{rel(path)}: `{name}.spec` has no proof in "
                f"{rel(os.path.join(PROOF, os.path.relpath(path, SPEC)))}", pkg)

    # the proofs that cannot be linked: a PENDING callee, transitively
    all_proofs = {n: v for ps in packages.values() for n, v in ps.items()}
    why = {}
    for n, (_, hyps, _) in all_proofs.items():
        for h in hyps:
            if len(h) == 2 and h[1] in PENDING:
                why.setdefault(n, f"takes `{h[1]}.spec`, which has no result yet")
    changed = True
    while changed:
        changed = False
        for n, (_, hyps, _) in sorted(all_proofs.items()):
            if n not in why:
                for h in hyps:
                    if len(h) == 2 and h[1] in why:
                        why[n] = f"its callee `{h[1]}` is not linked"
                        changed = True
                        break
    skipped = {}

    # the imports of the discipline
    fn_proofs = {module_of(p) for ps in packages.values() for (p, _, _) in ps.values()}
    links = {module_of(link_path(pkg)) for pkg in PACKAGES}
    for pkg in PACKAGES:
        for base in (SPEC, PROOF):
            for path in lean_files(os.path.join(base, pkg)):
                if any(os.path.relpath(path, os.path.join(base, q)).split(os.sep)[0] != ".."
                       for q in PACKAGES if len(q) > len(pkg)):
                    continue  # the other package's
                if os.path.basename(path) == "Link.lean":
                    continue
                for imp in IMPORT.findall(open(path, encoding="utf-8").read()):
                    imp = strip_guillemets(imp)
                    if imp in fn_proofs or imp in links:
                        err(f"{rel(path)}: imports {imp}; import the Spec files of callees "
                            f"and shared files only", pkg)

    outputs = {}
    for pkg in PACKAGES:
        proofs = packages.get(pkg, {})
        skipped[pkg] = sorted((n, why[n]) for n in why if specs.get(n, (None,))[0] == pkg)
        proofs = {n: v for n, v in proofs.items() if n not in why}
        order, state = [], {}

        def visit(n, stack):
            if state.get(n) == "done":
                return
            if state.get(n) == "active":
                err(f"package {pkg}: the proofs' hypotheses are circular: "
                    f"{' -> '.join(stack + [n])}", pkg)
                return
            state[n] = "active"
            for h in proofs[n][1]:
                if len(h) == 2 and h[1] in proofs:
                    visit(h[1], stack + [n])
            state[n] = "done"
            order.append(n)

        for n in sorted(proofs):
            visit(n, [])

        imports, context, canon, args_of = set(), [], {}, {}
        for n in order:
            path, hyps, ctx = proofs[n]
            ctx = canonical_vars(ctx, canon)
            proofs[n] = (path, hyps, ctx)
            imports.add(module_of(path))
            for v in ctx:
                if v not in context:
                    context.append(v)
            args = []
            for h in hyps:
                hname, callee = h[0], h[1]
                if len(h) == 3:
                    res = result_name(callee) + h[2]
                    if res not in trusted:
                        err(f"{rel(path)}: hypothesis `{hname}`: no shared Proof file of the package "
                            f"proves `{res}` (`{callee}.spec{h[2]}`)", pkg)
                    elif trusted[res] is None:
                        err(f"{rel(path)}: hypothesis `{hname}`: `{res}` is an axiom", pkg)
                    else:
                        imports.add(trusted[res])
                    args.append("_root_.Perennial." + res)
                elif callee in specs:
                    cpkg = specs[callee][0]
                    if cpkg != pkg:
                        imports.add(module_of(link_path(cpkg)))
                    args.append(own_result(callee))
                elif callee in ext and ext[callee][1]:
                    imports.update(ext[callee][1])
                    args.append(ext[callee][2])
                else:
                    err(f"{rel(path)}: hypothesis `{hname}`: `{callee}.spec` has no result"
                        + (" (its spec has no proof yet)" if callee in ext else
                           " (no Spec file defines it)"), pkg)
                    args.append("sorry")
            args_of[n] = args

        lines = [
            "/-",
            f"The results of the proofs of `github_com/hashicorp/{pkg}`: every `<F>.wp_proof` of",
            f"`Dsverify/Proof/github_com/hashicorp/{pkg}/` applied to its callees' results, in dependency",
            "order. Generated by `etc/dsv/tools/hraft-link.py` (`etc/gen-link.py --hraft`, `--hraft-snapstore`);",
            "do not edit by hand.",
        ]
        if skipped[pkg]:
            lines += ["", "Not linked yet (a callee has no result: `PENDING` in the script):"]
            lines += [f"`{n}`" + (", " if i + 1 < len(skipped[pkg]) else ".")
                      for i, (n, _) in enumerate(skipped[pkg])]
        lines += ["-/", "module", ""]
        lines += [f"public import {m}" for m in sorted(imports)]
        lines += ["", "@[expose] public section", "", "namespace Perennial", ""]
        lines += [v for v in context if v.startswith("open ")]
        # the results under `Perennial.EtcdGrove`, as every Link's (etc/proof_roots.py); the
        # callees' results outside it are written from the root, so that a name of `EtcdGrove`'s
        # (`EtcdGrove.fmt.wp_Errorf`) never captures one of Perennial's
        lines += ["", "namespace EtcdGrove"]

        def own_vars(n):
            return [v for v in proofs[n][2] if v.startswith("variable ")]
        binders = {}
        for v in context:
            if v.startswith("variable "):
                for names in VAR_BINDER.findall(v):
                    for b in names.split():
                        binders.setdefault(b, set()).add(v)
        if any(len(vs) > 1 for vs in binders.values()):
            runs = []
            for n in order:
                if runs and own_vars(runs[-1][-1]) == own_vars(n):
                    runs[-1].append(n)
                else:
                    runs.append([n])
            sections = [(own_vars(r[0]), r) for r in runs]
        else:
            allv = [v for v in context if v.startswith("variable ")]
            need = {}
            for n in order:
                vs = set(own_vars(n))
                for h in proofs[n][1]:
                    if len(h) == 2 and h[1] in proofs:
                        vs |= need[h[1]]
                need[n] = vs
            sorder = sorted(order, key=lambda n: len(need[n]))
            sections = []
            for n in sorder:
                vs = [v for v in allv if v in need[n]]
                if sections and sections[-1][0] == vs:
                    sections[-1][1].append(n)
                else:
                    sections.append((vs, [n]))
        for i, (vs, ns) in enumerate(sections):
            lines += ["", "end link", ""] if i > 0 else [""]
            lines += ["section link"]
            lines += vs
            for n in ns:
                args = "".join(" " + a for a in args_of[n])
                lines += ["", f"theorem {own_result(n)} : {n}.spec (GF := GF) (hG := hG) :=",
                          f"  {n}.wp_proof{args}"]
        lines += ["", "end link", "", "end EtcdGrove", "", "end Perennial", ""]
        outputs[link_path(pkg)] = "\n".join(lines)
    return outputs, skipped


def main():
    argv = sys.argv[1:]
    check = "--check" in argv
    outputs, skipped = generate()
    if errors:
        for _, e in errors:
            print(e, file=sys.stderr)
        sys.exit(1)
    if "--stdout" in argv:
        pkg = argv[argv.index("--stdout") + 1]
        sys.stdout.write(outputs[link_path(pkg)])
        return
    for pkg, names in sorted(skipped.items()):
        for n, w in names:
            print(f"not linked in {pkg}: {n} ({w})", file=sys.stderr)
    stale = []
    for path, content in sorted(outputs.items()):
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != content:
            stale.append(path)
            if not check:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(content)
    for p in stale:
        print(("out of date: " if check else "wrote ") + rel(p))
    if check and stale:
        sys.exit(1)


if __name__ == "__main__":
    main()
