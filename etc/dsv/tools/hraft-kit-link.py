#!/usr/bin/env python3
"""The `Link.lean` of the hraft kit (`examples/hraftnet` and its packages `rpctransport`, `service`;
notes/dsv-hraft.md, S5g): every `<F>.wp_proof` under `Dsverify/Proof/github_com/hashicorp/raft/examples/hraftnet/`
applied to its callees' results, in dependency order, in one file.

The kit's proofs are written inside their package's namespace, with `open`s, so a hypothesis
`(name : <G>.spec ...)` names its callee relatively; it is resolved as Lean would: `<G>` in each
enclosing namespace (innermost first), then in each opened one, then from the root. A callee is:

* a proof of the kit: its result in this Link (`hraftnet.wp_Orch`, `hraftnet.rpctransport.Conn.wp_Call`);
* a proof of raft or snapstore: its result in that package's Link (`etc/dsv/tools/hraft-link.py`);
* a spec of Perennial or of the main tree: as `etc/dsv/tools/hraft-link.py` resolves it;
* one of `EXT` below (Net's proofs, remote's Link, the main tree's `strconv.Atoi_dec`), a variant
  `(name : <G>.spec_<v> ...)` included (`net.rpc.NewServer.spec_owned`).

Each result is stated under its proof file's `variable`s. A callee with no result is an error.

usage: etc/dsv/tools/hraft-kit-link.py            print the Link (what `etc/gen-link.py --hraft-kit` runs)
"""
import importlib.util
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("hraft_link", os.path.join(os.path.dirname(os.path.abspath(__file__)), "hraft-link.py"))
hl = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hl)

KIT = os.path.join(ROOT, "Dsverify", "Proof", "github_com", "hashicorp", "raft", "examples", "hraftnet")
KIT_NS = "github_com.hashicorp.raft.examples.hraftnet"
LINK = os.path.join(KIT, "Link.lean")
RAFT_LINKS = [os.path.join(ROOT, "Dsverify", "Proof", "github_com", "hashicorp", "raft", "Link.lean"),
              os.path.join(ROOT, "Dsverify", "Proof", "github_com", "hashicorp", "raft", "examples", "snapstore", "Link.lean")]

# callees outside the kit, raft and Perennial: spec name (with its variant) -> (module, result)
EXT = {
    ("net.Dial", ""): ("Net.Proof.net.Dial", "_root_.Perennial.net.Dial.wp_proof"),
    ("net.DialTimeout", ""): ("Net.Proof.net.DialTimeout", "_root_.Perennial.net.DialTimeout.wp_proof"),
    ("net.Listen", ""): ("Net.Proof.net.Listen", "_root_.Perennial.net.Listen.wp_proof"),
    ("net.Listener.Accept", ""): ("Net.Proof.net.Listener__Accept", "_root_.Perennial.net.Listener.Accept.wp_proof"),
    ("net.Conn.Read", ""): ("Net.Proof.net.Conn__Read", "_root_.Perennial.net.Conn.Read.wp_proof"),
    ("net.Conn.Write", ""): ("Net.Proof.net.Conn__Write", "_root_.Perennial.net.Conn.Write.wp_proof"),
    ("net.Conn.Close", ""): ("Net.Proof.net.Conn__Close", "_root_.Perennial.net.Conn.Close.wp_proof"),
    ("net.rpc.Client.Close", ""): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.Client.Close.wp"),
    ("net.rpc.Client.Go", ""): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.Client.Go.wp"),
    ("net.rpc.NewClient", ""): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.NewClient.wp"),
    ("net.rpc.NewServer", "_owned"): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.NewServer.wp_owned"),
    ("net.rpc.Server.Accept", ""): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.Server.Accept.wp"),
    ("net.rpc.Server.Register", "_fresh"): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.Server.Register.wp_fresh"),
    ("net.rpc.SetCodec", ""): ("Net.Proof.net.rpc.Results", "_root_.Perennial.net.rpc.SetCodec.wp"),
    ("github_com.mit_pdos.etcd_grove.examples.lib.remote.Check", ""):
        ("Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link", "_root_.Perennial.EtcdGrove.remote.wp_Check"),
    ("github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient", ""):
        ("Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link", "_root_.Perennial.EtcdGrove.remote.wp_ServeClient"),
    ("strconv.Atoi_dec", ""): ("Proof.strconv.Atoi_dec", "_root_.Perennial.EtcdGrove.strconv.Atoi_dec.wp_proof"),
}

NAME = hl.NAME
PROOF_DECL = re.compile(r"^[ \t]*theorem\s+(" + NAME + r")\.wp_proof\b", re.M)
HYP = re.compile(r"\(\s*(" + NAME + r")\s*:\s*(" + NAME + r")\.(spec[A-Za-z0-9_']*)\b")
errors = []


def scopes(text, pos):
    """The namespaces (below `Perennial`) and the opened names in effect at `pos`."""
    ns, opens = [], []
    for m in re.finditer(r"^(namespace|end|open)\s+(.*)$", text[:pos], re.M):
        kind, arg = m.group(1), m.group(2).strip()
        if kind == "namespace":
            ns += arg.split(".")
        elif kind == "end":
            parts = arg.split(".")
            if ns[-len(parts):] == parts:
                del ns[-len(parts):]
        elif not arg.endswith(" in"):
            arg = re.sub(r"\([^)]*\)", "", arg)
            opens += [(list(ns), o) for o in arg.split() if o != "hiding"]
    if ns and ns[0] == "Perennial":
        ns = ns[1:]
    return ns, [(n[1:] if n and n[0] == "Perennial" else n, o) for n, o in opens]


def candidates(name, ns, opens):
    out = []
    for i in range(len(ns), -1, -1):
        out.append(".".join(ns[:i] + [name]))
    for ons, o in opens:
        for i in range(len(ons), -1, -1):
            out.append(".".join(ons[:i] + [o, name]))
    out.append(name)
    return out


def qualify(line, ns):
    """A proof file's `variable` line with its packages' `Assumptions` classes written from the root
    (`Assumptions` in `…hraftnet.rpctransport`, `service.Assumptions` in `…hraftnet`)."""
    def fix(m):
        name = m.group(2)
        if name.startswith(("github_com.", "net.", "_root_.")) or "." in name and name.split(".")[0] in ("go", "sync", "time", "log", "errors"):
            return m.group(0)
        return m.group(1) + ".".join(ns + [name])
    return re.sub(r"([\[(:\s])((?:[A-Za-z_][\w']*\.)*Assumptions)\b", fix, line)


def section_vars(text, pos):
    """The `variable` lines of the section a declaration at `pos` is in."""
    start = max([m.end() for m in re.finditer(r"^section\b.*$", text[:pos], re.M)] + [0])
    return re.findall(r"^variable .*$", text[start:pos], re.M)


def path_of_module(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def result_vars(mod, result):
    """The bound and ghost-state instance binders (`NaInvG`, `ThreadBoundLe`, `ReceiptBoundLe`) a
    callee's result is stated under (its Link's section), if `mod` declares it as `theorem <result>`;
    the packages' `Assumptions` it takes are found from the kit's."""
    p = path_of_module(mod)
    if not os.path.exists(p):
        return []
    t = open(p, encoding="utf-8").read()
    short = result.replace("_root_.Perennial.", "").replace("EtcdGrove.", "", 1)
    last = short.split(".")[-1]
    for m in re.finditer(r"^theorem\s+(\S+)", t, re.M):
        n = m.group(1)
        if n == short or n == last or short.endswith("." + n):
            return [g for v in section_vars(t, m.start()) for g in (hl.binder_groups(v) or [])
                    if re.match(r"\[\s*(?:[\w']+\s*:\s*)?(?:NaInvG|ThreadBoundLe|ReceiptBoundLe)\s+GF\b", g)]
    return []


def own_result(full):
    r = hl.result_name(full)
    return "hraftnet." + r[len(KIT_NS) + 1:] if r.startswith(KIT_NS + ".") else r


def generate():
    proofs = {}  # full name -> (module, hyps [(hname, callee, variant, cands)], variables)
    for path in sorted(hl.lean_files(KIT)):
        if os.path.basename(path) == "Link.lean":
            continue
        text = open(path, encoding="utf-8").read()
        for d in PROOF_DECL.finditer(text):
            ns, opens = scopes(text, d.start())
            name = d.group(1)
            full = name if name.startswith("github_com.") else ".".join(ns + [name])
            sig = hl.proof_signature(text, d.start())
            hyps = [(m.group(1), m.group(2), m.group(3)[len("spec"):], candidates(m.group(2), ns, opens))
                    for m in HYP.finditer(sig)]
            variables = [qualify(l, ns) for l in re.findall(r"^variable .*$", text, re.M)]
            proofs[full] = (hl.module_of(path), hyps, variables, path)
    raft = {}  # spec full name -> (module, result)
    for lk in RAFT_LINKS:
        t = open(lk, encoding="utf-8").read()
        for m in re.finditer(r"^theorem\s+(\S+)\s*:\s*(\S+)\.spec\b", t, re.M):
            raft[m.group(2)] = (hl.module_of(lk), "_root_.Perennial.EtcdGrove." + m.group(1))
    ext = hl.ext_specs()
    order, state = [], {}
    args_of, imports = {}, set()

    def resolve(path, hname, callee, variant, cands):
        for c in cands:
            if variant == "" and c in proofs:
                return ("kit", c)
            if (c, variant) in EXT:
                return ("ext",) + EXT[(c, variant)]
            if variant == "" and c in raft:
                return ("ext",) + raft[c]
            if variant == "" and c in ext and ext[c][1]:
                return ("perennial", ext[c][1], ext[c][2])
        errors.append(f"{hl.rel(path)}: hypothesis `{hname}`: `{callee}.spec{variant}` has no result")
        return None

    res = {}
    for n, (_, hyps, _, path) in proofs.items():
        res[n] = [resolve(path, h[0], h[1], h[2], h[3]) for h in hyps]

    def visit(n, stack):
        if state.get(n) == "done":
            return
        if state.get(n) == "active":
            errors.append("circular: " + " -> ".join(stack + [n]))
            return
        state[n] = "active"
        for r in res[n]:
            if r and r[0] == "kit":
                visit(r[1], stack + [n])
        state[n] = "done"
        order.append(n)

    for n in sorted(proofs):
        visit(n, [])
    for n in order:
        mod, hyps, _, _ = proofs[n]
        imports.add(mod)
        args = []
        for r in res[n]:
            if r is None:
                args.append("sorry")
            elif r[0] == "kit":
                args.append(own_result(r[1]))
            elif r[0] == "ext":
                imports.add(r[1]); args.append(r[2])
            else:
                imports.update(r[1]); args.append(r[2])
        args_of[n] = args
    lines = ["/-",
             "The results of the hraft kit's proofs (`examples/hraftnet`, `rpctransport`, `service`): every",
             "`<F>.wp_proof` of `Dsverify/Proof/github_com/hashicorp/raft/examples/hraftnet/` applied to its",
             "callees' results (the kit's own, raft's and snapstore's Links, Perennial's, Net's, remote's), in",
             "dependency order. Generated by `etc/dsv/tools/hraft-kit-link.py` (`etc/gen-link.py --hraft-kit`);",
             "do not edit by hand.",
             "-/", "module", ""]
    lines += [f"public import {m}" for m in sorted(imports)]
    lines += ["", "@[expose] public section", "", "set_option linter.unusedSectionVars false", "",
              "namespace Perennial", "", "open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode", "",
              "namespace EtcdGrove", "", "open Net", "open github_com.mit_pdos.etcd_grove.examples.lib.remote (RemoteGS)", "",
              "attribute [local instance] GooseGlobalGS.gooseInvGS"]
    cur = None
    extras = {}
    for n in order:
        vs = list(proofs[n][2])
        have = {hl.binder_key(g) for v in vs for g in (hl.binder_groups(v) or [])}
        extra = []
        for r in res[n]:
            gs = (result_vars(r[1], r[2]) if r and r[0] == "ext" else
                  extras.get(r[1], []) if r and r[0] == "kit" else [])
            for g in gs:
                k = hl.binder_key(g)
                if k not in have:
                    have.add(k)
                    extra.append(g)
        extras[n] = extra
        if extra:
            vs.append("variable " + " ".join(extra))
        if vs != cur:
            if cur is not None:
                lines += ["", "end link"]
            lines += ["", "section link"] + vs
            cur = vs
        args = "".join(" " + a for a in args_of[n])
        lines += ["", f"theorem {own_result(n)} : _root_.Perennial.{n}.spec (GF := GF) (hG := hG) :=",
                  f"  _root_.Perennial.{n}.wp_proof{args}"]
    if cur is not None:
        lines += ["", "end link"]
    lines += ["", "end EtcdGrove", "", "end Perennial", ""]
    return "\n".join(lines)


def main():
    out = generate()
    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        sys.exit(1)
    sys.stdout.write(out)


if __name__ == "__main__":
    main()
