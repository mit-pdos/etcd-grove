"""`etc/gen-link.py --kvnet`: KvNet/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Link.lean,
kvnet's and kvcheck's proofs (the part `KvNet/`, `notes/kvnet-part.md`), every proof applied to its
callees' results.

As `--walfs` (`etc/link_walfs.py`), the callees are read off each proof's binders, not from a list.
What differs: kvnet's specs are stated over **model parameters** that the proofs instantiate at
different places (`Run.spec F rep cf S` is generic, `StartNode.wp_proof` proves `StartNode.spec` only
at `kvFacts γ _`, `kvRep γ vs dir`, ...), so a result's statement is not always its proof's. The rules:

- **The results.** Every `theorem` named `<F>.wp_proof<S>` of the part's own proofs (`OWN`: under
  `KvNet/Proof`, outside raft's tree, which raft-noax's `Link` links; and the main tree's directories
  of `MAIN_OWN`) whose conclusion is a spec applied to arguments and whose explicit binders are all
  callee specs or parameters (`PARAMS`). The roots are the proofs of kvnet and kvcheck (`ROOT_DIR`);
  the own proofs their binders reach are linked too.
- **A result's statement** is its proof's conclusion over its proof's parameters, unless `INST` gives
  it (binders and arguments): a proof generic in a model parameter that some callee proves only at a
  particular one is linked at that one (`Run`, `RunNode`, `Node.serve`, ...: at the store's
  `kvFacts γ (fun _ => True)`, `kvRep γ vs dir`, `kvConfRead`, `kvNodeStart γ vs dir`).
- **The application.** The proof applied to its explicit binders in order: a parameter the result
  also binds by that name is passed by name, any other `_` (Lean finds it by unification with the
  statement and the callees' types); a callee spec is given its result applied to one `_` per
  parameter of that result.
- **The callees' results**: the part's own (this file's), else the linked results of the Links of
  `EXT_LINKS` (raft-noax's `Link` and `Linked`, `durable`'s, lintest's and porcupine's, Perennial's),
  used as they are: a result of theirs with a hypothesis (until 2026-11-22, `durable`'s
  `h_errors_IsPathErrnoNotExist`; none today) makes it a hypothesis of every result that reaches it,
  `h_<name>`, in `section links_pending`.
  A spec no result proves is a hypothesis too.
- Instance binders are section variables (`SEC_VARS`, then the proofs' own `variable` lines'
  instances), all `include`d; `kdStorageModel` is the section's `StorageModel` (kvnet's storage is
  `KdStorage`'s registry, `[KdStor GF]`).

`--check` compares the output with the committed file.

**kvudp** (`etc/gen-link.py --kvudp`, 2026-11-24, `notes/kvudp-proof-plan.md`): the UDP transport's
proofs are the part's own proofs whose section has `[HasExt udpExt]`, and its pure helpers
(`UDP_PURE`): `is_udp`. `--kvnet` leaves them
out of its roots (their instances would make every kvnet result need the UDP extension, which kvnet's
`[netExt, fsExt]` lacks); `--kvudp` links them, with the own proofs they reach (kvnet's, linked again
under the UDP section's instances), into `KvNet/Proof/.../kvnet/cmd/kvudp/Link.lean`
(namespace `Perennial.EtcdGrove.kvudpLink`).
"""
import os
import re
import sys
import textwrap

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import link_bbolt  # noqa: E402

KVDIR = "github_com/mit_pdos/etcd_grove/examples/raft/kvnet"
OUT = "KvNet/Proof/" + KVDIR + "/Link.lean"
NS = "Perennial.EtcdGrove.kvnetLink"
ROOT_DIR = "KvNet/Proof/" + KVDIR
# the main tree's proofs the part's own proofs call (imported as they are, not copied)
MAIN_OWN = ["Proof/github_com/mit_pdos/gokv"]
# the main tree's specs the part imports (lintest's, porcupine's, gokv's): not all of `Spec/`, whose
# names-only `net` declares other names than the part's
MAIN_SPECS = ["Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest", "Spec/github_com/anishathalye",
              "Spec/github_com/mit_pdos/gokv"]
# the Links whose results are used as they are: (source file, module the part imports)
DUR = "github_com/mit_pdos/etcd_grove/examples/lib/durable"
EXT_LINKS = [
    ("RaftNoAx/Proof/go_etcd_io/raft/v3/Link.lean", "KvNet.Proof.go_etcd_io.raft.v3.Link"),
    ("RaftNoAx/Proof/go_etcd_io/raft/v3/Linked.lean", "KvNet.Proof.go_etcd_io.raft.v3.Linked"),
    ("WalTester/Proof/" + DUR + "/Link.lean", "KvNet.Proof." + DUR.replace("/", ".") + ".Link"),
    ("Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/Link.lean",
     "Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Link"),
    ("Proof/github_com/anishathalye/porcupine/Link.lean", "Proof.github_com.anishathalye.porcupine.Link"),
]
# explicit binder types a result may take as parameters
PARAMS = [r"KdNames", r"List w64", r"GoString", r"KvFacts GF", r"Loc → w64 → IProp GF",
          r"GoInterface → List w8 → IProp GF", r"List w8 → Prop", r"NodeStopper GF",
          r"w64 → GoString → github_com\.mit_pdos\.etcd_grove\.examples\.raft\.kvnet\.Options → "
          r"GMap w64 GoString → IProp GF"]
# the store's instantiation of the generic proofs (see the docstring)
_STORE_B = "(γ : KdNames) (vs : List w64) (dir : GoString)"
_STORE_3 = "(kvFacts γ (fun _ => True)) (kvRep γ vs dir) kvConfRead"
# (2026-11-24, G5) the node's specs take the incarnation stopper before the conf read
_STORE_4 = "(kvFacts γ (fun _ => True)) (kvRep γ vs dir) (kvStp γ vs dir) kvConfRead"
INST = {
    # (2026-11-24, kvudp) the UDP receiver and entry, linked as `Node.servePeer`'s callers and `Run`
    "Perennial.EtcdGrove.raft_kvnet.udpNet.receive.wp_proof": (_STORE_B, _STORE_3.replace(" kvConfRead", "") + " (kvStp γ vs dir)"),
    "Perennial.EtcdGrove.raft_kvnet.udpNet.stepper.wp_proof": (_STORE_B, _STORE_3.replace(" kvConfRead", "") + " (kvStp γ vs dir)"),
    "Perennial.EtcdGrove.raft_kvnet.RunUDP.wp_proof": (_STORE_B, _STORE_3 + " (kvNodeStart γ vs dir)"),
    "Perennial.EtcdGrove.raft_kvnet.RunNodeUDP.wp_proof": (_STORE_B, _STORE_3 + " (kvNodeStart γ vs dir)"),
    "Perennial.EtcdGrove.raft_kvnet.Node.handle.wp_proof": (_STORE_B, _STORE_4),
    "Perennial.EtcdGrove.raft_kvnet.Node.serveClient.wp_proof": (_STORE_B, _STORE_4),
    "Perennial.EtcdGrove.raft_kvnet.Node.serve.wp_proof": (_STORE_B, _STORE_4),
    "Perennial.EtcdGrove.raft_kvnet.Node.accept.wp_proof": (_STORE_B, _STORE_4),
    "Perennial.EtcdGrove.raft_kvnet.Run.wp_proof": (_STORE_B, _STORE_3 + " (kvNodeStart γ vs dir)"),
    "Perennial.EtcdGrove.raft_kvnet.RunNode.wp_proof": (_STORE_B, _STORE_3 + " (kvNodeStart γ vs dir)"),
}
SEC_VARS = """variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS] [KdStor GF]
variable [sem : go.Semantics]
"""
OWN_INSTS = {"GooseExts", "GooseSemantics", "GooseInterp", "HasExt netExt", "HasExt Net.netExt",
             "ExtSemantics Fs.fsExt", "Fs.FsSemOk", "HasExt Fs.fsExt", "ExtSemantics fsExt", "FsSemOk",
             "HasExt fsExt", "GoGlobalContext", "go.IntoValInj GoString", "go.BasicIntoValInj",
             "HeapGS HasLC.hasLC GF", "HeapGS hlc GF", "NetProtoGS", "Net.NetProtoGS", "KdStor GF",
             "StorageModel GF", "go.Semantics", "AllG GF"}
OPENS = ("open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode\n"
         "open Net go_etcd_io.raft.v3 Perennial.EtcdGrove.raft_kvnet Perennial.EtcdGrove.raft_kvcheck\n")
SPEC_RE = re.compile(r"\.(?:spec|apiSpec)[\w']*$")


def scan_file(path, mod, out, opens_of, vars_of):
    """Specs (`def`/`abbrev` named `….spec<S>`/`….apiSpec<S>`) and theorems of `path`."""
    s = link_bbolt.strip_comments(open(path, encoding="utf-8").read())
    opens_of[mod] = [o for line in re.findall(r"^open (.*)$", s, re.M) for o in line.split()
                     if not o.startswith("(")]
    vars_of[mod] = re.findall(r"^variable (.*)$", s, re.M)
    stack = []
    for m in link_bbolt.DECL.finditer(s):
        kw, name = m.group(1), m.group(3)
        if kw == "namespace":
            stack.extend(("ns", c) for c in name.split("."))
        elif kw == "section":
            stack.append(("sec", name))
        elif kw == "end":
            if stack:
                k = len(name.split(".")) if name and stack[-1][0] == "ns" else 1
                del stack[len(stack) - k:]
        else:
            kind = m.group(2)
            ns = ".".join(c for t, c in stack if t == "ns")
            full = name[len("_root_."):] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
            if kind in ("abbrev", "def") and not SPEC_RE.search(full):
                continue
            parts, concl = link_bbolt.split_decl(s, m.end())
            out.append(dict(mod=mod, kind=kind, name=full, ns=ns, hyps=parts, concl=" ".join(concl.split())))


def walk(base, prefix, out, opens_of, vars_of, skip=(), keep=lambda rel: True):
    if not os.path.isdir(base):
        return
    for dp, dns, fs in os.walk(base):
        dns.sort()
        rel = os.path.relpath(dp, base)
        if any((rel + os.sep).startswith(k + os.sep) for k in skip):
            dns[:] = []
            continue
        for f in sorted(fs):
            if f.endswith(".lean") and keep(os.path.relpath(os.path.join(dp, f), base)):
                p = os.path.join(dp, f)
                mod = prefix + os.path.relpath(p, base)[:-5].replace(os.sep, ".")
                scan_file(p, mod, out, opens_of, vars_of)


NAMED = re.compile(r"\((GF|hG|hlc) := [\w.]+\)$")


def parse_app(ty):
    ts = link_bbolt_toks(ty.strip())
    if not ts or not re.fullmatch(r"(?:_root_\.)?[\w.«»']+\.(?:spec|apiSpec)[\w']*", ts[0]):
        return None
    return ts[0], [t for t in ts[1:] if NAMED.fullmatch(t)], [t for t in ts[1:] if not NAMED.fullmatch(t)]


def link_bbolt_toks(s):
    out, cur, depth = [], "", 0
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


# kvudp's pure helpers (no UDP instance in their sections): linked with kvudp's, not kvnet's
UDP_PURE = {"putUint32", "putHeader", "putFragment", "putAck", "fragments", "parseAddr"}
OUT_UDP = "KvNet/Proof/" + KVDIR + "/cmd/kvudp/Link.lean"
NS_UDP = "Perennial.EtcdGrove.kvudpLink"


def main(root, perennial, argv0, check=False, udp=False):
    global OUT, NS
    if udp:
        OUT, NS = OUT_UDP, NS_UDP
    flag = "--kvudp" if udp else "--kvnet"
    decls, opens_of, vars_of = [], {}, {}
    # specs: the part's, the main tree's, Perennial's
    walk(os.path.join(root, "KvNet", "Spec"), "KvNet.Spec.", decls, opens_of, vars_of)
    walk(os.path.join(root, "KvNet", "Proof"), "KvNet.Proof.", decls, opens_of, vars_of)
    # `net`'s proofs: the part `Net/`'s (copied into the part when the Link imports them)
    walk(os.path.join(root, "Net", "Proof", "net"), "KvNet.Proof.net.", decls, opens_of, vars_of,
         keep=lambda rel: not os.path.exists(os.path.join(root, "KvNet", "Proof", "net", rel)))
    for d in MAIN_SPECS:
        walk(os.path.join(root, d), d.replace("/", ".") + ".", decls, opens_of, vars_of)
    for d in MAIN_OWN:
        walk(os.path.join(root, d), d.replace("/", ".") + ".", decls, opens_of, vars_of)
    walk(os.path.join(perennial, "Perennial", "Spec"), "Perennial.Spec.", decls, opens_of, vars_of)
    ext_decls = []
    for src, mod in EXT_LINKS:
        scan_file(os.path.join(root, src), mod, ext_decls, opens_of, vars_of)
    for dp, dns, fs in os.walk(os.path.join(perennial, "Perennial", "Proof")):
        dns.sort()
        if "Link.lean" in fs:
            p = os.path.join(dp, "Link.lean")
            mod = "Perennial.Proof." + os.path.relpath(p, os.path.join(perennial, "Perennial", "Proof"))[:-5] \
                .replace(os.sep, ".")
            scan_file(p, mod, ext_decls, opens_of, vars_of)
    specs = set()
    for x in decls + ext_decls:
        if x["kind"] in ("abbrev", "def"):
            specs.add(x["name"])

    def resolve(a, x):
        if a.startswith("_root_."):
            return a[7:] if a[7:] in specs else None
        parts = x["ns"].split(".") if x["ns"] else []
        for k in range(len(parts), -1, -1):
            pre = parts[:k]
            for o in [""] + opens_of.get(x["mod"], []):
                c = ".".join(pre + ([o] if o else []) + [a])
                if c in specs:
                    return c
        for o in opens_of.get(x["mod"], []):  # an open of a full name
            c = o + "." + a
            if c in specs:
                return c
        return None

    def binders(x):
        """[('param', name, ty) | ('spec', name, spec)] or None (not a result)."""
        out = []
        for h in x["hyps"]:
            if h.startswith(("{", "⦃", "[")):
                continue
            m = re.match(r"\(\s*([\w'γ]+(?:\s+[\w'γ]+)*)\s*:\s*(.*)\)$", h, re.S)
            if not m:
                return None
            names, ty = m.group(1).split(), " ".join(m.group(2).split())
            app = parse_app(ty)
            for n in names:
                if app:
                    r = resolve(app[0], x)
                    if not r:
                        return None
                    out.append(("spec", n, r))
                elif any(re.fullmatch(p, ty) for p in PARAMS):
                    out.append(("param", n, ty))
                else:
                    return None
        return out

    def concl(x):
        app = parse_app(x["concl"])
        if not app:
            return None
        r = resolve(app[0], x)
        return (r, app[1], app[2]) if r else None

    # the external results: spec -> (term, nparams, hyps [(name, type)], module)
    ext = {}
    for x in ext_decls:
        if x["kind"] != "theorem":
            continue
        c = concl(x)
        if not c or c[0] in ext:
            continue
        nparams, hyps = 0, []
        for h in x["hyps"]:
            if h.startswith(("{", "⦃", "[")):
                continue
            m = re.match(r"\(\s*([\w']+)\s*:\s*(.*)\)$", h, re.S)
            if m and m.group(1).startswith("h_"):
                hyps.append((m.group(1), " ".join(m.group(2).split())))
            else:
                nparams += 1
        ext[c[0]] = ("_root_." + x["name"], nparams, hyps, x["mod"])

    # the own proofs: spec -> proof (the `wp_proof<S>` matching the spec's suffix first)
    own = {}
    for x in decls:
        if x["kind"] != "theorem" or not re.search(r"\.wp_proof[\w']*$", x["name"]):
            continue
        if x["mod"].startswith("KvNet.Proof.go_etcd_io.raft."):
            continue
        if not (x["mod"].startswith("KvNet.Proof.") or x["mod"].startswith(tuple(
                d.replace("/", ".") + "." for d in MAIN_OWN))):
            continue
        c, bs = concl(x), binders(x)
        if not c or bs is None:
            continue
        x["spec"], x["named"], x["args"], x["binders"] = c[0], c[1], c[2], bs
        suf = re.search(r"\.wp_proof([\w']*)$", x["name"]).group(1)
        good = re.search(r"\.(?:spec|apiSpec)" + re.escape(suf) + "$", c[0]) is not None
        if c[0] not in own or (good and not own[c[0]]["good"]):
            x["good"] = good
            own[c[0]] = x

    rootmod = ROOT_DIR.replace("/", ".")
    order, seen, missing = [], set(), set()

    def visit(s):
        if s in seen:
            return
        seen.add(s)
        x = own[s]
        for b in x["binders"]:
            if b[0] == "spec":
                if b[2] in own:
                    visit(b[2])
                elif b[2] not in ext:
                    missing.add(b[2])
        order.append(s)

    def is_udp(mod):
        return any("HasExt udpExt" in line for line in vars_of.get(mod, [])) or \
            mod.rsplit(".", 1)[-1] in UDP_PURE

    for s in sorted(own, key=lambda s: own[s]["name"]):
        if own[s]["mod"].startswith(rootmod + ".") and is_udp(own[s]["mod"]) == udp:
            visit(s)

    def rname(x):
        n = x["name"]
        n = n[len("Perennial.EtcdGrove."):] if n.startswith("Perennial.EtcdGrove.") else (
            n[len("Perennial."):] if n.startswith("Perennial.") else n)
        pre, m, suf = re.fullmatch(r"(.*)\.(\w+)\.wp_proof([\w']*)", n).groups()
        return f"{pre}.wp_{m}{suf}"

    def rbinders(x):
        if x["name"] in INST:
            return INST[x["name"]][0]
        return " ".join(f"({b[1]} : {b[2]})" for b in x["binders"] if b[0] == "param")

    def nparams_of(x):
        return len(re.findall(r"\(([^():]*):", rbinders(x))) and sum(
            len(g.split()) for g in re.findall(r"\(([^():]*):", rbinders(x)))

    def rparam_names(x):
        return set(n for g in re.findall(r"\(([^():]*):", rbinders(x)) for n in g.split())

    # hypotheses each result reaches (external results' and unproved specs)
    hyps_of = {}
    for s in order:
        x, hs = own[s], {}
        for b in x["binders"]:
            if b[0] != "spec":
                continue
            if b[2] in own:
                hs.update(hyps_of[b[2]])
            elif b[2] in ext:
                for n, t in ext[b[2]][2]:
                    hs[n] = t
            else:
                n = "h_" + "_".join(re.sub(r"^Perennial\.(EtcdGrove\.)?", "", b[2]).split(".")[:-1])
                hs[n] = "_root_." + b[2] + " (GF := GF) (hG := hG)"
        hyps_of[s] = hs

    def term(s, caller):
        if s in own:
            y = own[s]
            t = "_root_." + NS + "." + rname(y)
            n = nparams_of(y)
            hs = hyps_of[s]
        elif s in ext:
            t, n, hl, _ = ext[s]
            hs = dict(hl)
        else:
            return "h_" + "_".join(re.sub(r"^Perennial\.(EtcdGrove\.)?", "", s).split(".")[:-1])
        args = ["_"] * n + sorted(hs)
        return f"({t} {' '.join(args)})" if args else t

    def emit(s):
        x = own[s]
        names = rparam_names(x)
        app = []
        for b in x["binders"]:
            if b[0] == "param":
                app.append(b[1] if b[1] in names and x["name"] not in INST else "_")
            else:
                app.append(term(b[2], x))
        args = INST[x["name"]][1] if x["name"] in INST else " ".join(x["args"])
        hb = "".join(f"\n    ({n} : {t})" for n, t in sorted(hyps_of[s].items()))
        bs = rbinders(x)
        stmt = f"_root_.{s} {' '.join(x['named'])}" + (f" {args}" if args else "")
        body = textwrap.fill(f"_root_.{x['name']} " + " ".join(app), 100, initial_indent="  ",
                             subsequent_indent="    ", break_on_hyphens=False, break_long_words=False)
        return (f"theorem {rname(x)}" + (f" {bs}" if bs else "") + hb + f" :\n    {stmt} :=\n{body}\n")

    # instances: the proofs' own `variable` lines'
    insts = []
    ext_used = []
    for s in order:
        for b in own[s]["binders"]:
            if b[0] == "spec" and b[2] not in own and b[2] in ext and ext[b[2]][3] not in ext_used:
                ext_used.append(ext[b[2]][3])
    for mod in [own[s]["mod"] for s in order] + ext_used:
        for line in vars_of.get(mod, []):
            for g in re.findall(r"\[([^\[\]]*)\]", line):
                ty = g.split(":", 1)[1].strip() if re.match(r"\s*[\w']+\s*:", g) else g.strip()
                if ty not in OWN_INSTS and ty not in insts and not re.search(r"\bhlc\b", ty):
                    insts.append(ty)
    imports = set(own[s]["mod"] for s in order)
    for s in order:
        for b in own[s]["binders"]:
            if b[0] == "spec" and b[2] not in own and b[2] in ext:
                imports.add(ext[b[2]][3])
    imports.add("KvNet.Proof." + KVDIR.replace("/", ".") + ".KdStorage")
    closed = [s for s in order if not hyps_of[s]]
    pend = sorted(set(n for s in order for n in hyps_of[s]))
    what = ("kvudp's UDP transport's proofs (`notes/kvudp-proof-plan.md`) and the kvnet proofs they reach"
            if udp else "kvnet's and kvcheck's proofs")
    head = ("/-\n" + textwrap.fill(
        what + " (the part `KvNet/`, `notes/kvnet-part.md`), every proof applied to its "
        "callees' results: the part's own, and raft-noax's, `durable`'s, lintest's, porcupine's and "
        "Perennial's linked results (their `Link.lean`s, used as they are). The callees are read off each "
        "proof's binders; a proof generic in kvnet's model parameters is linked at the store's "
        f"(`etc/link_kvnet.py`'s docstring). Generated by `etc/gen-link.py {flag}` -- do not edit by hand.",
        100, break_on_hyphens=False) + "\n\n" + textwrap.fill(
        f"{len(order)} results, {len(closed)} of them with no hypothesis. The others take, as hypotheses, "
        "the specs no result proves and the hypotheses of the linked results they use: "
        + (", ".join(f"`{n}`" for n in pend) or "none") + ".", 100, break_on_hyphens=False)
        + "\n\n`#print axioms` on a result is its trust base.\n-/")
    _unused_head = ("/-\n" + textwrap.fill(
        "kvnet's and kvcheck's proofs (the part `KvNet/`, `notes/kvnet-part.md`), every proof applied to its "
        "callees' results: the part's own, and raft-noax's, `durable`'s, lintest's, porcupine's and "
        "Perennial's linked results (their `Link.lean`s, used as they are). The callees are read off each "
        "proof's binders; a proof generic in kvnet's model parameters is linked at the store's "
        "(`etc/link_kvnet.py`'s docstring). Generated by `etc/gen-link.py --kvnet` -- do not edit by hand.",
        100, break_on_hyphens=False) + "\n\n" + textwrap.fill(
        f"{len(order)} results, {len(closed)} of them with no hypothesis. The others take, as hypotheses, "
        "the specs no result proves and the hypotheses of the linked results they use: "
        + (", ".join(f"`{n}`" for n in pend) or "none") + ".", 100, break_on_hyphens=False)
        + "\n\n`#print axioms` on a result is its trust base.\n-/")
    sec = SEC_VARS + "".join(f"variable [{c}]\n" for c in insts)
    out = [head, "module", ""]
    out.extend(f"public import {m}" for m in sorted(imports))
    out.append(f"""
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace {NS}

{OPENS.replace(" Perennial.EtcdGrove.raft_kvcheck", "") + "open Udp\n" if udp else OPENS}
attribute [local instance] raft_kvnet.kdStorageModel
""")
    out.append("section links\n" + sec)
    out.extend(emit(s) for s in order if not hyps_of[s])
    out.append("end links\n")
    out.append("section links_pending\n" + sec)
    out.extend(emit(s) for s in order if hyps_of[s])
    out.append("end links_pending\n")
    out.append(f"end {NS}")
    text = "\n".join(out) + "\n"
    if missing:
        print(f"gen-link.py {flag}: specs with no result (hypotheses): " + ", ".join(sorted(missing)),
              file=sys.stderr)
    rej = [x["name"] for x in decls if x["kind"] == "theorem" and re.search(r"\.wp_proof([A-Z][\w']*)?$", x["name"])
           and x["mod"].startswith(rootmod + ".") and x.get("spec") is None]
    if rej:
        print(f"gen-link.py {flag}: root proofs not linked (a binder of no known kind): "
              + ", ".join(sorted(rej)), file=sys.stderr)
    if check:
        p = os.path.join(root, OUT)
        cur = open(p, encoding="utf-8").read() if os.path.exists(p) else ""
        if cur != text:
            print(f"gen-link.py {flag}: {OUT} differs from the generated file", file=sys.stderr)
            sys.exit(1)
        return
    sys.stdout.write(text)
