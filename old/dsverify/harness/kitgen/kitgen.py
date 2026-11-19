#!/usr/bin/env python3
"""kitgen: generate a kit's configuration-dependent files from its kit.toml (kit v2,
notes/kit-v2.md decisions 3, 5 and 7).

Usage:
  kitgen.py KITDIR [--tree TREE]            write the generated files
  kitgen.py KITDIR [--tree TREE] --check    exit 1 unless every generated file is current
  kitgen.py KITDIR [--tree TREE] --audit    print what a person must read, with line counts

KITDIR holds kit.toml. TREE is the target's work tree (the fork with the kit's patches applied);
default: the manifest's [target].dev, relative to the lab. Generated files carry a header saying
so; they are regenerated, never edited.

Into TREE (Go, the rig, goose):
  <test.pkg>/kit_gen.go   the configuration constants, Addrs() and Main (one driver.Run call)
  <cmd>/client/main.go    the client node's command (Main); <cmd> is test.cmd (default "cmd")
  <cmd>/server/main.go    the server nodes' command (node DSRIG_ID runs its function)
  rig.toml                the rig's config (module ".")
  goose.sh                goose + proofgen + typecheck of the target's packages
  with [rpc] (notes/craq-net.md): <test.pkg>/rpc_gen.go (the net/rpc model's codec),
  rpc_model_gen.go / rpc_real_gen.go (registerRPC, model and real builds), rpc_gen_test.go (the
  codec's claims against real gob and net/rpc's reflection); goose.sh then translates through
  a GOROOT with the models of net/rpc and net/http (harness/rpcmodel/goroot.sh)
  with [json] (notes/vsr-net.md): <test.pkg>/json_gen.go (the encoding/json model's codec),
  json_extra_gen.go (unnamed types, outside goose), json_model_gen.go / json_real_gen.go
  (registerJSON), json_gen_test.go (the codec's claims against real encoding/json)
Into KITDIR/gen (Lean):
  lean/<P>Spec.lean       the statement's plumbing: addresses, the DriverKit, nodes, NetConfig,
                          WellFormed by decide, <P>SpecHolds
  lean/<P>Main.lean       the per-kit residue: DriverMainFacts by fixed scripts, the goal from
                          the generic lemma (driver_dist_safe)
  Goal.lean               the run's goal (goal_spec is sorry)
  GoalCheck.lean          the final check's file
"""

import argparse
import fnmatch
import glob
import os
import re
import subprocess
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rpcgen  # noqa: E402
import jsongen  # noqa: E402
import pbgen  # noqa: E402

LAB = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
RIG_SUBNET = "10.77.0."      # node i is 10.77.0.(10+i) under the rig (harness/rig/rig.py)
RIG_BASE = 10

# The harness's models and checkers a kit may name (test.model). Each: the Go check function
# Main passes to the driver, the Lean model, encodings, checker lemma and its module.
CHECKERS = {
    "writeonce": {
        "go_import": "dsverify.lab/harness/check",
        "go_check": "check.WriteOnce",
        "lean_check": "dsverify_lab.harness.check.WriteOnce",
        "lean_check_pkg": "pkg_id.dsverify_lab.harness.check",
        "model": "writeOnce GoString",
        "encI": "encStr",
        "encO": "encStr",
        "checker_fn": "writeOnce_checker_fn",
        "lean_import": "Harness.WriteOnceChecker",
        # the prompt's description of the check (gen_prompt)
        "desc": "check.WriteOnce (every returned value is the same, and was proposed no later "
                "than the first return)",
    },
    # the key-value map over string keys and values: Gen returns models.KvIn{Put, K, V}, Op returns
    # models.KvOut (Get: {KvGot, found, v}; Put: {KvDone, false, ""}); the input premise is over
    # Lean's KvInput GoString GoString (`.get k`, `.put k v`)
    "kv": {
        "go_import": "dsverify.lab/harness/check",
        "go_check": "check.KV",
        "lean_check": "dsverify_lab.harness.check.KV",
        "lean_check_pkg": "pkg_id.dsverify_lab.harness.check",
        "model": "kv GoString GoString",
        "encI": "encKvIn",
        "encO": "encKvOut",
        "checker_fn": "kv_checker_fn",
        "lean_import": "Harness.Models",
        # the trusted claim the checker rests on (kitgen --audit)
        "trusted": ("harness/lean/Harness/Porcupine.lean", "CheckOperations.wp_proof",
                    "porcupine's checker spec (an axiom): CheckOperations returns true on a "
                    "linearizable history"),
        "desc": "check.KV (porcupine's linearizability check against the harness's key-value model: "
                "puts and gets of string keys and values; a get of a key never put finds nothing)",
    },
    # the key-value map with range scan over uint64 keys and string values (SwiftPaxos's state
    # machine; kits/epaxos-net-stage2): Gen returns models.KvsIn{Op, K, N, V} (Op KvsGet, KvsPut or
    # KvsScan; Scan(K, N) reads keys K..K+N), Op returns models.KvsOut (Get: {KvsGot, found, v};
    # Put: {KvsDone, false, ""}; Scan: {KvsScanned, false, the values in key order, concatenated});
    # the input premise is over Lean's KvsInput GoString (`.get k`, `.put k v`, `.scan k n`, keys
    # and n w64)
    "kvscan": {
        "go_import": "dsverify.lab/harness/check",
        "go_check": "check.KVScan",
        "lean_check": "dsverify_lab.harness.check.KVScan",
        "lean_check_pkg": "pkg_id.dsverify_lab.harness.check",
        "model": "kvScan w8",
        "encI": "encKvsIn",
        "encO": "encKvsOut",
        "checker_fn": "kvScan_checker_fn",
        "lean_import": "Harness.ModelsScan",
        "trusted": ("harness/lean/Harness/Porcupine.lean", "CheckOperations.wp_proof",
                    "porcupine's checker spec (an axiom): CheckOperations returns true on a "
                    "linearizable history"),
        "desc": "check.KVScan (porcupine's linearizability check against the harness's key-value "
                "model with range scan: puts and gets of uint64 keys and string values, and scans "
                "Scan(k, n), which return the values of the keys k..k+n that were put, in key "
                "order, concatenated; a get of a key never put finds nothing)",
    },
    # the int64 register, initially 0, whose compare-and-swap does not report its outcome (Gryff's
    # RMW reply; kits/gryff-net): Gen returns models.CasRegIn{Op, A, B} (Op CasRegRead,
    # CasRegWrite or CasRegCAS; CAS(A, B) sets B if the value is A), Op returns models.CasRegOut
    # (Read: {CasRegValue, v}; Write and CAS: {CasRegDone, 0}); the input premise is over Lean's
    # RegInput w64 (`.read`, `.write v`, `.cas a b`)
    "casreg": {
        "go_import": "dsverify.lab/harness/check",
        "go_check": "check.CasRegister",
        "lean_check": "dsverify_lab.harness.check.CasRegister",
        "lean_check_pkg": "pkg_id.dsverify_lab.harness.check",
        "model": "casRegister w64 (W64 0)",
        "encI": "encCasRegIn",
        "encO": "encCasRegOut",
        "checker_fn": "casRegister_checker_fn",
        "lean_import": "Harness.ModelsCas",
        "trusted": ("harness/lean/Harness/Porcupine.lean", "CheckOperations.wp_proof",
                    "porcupine's checker spec (an axiom): CheckOperations returns true on a "
                    "linearizable history"),
        "desc": "check.CasRegister (porcupine's linearizability check against the harness's model of "
                "an int64 register, initially 0, with reads, writes and compare-and-swaps; a "
                "compare-and-swap's output is only its completion, since Gryff's reply does not say "
                "whether it swapped)",
    },
}

# The net model's proved specs, offered to every statement.
NET_IMPORTS = [
    "Harness.NetLib", "Harness.Proof.log",
    "Harness.Proof.net.Listen", "Harness.Proof.net.Dial", "Harness.Proof.net.DialTimeout",
    "Harness.Proof.net.TCPListener__Accept", "Harness.Proof.net.TCPListener__Close",
    "Harness.Proof.net.TCPListener__Addr", "Harness.Proof.net.TCPConn__Read",
    "Harness.Proof.net.TCPConn__Write", "Harness.Proof.net.TCPConn__Close",
    "Harness.Proof.net.TCPConn__SetDeadline", "Harness.Proof.net.TCPConn__SetReadDeadline",
    "Harness.Proof.net.TCPConn__SetWriteDeadline", "Harness.Proof.net.TCPConn__LocalAddr",
    "Harness.Proof.net.TCPConn__RemoteAddr", "Harness.Proof.net.initialize",
]

# The specs of the net/rpc and net/http models (harness/rpcmodel; proved once in the harness),
# offered to a statement whose kit has [rpc]; they define the models' isPkgInit.
RPC_IMPORTS = ["Harness.Proof.net.http.initialize", "Harness.Proof.net.rpc.initialize"]

INSTANCES = ("netConnExts netConnExtsSemantics netConnExtsInterp\n"
             "  GooseGlobalGS.gooseInvGS netConnExts_has")


def die(msg):
    sys.exit(f"kitgen: {msg}")


# ---------------------------------------------------------------------------------------------
# The manifest


class Kit:
    def __init__(self, kitdir):
        self.dir = os.path.abspath(kitdir)
        self.toml_path = os.path.join(self.dir, "kit.toml")
        with open(self.toml_path, "rb") as fp:
            self.c = tomllib.load(fp)
        c = self.c
        for sec in ("target", "test", "node", "lean"):
            if sec not in c:
                die(f"{self.toml_path}: no [{sec}]")
        self.name = c["name"]
        self.module = c["target"]["module"]
        t = c["test"]
        self.test = t
        self.pkg_rel = t["pkg"].strip("/")
        self.pkg_path = f"{self.module}/{self.pkg_rel}"
        self.go_name = t["go_name"]
        # where the node commands go (a target with its own cmd/client names another directory)
        self.cmd = t.get("cmd", "cmd").strip("/")
        if not re.fullmatch(r"[\w-]+(/[\w-]+)*", self.cmd):
            die(f"test.cmd = {self.cmd!r}: a relative directory")
        if t["model"] not in CHECKERS:
            die(f"test.model {t['model']!r}: the harness has {sorted(CHECKERS)}")
        self.chk = CHECKERS[t["model"]]
        for f in ("new", "op", "gen", "start"):
            if not re.fullmatch(r"[A-Z]\w*", t[f]):
                die(f"test.{f} = {t[f]!r} is not an exported Go function name")
        self.nC, self.k, self.waitMs = int(t["nC"]), int(t["k"]), int(t["waitMs"])
        if not (0 < self.nC < 2 ** 32 and self.k >= 0 and self.nC * self.k < 2 ** 61
                and 0 <= self.waitMs < 2 ** 63 // 10 ** 6):
            die("test.nC, k, waitMs out of the driver's range (nC < 2^32, nC*k < 2^61)")
        self.consts = t.get("consts", {})
        reserved = {"NC", "K", "WaitMs", "Addrs", "Main"}
        for n, v in self.consts.items():
            if n in reserved or not re.fullmatch(r"[A-Z]\w*", n) or not isinstance(v, int) \
                    or not 0 <= v < 2 ** 64:
                die(f"test.consts.{n}: an exported name other than {sorted(reserved)}, a uint64")
        self.nodes = c["node"]
        if not self.nodes or self.nodes[0].get("role") != "client":
            die("node 0 must be the client node (role = \"client\")")
        for i, nd in enumerate(self.nodes):
            if i > 0:
                if nd.get("role", "server") != "server" or not re.fullmatch(r"[A-Z]\w*", nd["func"]):
                    die(f"node {i}: a server node runs an exported function of the test package")
                for a in nd.get("args", []):
                    if not isinstance(a, int) or not 0 <= a < 2 ** 64:
                        die(f"node {i}: arguments are uint64 constants")
            # a node's ports: `port`, or `ports` (several: the node listens on each; the first is
            # its address in Addrs())
            if ("port" in nd) == ("ports" in nd):
                die(f"node {i}: one of port, ports")
            ports = nd["ports"] if "ports" in nd else [nd["port"]]
            if not ports or not all(isinstance(p, int) and 0 < p < 65536 for p in ports):
                die(f"node {i}: ports")
            nd["_ports"] = ports
        # Addrs(): node i's (first) address; the configured endpoints: every port of every node
        self.addrs = [f"{RIG_SUBNET}{RIG_BASE + i}:{nd['_ports'][0]}" for i, nd in enumerate(self.nodes)]
        self.node_addrs = [[f"{RIG_SUBNET}{RIG_BASE + i}:{p}" for p in nd["_ports"]]
                           for i, nd in enumerate(self.nodes)]
        self.all_addrs = [a for na in self.node_addrs for a in na]
        self.multiport = any(len(na) > 1 for na in self.node_addrs)
        if len(set(self.all_addrs)) != len(self.all_addrs):
            die("an endpoint twice")
        lean = c["lean"]
        self.lean = lean
        self.root = lean["root"]
        self.ns = lean["namespace"]
        self.prefix = lean["prefix"]
        self.timeout = c.get("rig", {}).get("timeout", 60)
        # an on-link default route in each node's namespace (rig) and on lo (the node test)
        self.default_route = bool(c.get("rig", {}).get("default_route", False))
        self.rpc = None
        if "rpc" in c:
            try:
                self.rpc = rpcgen.Types(c["rpc"])
            except rpcgen.RpcError as e:
                die(f"[rpc]: {e}")
        self.json = None
        if "json" in c:
            try:
                self.json = jsongen.Types(c["json"])
            except jsongen.JsonError as e:
                die(f"[json]: {e}")
            if "encoding/json" not in lean.get("harness_pkgs", []):
                die("[json]: lean.harness_pkgs needs encoding/json (the model, translated in the harness)")
        # [protobuf] (notes/grpc-model.md): the protobuf model's codec for the listed messages
        self.protobuf = None
        if "protobuf" in c:
            try:
                self.protobuf = pbgen.Messages(c["protobuf"])
            except pbgen.PbError as e:
                die(f"[protobuf]: {e}")
        for p in c["target"].get("patch", []):
            if p.get("adapter") and p.get("proved"):
                die(f"patch {p['file']}: adapter (trusted) or proved (by the run), not both")
        for gone in ("pkg_init_true", "pkg_init_errors"):
            if gone in lean:
                die(f"lean.{gone}: removed; the run chooses every package's package-level state "
                    "(the statement's PkgState class), only lean.pkg_init_order is given")
        self.pkg_init_order = lean.get("pkg_init_order")
        if not self.pkg_init_order or self.pkg_init_order[-1] != self.pkg_path:
            die("lean.pkg_init_order: every translated package of the target, imports first, "
                "the test package last")
        # [model_build] (notes/grpc-model.md, notes/quepaxa-net.md): modules the model build replaces
        # by the lab's models (go.model.mod, generated from the fork's go.mod); goose.sh and the
        # kit's test commands build with it
        self.model_build = c.get("model_build")
        if self.model_build is not None:
            mb = self.model_build
            for k in mb:
                if k not in ("replace", "require", "tags"):
                    die(f"[model_build].{k}: unknown (replace, require, tags)")
            if not mb.get("replace") or not all(
                    re.fullmatch(r"[\w./-]+", m) and re.fullmatch(r"[\w./-]+", p) and not p.startswith("/")
                    for m, p in mb["replace"].items()):
                die("[model_build].replace: module = path under the harness (from the go.mod's "
                    "replace of dsverify.lab/harness)")
            if not all(re.fullmatch(r"[\w./-]+ v[\w.+-]+", r) for r in mb.get("require", [])):
                die("[model_build].require: \"module version\" strings")
            if not all(re.fullmatch(r"\w+", t) for t in mb.get("tags", [])):
                die("[model_build].tags: build tags")
        # lean.extra_assumptions: [module, class] pairs, the harness's goose translations of library
        # functions Perennial's pinned translation has as names only (io_extra's kind:
        # Harness/Code/<pkg>_extra.lean, a class <pkg>.ExtraAssumptions), added to every node's
        # assumptions and to the statement's imports. lean.io_extra = true is
        # ["Harness.Code.io_extra", "io.ExtraAssumptions"].
        self.extras = []
        if lean.get("io_extra", False):
            self.extras.append(("Harness.Code.io_extra", "io.ExtraAssumptions"))
        for e in lean.get("extra_assumptions", []):
            if not (isinstance(e, list) and len(e) == 2 and re.fullmatch(r"Harness\.Code\.\w+", e[0])
                    and re.fullmatch(r"[\w.]+\.ExtraAssumptions", e[1])):
                die(f"lean.extra_assumptions {e!r}: [\"Harness.Code.<pkg>_extra\", \"<pkg>.ExtraAssumptions\"]")
            if tuple(e) not in self.extras:
                self.extras.append(tuple(e))
        # lean.trusted_init: packages translated with a goose config whose initialization (init
        # functions, package variables' initializers) is a trusted no-op, as protoc-gen-go's
        # descriptor registration (notes/grpc-model.md decision 9) or a names-only library: kitgen
        # writes the config into goose.sh and the TrustedCode (and empty ManualProof) Lean files
        # into gen/lean/<root>/, which the seed makes fixed files
        self.trusted_init = lean.get("trusted_init", {})
        for p, t in self.trusted_init.items():
            if p not in lean["goose_pkgs"]:
                die(f"lean.trusted_init {p!r}: a package of lean.goose_pkgs")
            if p in lean.get("names_only", {}):
                die(f"lean.trusted_init {p!r}: also in lean.names_only (one goose config per package)")
            for k in t:
                if k not in ("translate", "imports", "inits", "vars", "names"):
                    die(f"lean.trusted_init {p!r}.{k}: unknown (translate, imports, inits, vars, names)")
            if not t.get("inits") and not t.get("vars"):
                die(f"lean.trusted_init {p!r}: no inits or vars")
            if not all(re.fullmatch(r"init\.\d+", x) for x in t.get("inits", [])) or \
                    not all(re.fullmatch(r"\w+", x) for x in t.get("vars", []) + t.get("names", [])):
                die(f"lean.trusted_init {p!r}: inits are init.N, vars and names package variables (or _)")
            tr = t.get("translate", ["!*"])
            for x in t.get("inits", []) + t.get("vars", []) + t.get("names", []):
                # goose translates a trusted name that translate also covers (notes/grpc-model.md 9)
                pos = any(not q.startswith("!") and fnmatch.fnmatchcase(x, q) for q in tr)
                neg = any(q.startswith("!") and fnmatch.fnmatchcase(x, q[1:]) for q in tr)
                if pos and not neg:
                    die(f"lean.trusted_init {p!r}: {x} is trusted, exclude it from translate (\"!{x}\")")
        # [checks] (harness/rig/kitcheck.py; kits/README.md section 6): the kit's smoke, vacuity and
        # coverage checks; nothing is generated from it
        self.checks = c.get("checks", {})
        ck = self.checks
        known = {"smoke_runs": int, "smoke_jobs": int, "deploy_test": str, "deploy_env": dict,
                 "deploy_timeout": int, "vacuity_build": str, "vacuity_cap": int, "caught": str,
                 "cover_pkgs": list, "cover_files": list, "cover_funcs": list, "count": list, "plant": list}
        for k, v in ck.items():
            if k not in known:
                die(f"[checks].{k}: unknown (known: {sorted(known)})")
            if not isinstance(v, known[k]):
                die(f"[checks].{k}: not a {known[k].__name__}")
        if ck.get("vacuity_build", "model") not in ("real", "model"):
            die("[checks].vacuity_build: real or model")
        for x in ck.get("count", []):
            if set(x) - {"label", "pattern", "nodes"} or not x.get("label") or not x.get("pattern") \
                    or x.get("nodes", "client") not in ("client", "servers"):
                die(f"[[checks.count]] {x!r}: label, pattern, nodes = client or servers")
        names = set()
        for p in ck.get("plant", []):
            if set(p) - {"name", "why", "patch", "rewrite"} or not re.fullmatch(r"[\w-]+", p.get("name", "")) \
                    or ("patch" in p) == ("rewrite" in p) or not p.get("why"):
                die(f"[[checks.plant]] {p!r}: name, why, and one of patch, rewrite")
            if p["name"] in names:
                die(f"[[checks.plant]] {p['name']}: twice")
            names.add(p["name"])
            f = p.get("patch") or p.get("rewrite")
            if not os.path.isfile(os.path.join(self.dir, f)):
                die(f"[[checks.plant]] {p['name']}: no {f} in the kit")

    def tree_default(self):
        return os.path.join(LAB, self.c["target"]["dev"])


def lean_ns(path):
    """A Go package path as goose's Lean namespace: github.com/x/y -> github_com.x.y."""
    return ".".join(p.replace(".", "_").replace("-", "_") for p in path.split("/"))


def go_string_list(addrs, indent):
    return "".join(f'{indent}"{a}",\n' for a in addrs)


# ---------------------------------------------------------------------------------------------
# Go


def gen_go_header(kit, what):
    return (f"// Code generated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml. "
            f"DO NOT EDIT.\n\n// {what}\n")


def gen_kit_gen_go(kit):
    consts = [("NC", kit.nC), ("K", kit.k), ("WaitMs", kit.waitMs)] + list(kit.consts.items())
    w = max(len(n) for n, _ in consts)
    cl = "".join(f"\t{n.ljust(w)} uint64 = {v}\n" for n, v in consts)
    # the harness packages the extra assumptions' glue calls (EXTRA_GO_IMPORTS): imported for their
    # initialization only
    blank = "".join(f"\n\t// {m}'s model (its package state; lean.extra_assumptions)\n\t_ \"{EXTRA_GO_IMPORTS[m]}\"\n"
                    for m, _ in kit.extras if m in EXTRA_GO_IMPORTS)
    return (gen_go_header(kit, f"The configuration of {kit.name} (kit.toml) and the client node's "
                          "program.") +
            f"\npackage {kit.go_name}\n\n"
            "import (\n"
            f"\t\"{kit.chk['go_import']}\"\n"
            "\t\"dsverify.lab/harness/driver\"\n" + blank +
            ")\n\n"
            "// The configuration (kit.toml): NC clients, K operations each, the driver's wait\n"
            "// WaitMs, and the adapter's constants.\n"
            f"const (\n{cl})\n\n"
            "// Addrs is every node's address, by node id (node 0 is the client node).\n"
            "func Addrs() []string {\n"
            "\treturn []string{\n" + go_string_list(kit.addrs, "\t\t") + "\t}\n}\n\n"
            "// Main is the client node's program: the harness's driver with the kit's\n"
            "// functions; it panics if the recorded history is not one of the model's.\n"
            "func Main() {\n"
            f"\tdriver.Run(Addrs(), {kit.test['new']}, {kit.test['op']}, {kit.test['gen']}, "
            f"{kit.chk['go_check']}, NC, K, {kit.test['start']}, WaitMs)\n"
            "}\n")


def gen_cmd_client(kit):
    return (gen_go_header(kit, f"Command client is {kit.name}'s client node ({kit.go_name}.Main), "
                          "for the dsrig rig:\n// DSRIG_ADDRS (the rig's node addresses, if set) "
                          f"must be {kit.go_name}.Addrs() without the\n// ports. It exits 0 if "
                          "the history checks, and by a panic otherwise.") +
            "package main\n\n"
            "import (\n"
            "\t\"dsverify.lab/harness/rigenv\"\n"
            f"\t\"{kit.pkg_path}\"\n"
            ")\n\n"
            "func main() {\n"
            f"\trigenv.CheckAddrs({kit.go_name}.Addrs())\n"
            f"\t{kit.go_name}.Main()\n"
            "}\n")


def gen_cmd_server(kit):
    cases = ""
    for i, nd in enumerate(kit.nodes[1:], 1):
        args = ", ".join(str(a) for a in nd.get("args", []))
        cases += f"\tcase \"{i}\":\n\t\t{kit.go_name}.{nd['func']}({args})\n"
    return (gen_go_header(kit, f"Command server is {kit.name}'s server nodes, for the dsrig rig: "
                          "node DSRIG_ID runs its\n// function of the test package (kit.toml's "
                          "[[node]]), as the theorem's node does.\n// DSRIG_ADDRS (if set) must "
                          f"be {kit.go_name}.Addrs() without the ports.") +
            "package main\n\n"
            "import (\n"
            "\t\"fmt\"\n"
            "\t\"os\"\n\n"
            "\t\"dsverify.lab/harness/rigenv\"\n"
            f"\t\"{kit.pkg_path}\"\n"
            ")\n\n"
            "func main() {\n"
            f"\trigenv.CheckAddrs({kit.go_name}.Addrs())\n"
            "\tswitch os.Getenv(\"DSRIG_ID\") {\n" + cases +
            "\tdefault:\n"
            "\t\tfmt.Fprintf(os.Stderr, \"server: bad DSRIG_ID %q\\n\", os.Getenv(\"DSRIG_ID\"))\n"
            "\t\tos.Exit(2)\n"
            "\t}\n"
            "}\n")


def gen_rig_toml(kit):
    n = len(kit.nodes) - 1
    return (f"# Generated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml. "
            "DO NOT EDIT.\n"
            f"# {kit.name} under the dsrig rig (harness/rig): node i at {RIG_SUBNET}({RIG_BASE}+i), "
            "as Addrs().\n"
            "module = \".\"\n"
            f"timeout = {kit.timeout}\n" +
            ("default_route = true\n" if kit.default_route else "") + "\n"
            "# Node 0: the client node (Main).\n"
            f"[[node]]\npkg = \"./{kit.cmd}/client\"\n\n"
            f"# Nodes 1..{n}: the server nodes (node DSRIG_ID runs its function).\n"
            f"[[node]]\npkg = \"./{kit.cmd}/server\"\ncount = {n}\n")


# The harness's model of github.com/google/uuid (harness/rpcmodel/uuid; gen_goose_sh).
UUID_PKG = "github.com/google/uuid"

# The harness's Go packages that a lean.extra_assumptions module's glue calls (their package state
# must be initialized: the generated kit_gen.go imports them, so the test package's initialization
# initializes them).
EXTRA_GO_IMPORTS = {"Harness.Code.sync_extra": "dsverify.lab/harness/syncmap"}


def model_flags(kit):
    """The go command's flags for the model build ([model_build]); empty without one."""
    if not kit.model_build:
        return ""
    tags = kit.model_build.get("tags", [])
    return "-modfile=go.model.mod" + (f" -tags={','.join(tags)}" if tags else "")


def gen_model_mod(kit, tree):
    """go.model.mod: the fork's go.mod, plus [model_build]'s requirements and its replaces of the
    real modules by the lab's models (at the harness the go.mod's replace of dsverify.lab/harness
    names, so a seed's in-sandbox paths carry over)."""
    gm = os.path.join(tree, "go.mod")
    if not os.path.exists(gm):
        die(f"[model_build]: no {gm}")
    with open(gm) as fp:
        src = fp.read()
    m = re.search(r"(?m)^replace dsverify\.lab/harness => (\S+)\s*$", src)
    if not m:
        die(f"[model_build]: {gm} has no replace of dsverify.lab/harness")
    h = m.group(1)
    mb = kit.model_build
    for mod in mb["replace"]:
        if re.search(rf"(?m)^replace {re.escape(mod)} ", src):
            die(f"[model_build]: {gm} already replaces {mod}")
    out = (f"// Generated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml ([model_build]) "
           "and go.mod. DO NOT EDIT.\n"
           "// The model build (`go ... " + model_flags(kit) + "`): go.mod, with the real modules below\n"
           "// replaced by the lab's models (the theorem's program; goose.sh translates it).\n" + src)
    if mb.get("require"):
        out += "\nrequire (\n" + "".join(f"\t{r} // indirect\n" for r in mb["require"]) + ")\n"
    for mod, path in mb["replace"].items():
        out += f"\nreplace {mod} => {h}/{path}\n"
    return out


def trusted_init_files(kit):
    """(path under gen/lean, content) of each lean.trusted_init package's TrustedCode file."""
    files = []
    for p, t in kit.trusted_init.items():
        path = go_pkg_path(kit, p)
        ns = lean_ns(path)
        defs = ""
        for x in t.get("inits", []):
            defs += f"def init.«{x.split('.')[1]}».impl : val :=\n  λ: <>, #()\n"
        for v in t.get("vars", []):
            defs += f"def {'«_»' if v == '_' else v}.init : val :=\n  λ: <>, #()\n"
        what = ", ".join([f"`{x}`" for x in t.get("inits", [])] +
                         [f"`{v}`'s initializer" for v in t.get("vars", [])])
        files.append((os.path.join(kit.root, "TrustedCode", *ns.split(".")) + ".lean", f"""/-
Generated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml (lean.trusted_init). DO NOT EDIT.

Trusted definitions of `{path}`, in namespace `{ns}` like the generated package: its initialization
only. {what} do nothing (goose's config for the package lists them as trusted and leaves them out of
the translation). The claim: in Go they touch no state the program reads and cannot panic (for a
`.pb.go` file: protoc-gen-go's descriptor registration, which a program without reflection does not
observe; for a names-only library: tables and settings no call of the program reaches).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace {ns}
section code
variable [GooseExts] [GoGlobalContext]

{defs}
end code
end {ns}

end Perennial
"""))
        # the (empty) module proofgen's GeneratedProof of a package with trusted names imports
        files.append((os.path.join(kit.root, "ManualProof", *ns.split(".")) + ".lean",
                      f"module\n\n-- Generated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml "
                      f"(lean.trusted_init). DO NOT EDIT.\n-- The (empty) module the generated proof of "
                      f"`{path}` imports (a package with trusted names).\n\n"
                      "public import Perennial.Proof.ProofPrelude\n\n@[expose] public section\n"))
    return files


def go_pkg_path(kit, p):
    """A lean.goose_pkgs entry as a Go package path."""
    if p.startswith("."):
        rel = p.strip("./").strip("/")
        return kit.module + ("/" + rel if rel else "")
    return p


def gen_goose_sh(kit):
    pkgs = " ".join(kit.lean["goose_pkgs"])
    mods = []
    for p in kit.lean["goose_pkgs"]:
        if p.startswith("."):
            rel = p.strip("./").strip("/")
            path = kit.module + ("/" + rel if rel else "")
        else:
            # another module's package, translated with the target (lean.roots names its root)
            path = p
            if not any(path == m or path.startswith(m + "/") for m in kit.lean.get("roots", {})):
                die(f"lean.goose_pkgs {p!r}: a package of the target (./...) or of a module in lean.roots")
        mods.append(lean_ns(path).replace(".", "/"))
    modlist = " \\\n    ".join(f"{kit.root}/{d}/{m}" for m in mods for d in ("Code", "GeneratedProof"))
    extra_roots = "".join(f"\n   -lean-root {m}={r}" for m, r in kit.lean.get("roots", {}).items())
    extra_roots += "".join(f"\n   -lean-root {p}=Harness" for p in kit.lean.get("harness_pkgs", []))
    # github.com/google/uuid: the lab's model (harness/rpcmodel/uuid, not in the offline module
    # cache), which the kit's go.mod substitutes (`require github.com/google/uuid v1.3.1` and
    # `replace github.com/google/uuid => /shared/dsverify-lab/harness/rpcmodel/uuid`; the seed
    # rewrites the replace), translated and proved in the harness (Harness/Proof/uuid): its specs
    # (and its isPkgInit) reach the statement through lean.imports
    if UUID_PKG in kit.lean.get("harness_pkgs", []) and not any(
            m.startswith("Harness.Proof.uuid.") for m in kit.lean.get("imports", [])):
        die(f"lean.harness_pkgs has {UUID_PKG}: lean.imports needs Harness.Proof.uuid.Specs")
    # lean.names_only: declarations Goose cannot translate as released (a goose config per package,
    # translate = everything but them: names only, a call is stuck), which the run's workaround
    # makes translatable
    cfgs = ""
    for p, decls in kit.lean.get("names_only", {}).items():
        if p not in kit.lean["goose_pkgs"] or not p.startswith("."):
            die(f"lean.names_only {p!r}: a package of the target in lean.goose_pkgs")
        if not decls or not all(re.fullmatch(r"\w+(\.\w+)?", d) for d in decls):
            die(f"lean.names_only {p!r}: a list of declarations (F or T.M)")
        rel = p.strip("./").strip("/")
        mod = lean_ns(kit.module + ("/" + rel if rel else "")).replace(".", "/")
        pats = ", ".join(['"*"'] + [f'"!{d}"' for d in decls])
        cfgs += (f'mkdir -p "$OUT/{kit.root}/Code/{os.path.dirname(mod)}"\n'
                 f"echo 'translate = [{pats}]' > \"$OUT/{kit.root}/Code/{mod}.toml\"\n")
    if cfgs:
        cfgs = ("# declarations left untranslated (kit.toml lean.names_only; ISSUES.md): goose's config\n"
                "# for their packages (also proofgen's, -configdir)\n" + cfgs)
    # lean.trusted_init: goose's config for each package whose initialization is a trusted no-op
    # (its TrustedCode file is a fixed file of the kit, built before this script runs: HARNESS_BUILD)
    tcfgs = ""
    for p, t in kit.trusted_init.items():
        mod = lean_ns(go_pkg_path(kit, p)).replace(".", "/")
        q = lambda xs: "[" + ", ".join(f'"{x}"' for x in xs) + "]"   # noqa: E731
        lines = [f"translate = {q(t.get('translate', ['!*']))}"]
        if "imports" in t:
            lines.append(f"imports = {q(t['imports'])}")
        lines.append(f"trusted = {q(t.get('inits', []) + t.get('vars', []) + t.get('names', []))}")
        tcfgs += (f'mkdir -p "$OUT/{kit.root}/Code/{os.path.dirname(mod)}"\n'
                  f"cat > \"$OUT/{kit.root}/Code/{mod}.toml\" <<'EOF'\n" + "\n".join(lines) + "\nEOF\n")
    if tcfgs:
        cfgs += ("# packages whose initialization is a trusted no-op (kit.toml lean.trusted_init; the\n"
                 f"# kit's fixed files {kit.root}/TrustedCode/...): goose's config for them\n" + tcfgs)
    # [model_build]: the model build's modfile (go.model.mod: the lab's models of the listed modules)
    modfile = ""
    if kit.model_build:
        modfile = ('# the model build (kit.toml [model_build]): go.model.mod replaces '
                   + ", ".join(kit.model_build["replace"]) + "\n# by the lab's models\n"
                   'export GOFLAGS="${GOFLAGS:-} -modfile=$F/go.model.mod"\n')
    rpc_roots = ""
    tags = ""
    what = "log is the lab's model"
    goroot_opt = ""
    if kit.rpc:
        rpc_roots = "\n   -lean-root encoding/gob=Harness"
        what = ("log, net/rpc and net/http are the lab's models, with the kit's codec\n"
                "# registration (rpc_model_gen.go, built under goose's own tag goose: goose's\n"
                "# package loader passes -tags goose, which overrides any tags in GOFLAGS)")
        if kit.rpc.gob:
            # [rpc] gob: encoding/gob is the lab's model, translated with the target (lean.roots)
            rpc_roots = ""
            goroot_opt = " gob"
            what = ("log, net/rpc, net/http and encoding/gob are the lab's models, with the kit's\n"
                    "# codec registration (rpc_model_gen.go, built under goose's own tag goose: goose's\n"
                    "# package loader passes -tags goose, which overrides any tags in GOFLAGS)")
    if kit.json:
        what = ("log, log/slog and encoding/json are the lab's models, with the kit's codec\n"
                "# registration (json_model_gen.go, built under goose's own tag goose)")
    rpc_env = (
        f"# {what} (harness/rpcmodel, notes/craq-net.md):\n"
        "# goose translates through a GOROOT that substitutes them\n"
        "HM=$(go list -m -f '{{.Dir}}' dsverify.lab/harness)\n"
        f'export GOROOT=$("$HM/rpcmodel/goroot.sh" "$OUT/goroot"{goroot_opt})\n' + tags)
    # lean.expand_tabs (default off; kits/rabia-net): Goose copies Go doc comments into Lean
    # docstrings, and Lean rejects tab characters; the translation's tabs are replaced by spaces
    # inside comments only (a tab anywhere else stops goose.sh: it could be in a string literal)
    tabs = ""
    if kit.lean.get("expand_tabs", False):
        tabs = f"""# tabs in Go doc comments (Lean rejects tabs): spaces, in the translation's comments only
# (kit.toml lean.expand_tabs); a tab outside a comment is an error
python3 - "$OUT/{kit.root}/Code" "$OUT/{kit.root}/GeneratedProof" <<'PYEOF'
import os, sys
for top in sys.argv[1:]:
    for d, _, fs in os.walk(top):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            src = open(p).read()
            if "\\t" not in src:
                continue
            out, depth, i, n = [], 0, 0, len(src)
            while i < n:
                if not depth and src[i] == '"':
                    j = i + 1
                    while j < n and src[j] != '"':
                        j += 2 if src[j] == "\\\\" else 1
                    seg = src[i:j + 1]
                    if "\\t" in seg:
                        sys.exit(f"goose.sh: a tab in a string literal in {{p}}")
                    out.append(seg); i = j + 1; continue
                if src.startswith("/-", i):
                    depth += 1; out.append("/-"); i += 2; continue
                if depth and src.startswith("-/", i):
                    depth -= 1; out.append("-/"); i += 2; continue
                if not depth and src.startswith("--", i):
                    j = src.find("\\n", i); j = n if j < 0 else j
                    out.append(src[i:j].replace("\\t", "    ")); i = j; continue
                c = src[i]
                if c == "\\t":
                    if not depth:
                        sys.exit(f"goose.sh: a tab outside a comment in {{p}}")
                    c = "    "
                out.append(c); i += 1
            open(p, "w").write("".join(out))
PYEOF
"""
    # sync.Map's memory (Harness/Code/sync_extra, a lean.extra_assumptions module): proofgen derives a
    # struct's points-to from its fields' instances, and for a sync.Map field it finds Perennial's
    # (a `sorry`: sync.Map is an axiomatized type). Each generated section that mentions sync.Map
    # gets the classes the harness's instances need (Harness/Proof/sync/Map.lean, imported), so the
    # generated instances are built on them (quepaxa-net-1's spec feedback 3).
    syncmap = ""
    if ("Harness.Code.sync_extra", "sync.ExtraAssumptions") in kit.extras:
        syncmap = f"""# sync.Map's memory: generated sections that mention sync.Map use the harness's instances
# (Harness/Proof/sync/Map.lean, under sync.ExtraAssumptions), not Perennial's `sorry`s
python3 - "$OUT/{kit.root}/GeneratedProof" <<'PYEOF'
import os, sys
EXTRA = "variable [sync.Assumptions] [sync.ExtraAssumptions]"
for d, _, fs in os.walk(sys.argv[1]):
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        lines = open(p).read().split(chr(10))
        if not any("sync.Map" in l for l in lines):
            continue
        out, sec, n = [], None, 0
        for l in lines:
            if l == "section def_":
                sec = [l]
            elif sec is not None:
                sec.append(l)
                if l == "end def_":
                    if any("sync.Map" in x for x in sec):
                        k = next(i for i, x in enumerate(sec) if x.startswith("variable [package_sem' : "))
                        sec.insert(k + 1, EXTRA)
                        n += 1
                    out += sec
                    sec = None
            else:
                out.append(l)
        if not n:
            sys.exit(f"goose.sh: {{p}} mentions sync.Map outside the sections it knows")
        k = out.index("public import Perennial.Proof.ProofPrelude")
        out.insert(k + 1, "public import Harness.Proof.sync.Map")
        open(p, "w").write(chr(10).join(out))
PYEOF
"""
    # the kit's trusted files are built into HARNESS_BUILD (goalbuild.sh); Lean finds a module root
    # (`{kit.root}`) under one search path only, so their oleans go beside the translation's
    trusted_copy = ""
    if kit.trusted_init:
        trusted_copy = (f"# the kit's trusted files ({kit.root}/TrustedCode and the empty {kit.root}/ManualProof, fixed\n# files built into HARNESS_BUILD), beside\n"
                        f"# the translation: Lean looks for the modules of `{kit.root}` under one search path\n"
                        f"mkdir -p \"$OUT/build/{kit.root}\"\n"
                        f"cp -r \"$HB/{kit.root}/TrustedCode\" \"$HB/{kit.root}/ManualProof\" \"$OUT/build/{kit.root}/\"\n")
    return f"""#!/bin/bash
# Generated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml. DO NOT EDIT.
# Translate the target's packages ({pkgs}) with goose and proofgen at the lab's pin, and
# typecheck the output with plain lean against the pinned Perennial and the harness's built
# modules. Usage: ./goose.sh [OUT]   (default OUT: ./lean, git-ignored)
# Environment (required): GOOSE_BIN (goose and proofgen built at the pin), PERENNIAL (a built
# checkout of Perennial at the pin), HARNESS_BUILD (the built Harness modules); LEAN (default lean).
set -euo pipefail
F=$(cd "$(dirname "$0")" && pwd)
OUT=$(mkdir -p "${{1:-$F/lean}}" && cd "${{1:-$F/lean}}" && pwd)
B=${{GOOSE_BIN:?set GOOSE_BIN to the directory of goose and proofgen built at the pin}}
D=${{PERENNIAL:?set PERENNIAL to a built checkout of Perennial at the pin}}
HB=${{HARNESS_BUILD:?set HARNESS_BUILD to the directory of the built Harness modules (oleans)}}
P=$D/.lake/packages
LEAN=${{LEAN:-lean}}
[ -f "$F/env.sh" ] && . "$F/env.sh"
{modfile}export CGO_ENABLED=0   # net as harness/lean translates it
R=(-lean-root {kit.module}={kit.root} -lean-root dsverify.lab/harness=Harness
   -lean-root net=Harness -lean-root github.com/anishathalye/porcupine=Harness
   -lean-root log=Harness{rpc_roots}{extra_roots})
cd "$F"
{cfgs}{rpc_env}"$B/goose" -out "$OUT/{kit.root}/Code" "${{R[@]}}" {pkgs}
"$B/proofgen" -out "$OUT/{kit.root}/GeneratedProof" -configdir "$OUT/{kit.root}/Code" "${{R[@]}}" {pkgs}
{tabs}{syncmap}{trusted_copy}export LEAN_PATH=$OUT/build:$HB:$D/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/iris/Iris/.lake/build/lib/lean
cd "$OUT"
for m in {modlist}; do
  # proofgen splits a large package's proof module into chunks ($m/chunkN.lean), which $m imports
  for c in $(ls "$m"/chunk*.lean 2>/dev/null | sort -V); do
    c=${{c%.lean}}; mkdir -p "build/$(dirname "$c")"
    echo "== $c"
    "$LEAN" -o "build/$c.olean" "$c.lean"
  done
  mkdir -p "build/$(dirname "$m")"
  echo "== $m"
  "$LEAN" -o "build/$m.olean" "$m.lean"
done
"""


# ---------------------------------------------------------------------------------------------
# Lean


def lean_header(kit, what):
    return (f"/-\nGenerated by harness/kitgen from kits/{os.path.basename(kit.dir)}/kit.toml. "
            "DO NOT EDIT: regenerate\n(`harness/kitgen/kitgen.py`); `kitgen.py --check` "
            f"verifies it is current.\n\n{what}\n-/\n")


def gen_spec_lean(kit):
    P = kit.prefix
    tp = lean_ns(kit.pkg_path)                 # the test package's namespace
    tpl = tp[len(kit.ns) + 1:] if tp.startswith(kit.ns + ".") else "_root_." + tp
    # each package's own part of its isPkgInit (isPkgInitDef: its package-level state) is the
    # run's choice, a field of the class {P}PkgState; the test package's is True (the kit's adapter)
    others = kit.pkg_init_order[:-1]
    names = {p: lean_ns(p).split(".")[-1] for p in kit.pkg_init_order}
    if len(set(names.values())) != len(names):
        names = {p: lean_ns(p)[len(kit.ns) + 1:].replace(".", "_") for p in kit.pkg_init_order}
    fields = "".join(f"  /-- `{p}`'s package-level state -/\n  {names[p]} : IProp GF\n" for p in others)
    insts = (f"/-- The run's choice of each package's own post-initialization predicate (`isPkgInitDef`:\n"
             "its package-level state, e.g. `errors.newVar` for an `errors.New` variable); the test\n"
             "package's is `True`. Not in the trust base: `SafeDist` does not mention it, and the run\n"
             "proves each package's initialization establishes it. -/\n"
             f"class {P}PkgState (GF : BundledGFunctors) where\n{fields}\n"
             f"/-- A choice of `{P}PkgState` at every heap. -/\n"
             f"abbrev {P}PkgStates [GoGlobalContext] :=\n"
             f"  ∀ {{GF : BundledGFunctors}} [HeapGS HasLC.hasLC GF] [go.Semantics], {P}PkgState GF\n\n")
    for p in kit.pkg_init_order:
        n = names[p]
        user = f"(pkgState.{n})" if p in others else "iprop(True)"
        insts += (f"instance {n}_isPkgInit_inst [pkgState : {P}PkgState GF] :\n"
                  f"    IsPkgInit (IProp GF) pkg_id.{lean_ns(p)} :=\n"
                  f"  define_is_pkg_init {user}\n"
                  f"instance {n}_get_isPkgInit_wf_inst [pkgState : {P}PkgState GF] :\n"
                  f"    GetIsPkgInitWf (IProp GF) pkg_id.{lean_ns(p)} :=\n"
                  "  build_get_is_pkg_init_wf\n\n")
    tn = names[kit.pkg_path]
    extra = ["Perennial.Proof.errors.NewVar"] + (RPC_IMPORTS if kit.rpc else [])
    # lean.io_extra (default off): the node's assumptions also give goose's FuncUnfold of Go's
    # io.ReadAtLeast and io.ReadFull (io.ExtraAssumptions, Harness/Code/io_extra.lean); in general,
    # lean.extra_assumptions: each module's class (kit.extras, io_extra's first)
    io_extra = ("Harness.Code.io_extra", "io.ExtraAssumptions") in kit.extras
    extra += [m for m, _ in kit.extras]
    node_assms = f"{tpl}.Assumptions ∧ net.model.Assumptions" + "".join(f" ∧ {c}" for _, c in kit.extras)
    io_note = ("; with lean.io_extra, goose's unfolding of `io.ReadAtLeast` and `io.ReadFull`\n"
               "(`io.ExtraAssumptions`)") if io_extra else ""
    others_x = [(m, c) for m, c in kit.extras if c != "io.ExtraAssumptions"]
    if others_x:
        io_note += ("; and the harness's translations of the library functions the pinned Perennial has\n"
                    "as names only (lean.extra_assumptions: " +
                    ", ".join(f"`{c}`, `{m.replace('.', '/')}.lean`" for m, c in others_x) + ")")
    imports = (["Harness.Driver", "Harness.PkgInit", kit.chk["lean_import"]] + NET_IMPORTS + extra +
               [f"{kit.root}.GeneratedProof.{tp}"] + kit.lean.get("imports", []))
    addrs = ",\n   ".join(", ".join(f'go!"{a}"' for a in kit.addrs[i:i + 3])
                           for i in range(0, len(kit.addrs), 3))
    ips = ", ".join(f"⟨{RIG_SUBNET.replace('.', ', ')}{RIG_BASE + i}⟩" for i in range(len(kit.nodes)))
    eps = ",\n     ".join(f"⟨⟨{RIG_SUBNET.replace('.', ', ')}{RIG_BASE + i}⟩, {p}⟩"
                          for i, nd in enumerate(kit.nodes) for p in nd["_ports"])
    cfgname = P[0].lower() + P[1:] + "Cfg"
    cfg_note = (" (`Addrs()[i]`\n  is node `i`'s first port; `allAddrs`, every node's ports)" if kit.multiport else "")
    if kit.multiport:
        alladdrs = ",\n   ".join(", ".join(f'go!"{a}"' for a in kit.all_addrs[i:i + 3])
                                for i in range(0, len(kit.all_addrs), 3))
        nodeaddrs = ",\n   ".join("[" + ", ".join(f'go!"{a}"' for a in na) + "]" for na in kit.node_addrs)
        cfg_addrs = f"""/-- Every configured endpoint, node by node (a node with several ports listens on each). -/
def allAddrs : List GoString :=
  [{alladdrs}]

/-- Node `i`'s endpoints (its first is `Addrs()[i]`). -/
def nodeAddrs : List (List GoString) :=
  [{nodeaddrs}]

theorem nodeAddrs_flatten : nodeAddrs.flatten = allAddrs := by decide

theorem nodeAddrs_head : nodeAddrs.map (fun l => l.headD go!"") = addrs := by decide

/-- The configured addresses are every node's endpoints, in node order. -/
theorem {cfgname}_addrs : {cfgname}.addrs = allAddrs := by decide"""
    else:
        cfg_addrs = f"""/-- The configured addresses are `Addrs()`'s, in node order. -/
theorem {cfgname}_addrs : {cfgname}.addrs = addrs := by decide"""
    servers = []
    for i, nd in enumerate(kit.nodes[1:], 1):
        args = ", ".join(f"#(W64 {a})" for a in nd.get("args", []))
        servers.append(f"  -- node {i}: `{nd['func']}({', '.join(str(a) for a in nd.get('args', []))})`\n"
                       f"  {{ Assumptions := nodeAssumptions, init := {tpl}.initialize',\n"
                       f"    main := {tpl}.{nd['func']}, args := [ {args} ] }}")
    t = kit.test
    n = len(kit.nodes)
    rpc_kit = ""
    if kit.rpc:
        rpc_kit = ("/-- The kit whose codec functions the program registers with the net/rpc model (the\n"
                   "generated `registerRPC`; `net.rpc.RpcKit`, Harness/Proof/net/rpc/Base.lean). -/\n"
                   f"instance rpcKit : net.rpc.RpcKit := ⟨go!\"{kit.pkg_path}\"⟩\n\n")
    if kit.json:
        rpc_kit += ("/-- The kit whose codec functions the program registers with the encoding/json model\n"
                    "(the generated `registerJSON`; `encoding.json.JsonKit`, Harness/Proof/encoding/json.lean). -/\n"
                    f"instance jsonKit : encoding.json.JsonKit := ⟨go!\"{kit.pkg_path}\"⟩\n\n")
    if kit.protobuf:
        rpc_kit += ("/-- The kit whose codec functions the program registers with the protobuf model (the\n"
                    "generated `registerProto`; `google_golang_org.protobuf.proto.PbKit`,\n"
                    "Harness/Proof/grpc/Base.lean). -/\n"
                    f"instance pbKit : google_golang_org.protobuf.proto.PbKit := ⟨go!\"{kit.pkg_path}\"⟩\n\n")
    return lean_header(kit, f"""The statement of {kit.name} ({kit.c.get('description', '')}): the
plumbing, all from kit.toml. The run proves `{P}SpecHolds`; `{P}Main.lean` (generated too) turns
it into `SafeDist (clientNode :: serverNodes) {P[0].lower() + P[1:]}Cfg` by the harness's generic
lemma (`driver_dist_safe`, `Harness/Driver.lean`).

* The kit's code (`kit`, a `DriverKit`): the test package `{kit.pkg_path}` and its functions
  `{t['new']}`, `{t['op']}`, `{t['gen']}`, `{t['start']}` (the adapter) that the generated `Main`
  passes to `driver.Run`, with `{kit.chk['go_check']}`, {kit.nC} clients, {kit.k} operation(s)
  each, a wait of {kit.waitMs} ms; the model `{kit.chk['model']}` and its encodings; the input
  premise.
* The nodes: node 0 runs `Main` (`clientNode`); node `i` ≥ 1 runs its function of the test
  package with its constant arguments (`serverNodes`). Every node runs the test package's
  initialization first; its assumptions are the package's generated ones and the `net` model's.
* The configuration: node `i` at {RIG_SUBNET}({RIG_BASE}+i), `Addrs()`'s constants{cfg_note}; well formed
  by `decide`.
* The goal `{P}SpecHolds`: at every global ghost state, a `DriverDistSpec`: the run's start
  update, the client spec of `kit` at the client node (`DriverClientSpec`: the package's
  initialization, `{t['new']}`, `{t['op']}`, `{t['gen']}`, `{t['start']}`), and the server nodes'
  boot programs, each on its node's IP (`NodeBootWpAt`).""") + f"""module

""" + "".join(f"public import {m}\n" for m in imports) + f"""
@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode NetConn Dsv dsverify_lab.harness

namespace {kit.ns}

attribute [local instance] {INSTANCES}

{rpc_kit}section defs
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

{insts}end defs

/-! ## The code -/

/-- `Addrs()`: node `i`'s address. -/
def addrs : List GoString :=
  [{addrs}]

/-- The kit's code: the test package, its functions passed to the driver, the constants, the model's
encodings and the input premise. -/
def kit [GoGlobalContext] : DriverKit ({kit.chk['model']}) where
  pkg := pkg_id.{tp}
  initialize' := {tpl}.initialize'
  addrs := addrs
  addrsF := {tpl}.Addrs
  newF := {tpl}.{t['new']}
  opF := {tpl}.{t['op']}
  genF := {tpl}.{t['gen']}
  checkF := {kit.chk['lean_check']}
  startF := {tpl}.{t['start']}
  mainF := {tpl}.Main
  nC := W64 {kit.nC}
  k := W64 {kit.k}
  waitMs := W64 {kit.waitMs}
  encI := {kit.chk['encI']}
  encO := {kit.chk['encO']}
  pre := {t['pre']}

instance kit_isPkgInit [GoGlobalContext] {{GF : BundledGFunctors}} [HeapGS HasLC.hasLC GF]
    [go.Semantics] [{P}PkgState GF] : IsPkgInit (IProp GF) kit.pkg :=
  {tn}_isPkgInit_inst
instance kit_get_isPkgInit_wf [GoGlobalContext] {{GF : BundledGFunctors}} [HeapGS HasLC.hasLC GF]
    [go.Semantics] [{P}PkgState GF] : GetIsPkgInitWf (IProp GF) kit.pkg :=
  {tn}_get_isPkgInit_wf_inst

/-! ## The nodes and the configuration -/

section nodes
variable [GoGlobalContext]

/-- Every node's assumptions on its Go context: the test package's generated ones (which include
its imports') and the `net` model's trusted layouts{io_note}. -/
def nodeAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop :=
  {node_assms}

/-- Node 0: the client node, `Main`. -/
def clientNode : Node where
  Assumptions := nodeAssumptions
  init := {tpl}.initialize'
  main := {tpl}.Main

/-- Nodes 1..{n - 1}: each runs its function with its arguments. -/
def serverNodes : List Node := [
{(',' + chr(10)).join(servers)}]

end nodes

/-- The rig's configuration: node `i` at {RIG_SUBNET}({RIG_BASE}+i), with its port{"s" if kit.multiport else ""}. -/
def {P[0].lower() + P[1:]}Cfg : NetConfig :=
  ⟨[{ips}],
    [{eps}]⟩

theorem {P[0].lower() + P[1:]}Cfg_wf : {P[0].lower() + P[1:]}Cfg.WellFormed {n} := by decide

{cfg_addrs}

/-! ## The goal -/

/-- The run's goal: for the run's choice `S` of the packages' state, at every global ghost state, a
`DriverDistSpec` for the kit's code, the client node, the server nodes and the configuration. -/
def {P}SpecHolds [GoGlobalContext] : Prop :=
  ∃ S : {P}PkgStates, ∀ [GooseGlobalGS .hasLC netDistGF],
    Nonempty (DriverDistSpec ({kit.chk['model']}) kit
      (pkgInst := fun {{GF}} [h : HeapGS HasLC.hasLC GF] [s : go.Semantics] => @kit_isPkgInit _ GF h s (@S GF h s))
      (pkgWf := fun {{GF}} [h : HeapGS HasLC.hasLC GF] [s : go.Semantics] => @kit_get_isPkgInit_wf _ GF h s (@S GF h s))
      clientNode serverNodes {P[0].lower() + P[1:]}Cfg)

end {kit.ns}

end Perennial
"""


def gen_main_lean(kit):
    P = kit.prefix
    cfg = P[0].lower() + P[1:] + "Cfg"
    tp = lean_ns(kit.pkg_path)
    tpl = tp[len(kit.ns) + 1:] if tp.startswith(kit.ns + ".") else "_root_." + tp
    n = len(kit.nodes)
    return lean_header(kit, f"""The per-kit residue of {kit.name}: the kit's facts at its client
node (`DriverMainFacts`, each by a fixed script) and the goal from the harness's generic lemma
`driver_dist_safe` (`Harness/Driver.lean`). Nothing here is about the kit's behavior: `Main` is the
generated one-line driver call, `Addrs()` the generated slice.""") + f"""module

public import {P}Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode NetConn Dsv dsverify_lab.harness

namespace {kit.ns}

attribute [local instance] {INSTANCES}

set_option linter.unusedSectionVars false

section facts
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : {tpl}.Assumptions] [pkgState : {P}PkgState GF]

set_option goose.wp.extras true in
/-- `Addrs()` returns a new slice of the address constants. -/
theorem wp_Addrs :
    {{{{ isPkgInit (PROP := IProp GF) pkg_id.{tp} }}}}
      (App (Val (@! {tpl}.Addrs)) (Val #()))
    {{{{ (sl : GoSlice), RET #sl; sl ↦* addrs }}}} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) addrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- The kit's facts under the client node's assumptions. -/
theorem driverFacts : DriverFacts (GF := GF) ({kit.chk['model']}) kit where
  driver_assumptions := inferInstance
  main := (func_unfold (f := {tpl}.Main)).trans rfl
  addrs := wp_Addrs
  get := ⟨get_is_pkg_init_of% pkg_id.{tp}, by get_is_pkg_init_wf⟩
  deps := by
    show isPkgInit (PROP := IProp GF) pkg_id.{tp} ⊢ _
    iintro #H
    iPkgInit
  checker := {kit.chk['checker_fn']} kit.pkg (by
    show isPkgInit (PROP := IProp GF) pkg_id.{tp} ⊢ _
    iintro #H
    iPkgInit)

end facts

/-- The client node runs the generated `Main` (`DriverMainFacts`), for any choice of the packages'
state. -/
theorem main_facts [GoGlobalContext] (S : {P}PkgStates) :
    DriverMainFacts ({kit.chk['model']}) kit
      (pkgInst := fun {{GF}} [h : HeapGS HasLC.hasLC GF] [s : go.Semantics] => @kit_isPkgInit _ GF h s (@S GF h s))
      (pkgWf := fun {{GF}} [h : HeapGS HasLC.hasLC GF] [s : go.Semantics] => @kit_get_isPkgInit_wf _ GF h s (@S GF h s)) clientNode :=
  ⟨rfl, rfl, rfl, by show uint.Z (W64 {kit.nC}) < 2 ^ 32; decide,
    by show uint.Z (W64 {kit.nC}) * uint.Z (W64 {kit.k}) < 2 ^ 61; decide, fun {{_}} {{_}} ha => by
    haveI := ha.1
    exact driverFacts (pkgState := S)⟩

/-- The {n} nodes are safe, given the run's `{P}SpecHolds`. -/
theorem goal_of_spec [GoGlobalContext] (hspec : {P}SpecHolds) :
    SafeDist (clientNode :: serverNodes) {cfg} := by
  obtain ⟨S, h⟩ := hspec
  exact driver_dist_safe ({kit.chk['model']}) kit
    (pkgInst := fun {{GF}} [h : HeapGS HasLC.hasLC GF] [s : go.Semantics] => @kit_isPkgInit _ GF h s (@S GF h s))
    (pkgWf := fun {{GF}} [h : HeapGS HasLC.hasLC GF] [s : go.Semantics] => @kit_get_isPkgInit_wf _ GF h s (@S GF h s))
    {cfg}_wf (main_facts S) h

end {kit.ns}

end Perennial
"""


def gen_goal_lean(kit):
    P = kit.prefix
    cfg = P[0].lower() + P[1:] + "Cfg"
    n = len(kit.nodes)
    t = kit.test
    return f"""/-
The goal of this run (generated by harness/kitgen from kit.toml): one theorem to prove,
`goal_spec`, and the safety of the {n} nodes, which follows from it.

`{P}Spec.lean` (the lab's, generated; read it first) states the nodes, the configuration, the
kit's code and `{P}SpecHolds`: at every global ghost state, a `DriverDistSpec`
(`Harness/Driver.lean`) for `kit`, the client node and the server nodes:
* `Γs`, `clientRes`, `serverRes`, `start`: your ghost names, and an update from the network's start
  resources (each address's token and unset protocols) to the client node's share and each server
  node's share; here you allocate the invariants the nodes share and set every address's
  protocols (`addrs_set_proto`, `Harness/SafeDist.lean`);
* `client_spec`: `DriverClientSpec ({kit.chk['model']}) kit (clientRes γ)` at the client node:
  you choose the abstract predicates (`is_sys`, `client_tok`, `own_state`) and prove the test
  package's initialization and its functions `{t['new']}` (from the client node's share and the
  address slice; it gives each client's token at operation 0, `client_tok γ c 0`), `{t['op']}`
  (logically atomic with its update at `↑clientN`; B form: `(_, false)` is an unknown outcome;
  an operation budget: only for client `c`'s `j`-th operation with `j < uint.nat kit.k`, taking
  `client_tok γ c j` to `client_tok γ c (j + 1)`), `{t['gen']}` and `{t['start']}`, given the
  fact that the client node's IP is its configured one (`cfg.ips[0]? = some ip` and
  `netIp = ip.spell`, the fact `nodeIp` as a Lean premise), with which it can tell its node
  from the servers';
* `servers_boot`: each server node's boot program (the test package's initialization, then its
  function with its arguments) is safe from its share (`NodeBootWpAt`), given the fact that its
  node's IP is its configured one (`nodeIp`, which a `net.Listen` on a wildcard host such as
  `":port"` or `"0.0.0.0:port"` needs: `net.ListenWild.wp_proof`).

`goal` (`SafeDist`: in every execution of the {n} nodes from a start where each has its Go
context, no package initialized and one thread, node `i` is on its configured IP, and the
network has the configured addresses and no listener or connection, no node panics, no thread is
stuck, and a finished main thread returned) follows from `goal_spec` by `goal_of_spec` (`{P}Main.lean`, generated: the generated
`Main` and the harness's generic lemma `driver_dist_safe`); its proof is given.

What you may change in this file: the imports (add the modules of your proofs) and the proof term
of `goal_spec` (`sorry`). Nothing else. The final check does not trust this file: it states the
theorems again from its own copies of the fixed files (checked byte-identical to the project's)
and applies `goal_spec` to them.
-/
module

public import {P}Spec
public import {P}Main

@[expose] public section

noncomputable section

namespace Perennial

open Dsv

namespace {kit.ns}

attribute [local instance] {INSTANCES}

/-- The code meets the client spec, the servers are safe, under a start of your choice. -/
theorem goal_spec [GoGlobalContext] : {P}SpecHolds :=
  sorry

/-- The {n} nodes are safe. -/
theorem goal [GoGlobalContext] : SafeDist (clientNode :: serverNodes) {cfg} :=
  goal_of_spec goal_spec

end {kit.ns}

end Perennial
"""


def gen_goalcheck_lean(kit):
    P = kit.prefix
    cfg = P[0].lower() + P[1:] + "Cfg"
    ns = "Perennial." + kit.ns
    return f"""-- Generated by harness/kitgen from kit.toml. The lab's statement of the run's goal (never in the
-- agent's view): `verify.sh` elaborates this file in the project. `DsvStatement`, `DsvNet`,
-- `{P}Spec`, `{P}Main` and the harness's modules are the project's copies, checked byte-identical
-- to the lab's first (`goal-check.sh`, the goal directory's `fixed/`); every name is written in
-- full, so a declaration of the project cannot shadow one.
import DsvStatement
import DsvNet
import {P}Spec
import {P}Main
import Goal

attribute [local instance] Perennial.Dsv.netConnExts Perennial.Dsv.netConnExtsSemantics
  Perennial.Dsv.netConnExtsInterp Perennial.GooseGlobalGS.gooseInvGS Perennial.Dsv.netConnExts_has

/-- The run's part: the client spec at the client node, the servers' boot programs, and the
start that ties them together. -/
theorem dsv_goal_check_spec [Perennial.GoGlobalContext] :
    {ns}.{P}SpecHolds :=
  {ns}.goal_spec

/-- The nodes are safe: the generated `Main` and the harness's generic lemma, from the run's part
only. -/
theorem dsv_goal_check [Perennial.GoGlobalContext] :
    Perennial.Dsv.SafeDist
      ({ns}.clientNode :: {ns}.serverNodes)
      {ns}.{cfg} :=
  {ns}.goal_of_spec dsv_goal_check_spec

#print axioms dsv_goal_check_spec
#print axioms dsv_goal_check
"""


# ---------------------------------------------------------------------------------------------
# Driver


def outputs(kit, tree):
    """(path, content, mode) of every generated file."""
    pkgdir = os.path.join(tree, kit.pkg_rel)
    gen = os.path.join(kit.dir, "gen")
    rpc = []
    if kit.rpc:
        h = lambda what: gen_go_header(kit, what)   # noqa: E731
        rpc = [
            (os.path.join(pkgdir, "rpc_gen.go"),
             rpcgen.gen_codec_go(kit.rpc, h("The net/rpc model's codec for kit.toml's [rpc] "
                                          "(harness/kitgen/rpcgen.py)."), kit.go_name), 0o644),
            (os.path.join(pkgdir, "rpc_model_gen.go"),
             rpcgen.gen_register_model(h("registerRPC for the net/rpc model."), kit.go_name,
                                       kit.rpc.gob), 0o644),
            (os.path.join(pkgdir, "rpc_real_gen.go"),
             rpcgen.gen_register_real(h("registerRPC for the real net/rpc."), kit.go_name,
                                      kit.rpc.gob), 0o644),
            (os.path.join(pkgdir, "rpc_gen_test.go"),
             rpcgen.gen_test_go(kit.rpc, h("Tests of the net/rpc codec's claims against real gob "
                                         "and net/rpc's reflection."), kit.go_name), 0o644),
        ]
    js = []
    if kit.json:
        h = lambda what: gen_go_header(kit, what)   # noqa: E731
        js = [
            (os.path.join(pkgdir, "json_gen.go"),
             jsongen.gen_codec_go(kit.json, h("The encoding/json model's codec for kit.toml's [json] "
                                            "(harness/kitgen/jsongen.py)."), kit.go_name, True), 0o644),
            (os.path.join(pkgdir, "json_model_gen.go"),
             jsongen.gen_register_model(h("registerJSON for the encoding/json model."), kit.go_name), 0o644),
            (os.path.join(pkgdir, "json_real_gen.go"),
             jsongen.gen_register_real(h("registerJSON for the real encoding/json."), kit.go_name), 0o644),
            (os.path.join(pkgdir, "json_gen_test.go"),
             jsongen.gen_test_go(kit.json, h("Tests of the encoding/json codec's claims against real "
                                           "encoding/json."), kit.go_name), 0o644),
        ]
        hx = h("The encoding/json model's codec for kit.toml's [json] types that Goose cannot "
               "translate (harness/kitgen/jsongen.py).")
        js += [(os.path.join(pkgdir, f), c, 0o644)
               for f, c in sorted(jsongen.gen_extra_files(kit.json, hx, kit.go_name).items())]
    if kit.protobuf:
        hp = gen_go_header(kit, "The protobuf model's codec for kit.toml's [protobuf] (harness/kitgen/pbgen.py).")
        js += [(os.path.join(pkgdir, f), c, 0o644)
               for f, c in sorted(pbgen.files(kit.protobuf, hp, kit.go_name).items())]
    # [model_build]: go.model.mod beside go.mod; lean.trusted_init: the fixed TrustedCode files
    mb = [(os.path.join(tree, "go.model.mod"), gen_model_mod(kit, tree), 0o644)] if kit.model_build else []
    ti = [(os.path.join(gen, "lean", f), c, 0o644) for f, c in trusted_init_files(kit)]
    return rpc + js + mb + ti + [
        (os.path.join(pkgdir, "kit_gen.go"), gen_kit_gen_go(kit), 0o644),
        (os.path.join(tree, kit.cmd, "client", "main.go"), gen_cmd_client(kit), 0o644),
        (os.path.join(tree, kit.cmd, "server", "main.go"), gen_cmd_server(kit), 0o644),
        (os.path.join(tree, "rig.toml"), gen_rig_toml(kit), 0o644),
        (os.path.join(tree, "goose.sh"), gen_goose_sh(kit), 0o755),
        (os.path.join(gen, "lean", f"{kit.prefix}Spec.lean"), gen_spec_lean(kit), 0o644),
        (os.path.join(gen, "lean", f"{kit.prefix}Main.lean"), gen_main_lean(kit), 0o644),
        (os.path.join(gen, "Goal.lean"), gen_goal_lean(kit), 0o644),
        (os.path.join(gen, "GoalCheck.lean"), gen_goalcheck_lean(kit), 0o644),
        (os.path.join(gen, "prompt.txt"), gen_prompt(kit), 0o644),
    ]


PROMPT_TEMPLATE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prompt-net.txt")
# kit.toml's [prompt]: the kit's own sentences; everything else in the prompt is the template's or
# derived from kit.toml (review item 5: one common body, a short per-kit part)
PROMPT_KEYS = {"system": True, "fork": True, "adapter": True, "deployment": True,
               "bugs": True, "system_code": False, "nodetest": False}


def gen_prompt(kit):
    pr = kit.c.get("prompt")
    if pr is None:
        die("kit.toml has no [prompt] section")
    for key, required in PROMPT_KEYS.items():
        if required and not pr.get(key):
            die(f"kit.toml [prompt].{key} is required")
    for key in pr:
        if key not in PROMPT_KEYS:
            die(f"kit.toml [prompt].{key}: unknown (known: {sorted(PROMPT_KEYS)})")
    tg, t, run = kit.c["target"], kit.c["test"], kit.c.get("run", {})
    repo = tg["url"].rstrip("/").split("/")[-1]
    n = len(kit.nodes)
    servers = ", ".join(
        f"node {i} runs {nd['func']}({', '.join(str(x) for x in nd.get('args', []))})"
        for i, nd in enumerate(kit.nodes[1:], 1))
    hosts = " ".join(str(i) for i in range(n))
    ids = " ".join(str(i) for i in range(1, n))
    nodetest = (f"for x in {hosts}; do ip addr add {RIG_SUBNET}$((10+x))/24 dev lo; done; " +
                ("ip route add default dev lo; " if kit.default_route else "") +
                f"go build {model_flags(kit) + ' ' if kit.model_build else ''}-o /tmp/kn/ "
                f"./{kit.cmd}/client ./{kit.cmd}/server; " +
                f"for i in {ids}; do DSRIG_ID=$i /tmp/kn/server & done; /tmp/kn/client " +
                "(exit 0: the history checked; a panic otherwise)")
    # [prompt].nodetest: the kit's own node-test sentence, for a target whose nodes cannot share one
    # network namespace (QuePaxa listens on 0.0.0.0, so its replicas' ports collide on lo)
    nodetest_sentence = (f"To run the {n} nodes as separate processes at their real addresses, put the "
                         "addresses on the loopback interface once per sandbox start (you are root in the "
                         f"sandbox's own network namespace) and start the binaries: {nodetest}; then kill "
                         "the servers.")
    if pr.get("nodetest"):
        nodetest_sentence = pr["nodetest"].strip()
    k = int(t["k"])
    pinned = run.get("pinned", [])
    fields = {
        "url": tg["url"], "system": pr["system"].strip(), "repo": repo, "branch": tg["branch"],
        "base": tg["base"], "fork": pr["fork"].strip(), "nC": kit.nC,
        "k_ops": "one operation each" if k == 1 else f"{k} operations each",
        "pkg": t["pkg"], "adapter": pr["adapter"].strip(), "check": kit.chk["desc"],
        "servers": servers, "nnodes": n, "deployment": pr["deployment"].strip(),
        "prefix": kit.prefix, "new": t["new"], "op": t["op"], "gen": t["gen"], "start": t["start"],
        "nodetest_sentence": nodetest_sentence, "bugs": pr["bugs"].strip(),
        "pinned": pinned[0] if len(pinned) == 1 else ", ".join(pinned[:-1]) + " and " + pinned[-1],
        "system_code": (pr["system_code"].strip() + " ") if pr.get("system_code") else "",
        "beside": f"fork/{repo}, harness, src/perennial-netext and src/porcupine",
    }
    with open(PROMPT_TEMPLATE) as fp:
        tmpl = fp.read()
    return tmpl.format(**fields)


def nlines(path):
    with open(path, errors="replace") as fp:
        return sum(1 for _ in fp)


def patch_stats(path):
    """Added and removed lines of a patch, and the files it touches."""
    add = rem = 0
    files = []
    with open(path, errors="replace") as fp:
        for l in fp:
            if l.startswith("+++ b/"):
                files.append(l[6:].strip())
            elif l.startswith("+") and not l.startswith("+++"):
                add += 1
            elif l.startswith("-") and not l.startswith("---"):
                rem += 1
    return add, rem, files


def rpc_section_lines(path):
    """The lines of kit.toml's [rpc] section (up to the next top-level table)."""
    n, on = 0, False
    with open(path) as fp:
        for l in fp:
            if l.startswith("["):
                on = l.startswith("[rpc") or l.startswith("[[rpc")
            if on:
                n += 1
    return n


def json_section_lines(path):
    """The lines of kit.toml's [json] section (up to the next top-level table)."""
    n, on = 0, False
    with open(path) as fp:
        for l in fp:
            if l.startswith("["):
                on = l.startswith("[json")
            if on:
                n += 1
    return n


def uses_slog(kit, tree):
    """Whether a translated package of the target imports log/slog."""
    for p in kit.lean["goose_pkgs"]:
        if not p.startswith("."):
            continue
        for f in glob.glob(os.path.join(tree, p, "*.go")):
            if f.endswith("_test.go"):
                continue
            with open(f) as fp:
                if re.search(r'^\s*(import\s+)?"log/slog"', fp.read(), re.M):
                    return True
    return False


def audit(kit, tree):
    rel = lambda p: os.path.relpath(p, LAB)
    print(f"Audit list of {kit.name} (notes/kit-v2.md decision 7): what a person must read to trust")
    print("the theorem. Everything else is proved once in the harness, generated by kitgen from")
    print("kit.toml (kitgen --check), or proved by the run.\n")
    total = 0
    n = nlines(kit.toml_path)
    total += n
    print(f"1. the manifest: {rel(kit.toml_path)}  ({n} lines): the deployment, the model and")
    print("   checker, the constants, the input premise")
    print("\n2. the patches to the target (git am on "
          f"{kit.c['target']['base']}), each with its reason:")
    adapter = []
    proved = []
    for p in kit.c["target"].get("patch", []):
        path = os.path.join(kit.dir, p["file"])
        add, rem, files = patch_stats(path)
        if p.get("proved"):
            # code the kit adds that the run proves like the target's (not read to trust the theorem)
            proved.append((p, add, rem, files))
            continue
        total += add + rem
        print(f"   - {p['file']}  (+{add} -{rem}; {', '.join(files)})")
        print(f"     why: {p['why']}")
        if p.get("adapter"):
            adapter += [f for f in files if f.endswith(".go") and not f.endswith("_test.go")
                        and f not in adapter]   # (a stage's patch may change a file again)
    print("\n3. the adapter (the Go code the theorem is about but the run does not prove correct):")
    for f in adapter:
        path = os.path.join(tree, f)
        if os.path.exists(path):
            print(f"   - {f}  ({nlines(path)} lines, in the adapter patch above): "
                  f"{kit.test['new']}, {kit.test['op']}, {kit.test['gen']}, {kit.test['start']}, "
                  "the server functions")
        else:
            print(f"   - {f}  (in the adapter patch above)")
    if proved:
        print("\n   Not on the list: the kit's patches whose code the run proves like the target's")
        print("   (translated by Goose and proved; not trusted, not counted):")
        for p, add, rem, files in proved:
            print(f"   - {p['file']}  (+{add} -{rem}; {', '.join(files)})")
            print(f"     why: {p['why']}")
    print("\n4. trusted library models the kit adds: " +
          (", ".join(kit.c.get("models", [])) or "none"))
    print("\n5. trusted claims the theorem rests on beyond the harness's net model:")
    claims = 0
    if "trusted" in kit.chk:
        f, name, what = kit.chk["trusted"]
        print(f"   - {what}: {name} in {f} (model {kit.test['model']})")
        claims += 1
    lg = os.path.join(LAB, "harness/rpcmodel/src/log/log.go")
    print(f"   - {rel(lg)}  ({nlines(lg)} lines): the lab's model of Go's log, translated in place")
    print("     of the real package for every package (its specs are proved in the harness,")
    print("     Harness/Proof/log.lean). Claim: real log and fmt run no code of the program other")
    print("     than the arguments' Error()/String() methods, which the model calls on every argument")
    print("     (at least where fmt does; tested, not proved: rpcmodel/difftest/log_test.go); the")
    print("     model's panic in Fatal*/Panic* is the lab's choice (a stricter semantics than exit).")
    claims += 1
    if kit.rpc:
        T = kit.rpc
        n = rpc_section_lines(kit.toml_path)
        print(f"   - the [rpc] section of kit.toml ({n} lines, counted in 1): {rpcgen.audit_lines(T)}.")
        print("     Claim: for exactly these types, the generated codec (rpc_gen.go) round-trips as")
        print("     gob does (encode, then decode into a zero value or a gob-compatible type, gives")
        print("     gob's result), and its dispatch table is net/rpc's (the registered receivers'")
        print("     suitable methods, with their argument and reply types). Tested, not proved:")
        print(f"     {kit.test['pkg']}/rpc_gen_test.go against real encoding/gob and reflection.")
        print("   - harness/rpcmodel: the lab's net/rpc and net/http models (Go, translated in place")
        print("     of the real packages; their specs are proved in the harness). Claim: they behave")
        print("     as Go's for the calls the kit makes (tested, not proved: rpcmodel/difftest runs")
        print("     the same calls against both):")
        for f in sorted(glob.glob(os.path.join(LAB, "harness/rpcmodel/src/net/*/*.go"))):
            print(f"       {rel(f)}  ({nlines(f)} lines)")
        if T.gob:
            g = os.path.join(LAB, "harness/rpcmodel/src/encoding/gob/gob.go")
            print(f"   - {rel(g)}  ({nlines(g)} lines): the lab's model of encoding/gob ([rpc] gob),")
            print("     translated with the target (the run proves what it uses). Claim: with the kit's")
            print("     codec, a fresh Encoder's Encode and a fresh Decoder's Decode carry a listed value")
            print("     over a byte stream as gob does, Decode reading exactly the value's bytes (tested, not")
            print("     proved: rpcmodel/difftest/gob against Go's gob; the codec by rpc_gen_test.go)")
        else:
            g = os.path.join(LAB, "harness/lean/Harness/TrustedCode/encoding/gob.lean")
            print(f"   - {rel(g)}  ({nlines(g)} lines): encoding/gob's package initialization is a")
            print("     no-op (gob is imported but the model's codec replaces it)")
        claims += 3
    if kit.json:
        T = kit.json
        n = json_section_lines(kit.toml_path)
        print(f"   - the [json] section of kit.toml ({n} lines, counted in 1): {jsongen.audit_lines(T)}.")
        print("     Claim: the listed structure is the Go types' (fields, types, tags, MarshalJSON and")
        print("     UnmarshalJSON methods), and for exactly these types the generated codec")
        print("     (json_gen.go) encodes as real encoding/json does, byte for byte, and decodes as it")
        print("     does (the value, and error or not), within the plain subset (it panics outside).")
        print(f"     Tested, not proved: {kit.test['pkg']}/json_gen_test.go against real encoding/json.")
        jc = os.path.join(LAB, "harness/jsoncodec/jsoncodec.go")
        print(f"   - {rel(jc)}  ({nlines(jc)} lines): the JSON scanner and the codec's helpers")
        print("     (translated and proved in the harness). Claim: they are real encoding/json's")
        print("     syntax (Scan, Valid) and encodings within the plain subset; tested, not proved:")
        print("     harness/jsoncodec/jsoncodec_test.go and the kit's codec test.")
        print("   - harness/rpcmodel/src/encoding/json: the lab's model of encoding/json (Go, translated")
        print("     in place of the real package; its specs are proved in the harness). Claim: Marshal,")
        print("     Unmarshal, Valid, RawMessage, Encoder and Decoder behave as Go's for the kit's calls,")
        print("     with the codec in place of reflection (a Decoder may read ahead as Go's may);")
        print("     tested, not proved: rpcmodel/difftest/json_test.go runs the same calls against both:")
        for f in sorted(glob.glob(os.path.join(LAB, "harness/rpcmodel/src/encoding/json/*.go"))):
            print(f"       {rel(f)}  ({nlines(f)} lines)")
        claims += 3
    if kit.protobuf:
        print(f"   - the [protobuf] section of kit.toml (counted in 1): {pbgen.audit_lines(kit.protobuf)}.")
        print("     Claim: the listed fields are the generated messages' (checked against their")
        print("     descriptors), and for exactly these types the generated codec (pb_gen.go) encodes")
        print("     as real proto.Marshal does, byte for byte, and decodes as proto.Unmarshal does (the")
        print("     value modulo unknown fields, and error or not). Tested, not proved:")
        print(f"     {kit.test['pkg']}/pb_gen_test.go against real google.golang.org/protobuf.")
        pc = os.path.join(LAB, "harness/pbcodec/pbcodec.go")
        print(f"   - {rel(pc)}  ({nlines(pc)} lines): the codec's wire helpers (translated); claim:")
        print("     protowire's and unicode/utf8's behavior; tested against them (pbcodec's tests).")
        print("   - harness/rpcmodel/grpc and harness/rpcmodel/protobuf: the lab's models of")
        print("     google.golang.org/grpc (unary) and protobuf (proto.Marshal/Unmarshal), translated in")
        print("     place of the real modules (go.model.mod) and proved in the harness")
        print("     (Harness/Proof/grpc). Claim: the calls behave as the real ones for the kit's use")
        print("     (notes/grpc-model.md); tested, not proved: harness/rpcmodel/grpcdifftest/run.sh:")
        for f in sorted(glob.glob(os.path.join(LAB, "harness/rpcmodel/grpc/*.go")) +
                        glob.glob(os.path.join(LAB, "harness/rpcmodel/grpc/*/*.go")) +
                        glob.glob(os.path.join(LAB, "harness/rpcmodel/grpc/*/*/*.go")) +
                        glob.glob(os.path.join(LAB, "harness/rpcmodel/protobuf/*/*.go")) +
                        glob.glob(os.path.join(LAB, "harness/rpcmodel/protobuf/*/*/*.go"))):
            print(f"       {rel(f)}  ({nlines(f)} lines)")
        claims += 3
    if uses_slog(kit, tree):
        sl = os.path.join(LAB, "harness/rpcmodel/src/log/slog/slog.go")
        print(f"   - {rel(sl)}  ({nlines(sl)} lines): the lab's model of Go's log/slog, translated in")
        print("     place of the real package (its specs are proved in the harness). Claim: real slog")
        print("     runs no code of the program other than the arguments' Error()/String() methods,")
        print("     which the model calls on every argument (at least where real slog does), and panics")
        print("     where Go does (New(nil), a nil *Logger); tested, not proved:")
        print("     rpcmodel/difftest/slog_test.go.")
        claims += 1
    if UUID_PKG in kit.lean.get("harness_pkgs", []):
        u = os.path.join(LAB, "harness/rpcmodel/uuid/uuid.go")
        print(f"   - {rel(u)}  ({nlines(u)} lines): the lab's model of github.com/google/uuid v1.3.1")
        print("     (the go.mod's replace; translated and proved in the harness, Harness/Proof/uuid).")
        print("     Claim: for New, NewRandom, NewString, Must, ID, Time, Version, Variant and String")
        print("     it is v1.3.1's code, but that its random bytes are two primitive.RandomUint64s")
        print("     (arbitrary in the theorem) and that NewRandom's error is nil (crypto/rand cannot")
        print("     fail); tested, not proved: rpcmodel/difftest/uuid against the real v1.3.1.")
        claims += 1
    for hp in kit.lean.get("harness_pkgs", []):
        t = os.path.join(LAB, "harness/lean/Harness/TrustedCode", hp + ".lean")
        if os.path.exists(t):
            print(f"   - {rel(t)}  ({nlines(t)} lines): {hp}'s trusted definitions in the harness "
                  "(the file's header says what they claim)")
            claims += 1
        # an axiomatized spec of a library in the harness (Harness/Spec/<pkg>.lean; crypto/sha256's)
        a = os.path.join(LAB, "harness/lean/Harness/Spec", hp + ".lean")
        if os.path.exists(a):
            print(f"   - {rel(a)}  ({nlines(a)} lines): {hp}'s axiomatized spec in the harness "
                  "(axioms; the file's header says what they claim and why they are consistent)")
            claims += 1
    for m, c in kit.extras:
        t = os.path.join(LAB, "harness/lean", *m.split(".")) + ".lean"
        print(f"   - {rel(t)}  ({nlines(t) if os.path.exists(t) else '?'} lines): `{c}`, a node "
              "assumption: goose's translation (or the")
        print("     harness's model) of library functions the pinned Perennial has as names only "
              "(the file's header says which and what it claims)")
        claims += 1
    for f, content in trusted_init_files(kit):
        if "/ManualProof/" in f:
            continue   # empty modules
        print(f"   - kits/{os.path.basename(kit.dir)}/gen/lean/{f}  ({content.count(chr(10))} lines, "
              "generated from lean.trusted_init): the package's")
        print("     initialization is a no-op (protoc-gen-go's descriptor registration, or a names-only "
              "library's tables)")
        claims += 1
    if not claims:
        print("   none")
    print(f"\nTotal: {total} lines (kit.toml plus the patches' changed lines).")
    print("\nNot on the list (for reference):")
    for path, content, _ in outputs(kit, tree):
        print(f"   generated  {rel(path) if path.startswith(LAB) else path}  "
              f"({content.count(chr(10))} lines)")
    print("   harness    harness/driver/driver.go, harness/lean/Harness/Driver.lean (driver.Run's "
          "spec, driver_dist_safe), harness/kitgen/kitgen.py: audited once for every kit")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("kitdir")
    ap.add_argument("--tree", help="the target's work tree (default: kit.toml's target.dev)")
    m = ap.add_mutually_exclusive_group()
    m.add_argument("--check", action="store_true", help="exit 1 unless the files are current")
    m.add_argument("--audit", action="store_true", help="print the audit list")
    a = ap.parse_args()
    kit = Kit(a.kitdir)
    tree = os.path.abspath(a.tree or kit.tree_default())
    if a.audit:
        audit(kit, tree)
        return
    stale = []
    for path, content, mode in outputs(kit, tree):
        cur = None
        if os.path.exists(path):
            with open(path) as fp:
                cur = fp.read()
        if a.check:
            if cur != content:
                stale.append(path)
            continue
        if cur != content:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fp:
                fp.write(content)
            print(f"wrote {path}")
        os.chmod(path, mode)
    if a.check:
        if stale:
            for p in stale:
                print(f"kitgen: not current: {p}", file=sys.stderr)
            sys.exit(1)
        print(f"kitgen: {kit.name}: every generated file is current")


if __name__ == "__main__":
    main()
