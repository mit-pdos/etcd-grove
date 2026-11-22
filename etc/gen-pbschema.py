#!/usr/bin/env python3
"""Generate the trusted protobuf schemas of `Proof/google_golang_org/protobuf/proto/PbSchema.lean`
from the registered descriptors (`models/pbdesc`, the one descriptor source: the dump pbgen reads).

The schemas (`FieldSchema`, `UfWire.lean`: each declared field number with the wire types
protobuf-go's decoder takes for it) and `pbSchemaOf` (which Go type has which schema) are written
between the file's two marker lines (`-- BEGIN etc/gen-pbschema.py` ... `-- END etc/gen-pbschema.py`);
the rest of the file (its header, the lemmas `pbSchemaOf_*`, the `PbGoType` instances) is
hand-written. Never edit the region by hand: change `TYPES` below (which message types get a
schema, under which Lean name) and rerun.

What is derived, per field of each type's descriptor (as `examples/pbschema/descriptor_test.go`'s
`wireTypes`, which reads protobuf-go v1.36.12's coders: `internal/impl/codec_tables.go`'s
`fieldCoder`, the consumers of `internal/impl/codec_gen.go`): its number, and the wire types its
decoder takes: a varint kind (`bool`, `enum`, `int32`, `sint32`, `uint32`, `int64`, `sint64`,
`uint64`) 0, `fixed64`/`sfixed64`/`double` 1, `fixed32`/`sfixed32`/`float` 5, `string`/`bytes`/a
message 2, a group 3; a map field 2; a repeated field of a scalar kind (not 2 or 3) both its own
wire type and 2 (packed or not: protobuf-go's slice consumers take both, e.g. `consumeUint64Slice`).
Fields are listed by increasing number. Every message type a listed type's fields reach must be
listed too (else `pbSchemaOf` would give it `[]`): the script refuses a dump where one is not.

    etc/gen-pbschema.py            rewrite the region (runs `go run` in examples/, GOWORK=off)
    etc/gen-pbschema.py --check    write nothing; exit 1 if the region differs
    etc/gen-pbschema.py --dump F   read a saved pbdesc dump (JSON) instead of running Go
    etc/gen-pbschema.py --print-dump

The dump runs in the examples' Go module (`examples/go.mod`: the etcd and raft pins, `models.lab`
by a `replace`), with Go `etc/goose.py`'s `GO_TOOLCHAIN` (`$GOTOOLCHAIN` overrides). The RaftNoAx
copy of the file is `etc/copy-part.py`'s: rerun it after a change.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
TARGET = "Proof/google_golang_org/protobuf/proto/PbSchema.lean"
BEGIN = "-- BEGIN etc/gen-pbschema.py"
END = "-- END etc/gen-pbschema.py"

# The message types with a schema: (protobuf full name, Go root "import/path.GoType", Lean name),
# in the order of the file. The Lean expression of a Go type is its translation's name with the
# namespace the file opens (`OPEN`) stripped.
TYPES = [
    ("raftpb.Entry", "go.etcd.io/raft/v3/raftpb.Entry", "entrySchema"),
    ("raftpb.Message", "go.etcd.io/raft/v3/raftpb.Message", "msgSchema"),
    ("raftpb.Snapshot", "go.etcd.io/raft/v3/raftpb.Snapshot", "snapSchema"),
    ("raftpb.SnapshotMetadata", "go.etcd.io/raft/v3/raftpb.SnapshotMetadata", "metaSchema"),
    ("raftpb.ConfState", "go.etcd.io/raft/v3/raftpb.ConfState", "csSchema"),
    ("raftpb.HardState", "go.etcd.io/raft/v3/raftpb.HardState", "hsSchema"),
    ("raftpb.ConfChange", "go.etcd.io/raft/v3/raftpb.ConfChange", "ccSchema"),
    ("raftpb.ConfChangeSingle", "go.etcd.io/raft/v3/raftpb.ConfChangeSingle", "ccsSchema"),
    ("raftpb.ConfChangeV2", "go.etcd.io/raft/v3/raftpb.ConfChangeV2", "cc2Schema"),
    ("walpb.Record", "go.etcd.io/etcd/server/v3/storage/wal/walpb.Record", "WalEnc.recSchema"),
    ("walpb.Snapshot", "go.etcd.io/etcd/server/v3/storage/wal/walpb.Snapshot", "WalEnc.walSnapSchema"),
]
OPEN = "go_etcd_io.raft.v3."

VARINT = {"bool", "enum", "int32", "sint32", "uint32", "int64", "sint64", "uint64"}
FIXED64 = {"fixed64", "sfixed64", "double"}
FIXED32 = {"fixed32", "sfixed32", "float"}
LEN = {"string", "bytes", "message"}


class GenError(Exception):
    pass


def wire_types(f):
    k = f["kind"]
    if k in VARINT:
        wt = 0
    elif k in FIXED64:
        wt = 1
    elif k in FIXED32:
        wt = 5
    elif k in LEN:
        wt = 2
    elif k == "group":
        wt = 3
    else:
        raise GenError(f"field {f['name']}: unknown kind {k!r}")
    if f["is_map"]:
        return [2]
    if f["cardinality"] == "repeated" and wt not in (2, 3):
        return [wt, 2]
    return [wt]


def lean_go_type(g):
    """The Lean name of a Go type's `.ty` (`go.etcd.io/raft/v3/raftpb` `Entry` ->
    `raftpb.Entry.ty`, the file opening `go_etcd_io.raft.v3`)."""
    path = g["pkg"]
    first, *rest = path.split("/")
    full = ".".join([first.replace(".", "_").replace("-", "_")] + [p.replace(".", "_").replace("-", "_") for p in rest])
    full += "." + g["name"] + ".ty"
    return full[len(OPEN):] if full.startswith(OPEN) else full


def field_doc(f):
    card = f["cardinality"]
    kind = f["kind"]
    if kind == "message" and f.get("message"):
        kind = f["message"]
    elif kind == "enum" and f.get("enum"):
        kind = f"enum {f['enum']}"
    extra = ""
    if card == "repeated" and f["kind"] not in ("string", "bytes", "message", "group"):
        extra = ", packed" if f["packed"] else ", unpacked"
    if f.get("oneof") and not f.get("synthetic_oneof"):
        extra += f", oneof {f['oneof']}"
    return f"{f['number']} `{f['name']}` ({card} {kind}{extra})"


def render(dump):
    msgs = {m["full_name"]: m for m in dump["messages"]}
    names = {t[0] for t in TYPES}
    for fn, _, _ in TYPES:
        if fn not in msgs:
            raise GenError(f"{fn}: not in the descriptor dump")
    for m in dump["messages"]:
        if m["full_name"] not in names:
            raise GenError(f"{m['full_name']}: reached by a listed type's field, but has no schema "
                           "in TYPES (pbSchemaOf would give it [])")
    out = [BEGIN + " (from the registered descriptors, models/pbdesc: do not edit, rerun it)", ""]
    for fn, root, lean in TYPES:
        m = msgs[fn]
        if m["go"] is None:
            raise GenError(f"{fn}: no registered Go type")
        if m["go"]["pkg"] + "." + m["go"]["name"] != root:
            raise GenError(f"{fn}: its Go type is {m['go']['pkg']}.{m['go']['name']}, TYPES says {root}")
        fs = sorted(m["fields"], key=lambda f: f["number"])
        nums = [f["number"] for f in fs]
        if len(set(nums)) != len(nums):
            raise GenError(f"{fn}: a field number twice")
        sch = ", ".join(f"({f['number']}, [{', '.join(str(w) for w in wire_types(f))}])" for f in fs)
        doc = f"/-- `{fn}` (`{m['file']}`, {m['syntax']}): " + ", ".join(field_doc(f) for f in fs) + ". -/"
        out.append(wrap_doc(doc))
        out.append(wrap_def(f"def {lean} : FieldSchema := [{sch}]"))
        out.append("")
    out.append("section schemas")
    out.append("variable [GooseExts] [GoGlobalContext]")
    out.append("")
    out.append("/-- **The schema of a message type** (see the file header): "
               + ", ".join(f"`{fn}`'s" for fn, _, _ in TYPES) + "; `[]` for every other type. -/")
    out[-1] = wrap_doc(out[-1])
    out.append("def pbSchemaOf (ty : go.GoType) : FieldSchema :=")
    out.append("  open Classical in")
    for i, (fn, _, lean) in enumerate(TYPES):
        kw = "if" if i == 0 else "else if"
        out.append(f"  {kw} ty = {lean_go_type(msgs[fn]['go'])} then {lean}")
    out.append("  else []")
    out.append("")
    out.append(END)
    return "\n".join(out) + "\n"


def wrap(text, indent="", width=100):
    """Greedy word wrap at `width`, continuation lines indented by `indent`."""
    lines, cur = [], ""
    for w in text.split(" "):
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = indent + w
        else:
            cur = cur + " " + w if cur else w
    lines.append(cur)
    return "\n".join(lines)


def wrap_doc(doc):
    return wrap(doc)


def wrap_def(d):
    """`def X : FieldSchema := [...]`, the list on the next lines, broken between pairs, when it
    does not fit (as the hand-written `msgSchema` was)."""
    if len(d) <= 100:
        return d
    head, body = d.split(" := ", 1)
    items = re.findall(r"\(\d+, \[[0-9, ]*\]\)", body)
    lines, cur = [], "  ["
    for i, it in enumerate(items):
        piece = it + ("]" if i == len(items) - 1 else ",")
        if len(cur) + (1 if cur.strip() not in ("[", "") else 0) + len(piece) > 100:
            lines.append(cur)
            cur = "   " + piece
        else:
            cur = cur + piece if cur.endswith("[") else cur + " " + piece
    lines.append(cur)
    return head + " :=\n" + "\n".join(lines)


def go_toolchain():
    m = re.search(r'^GO_TOOLCHAIN = "([^"]+)"', open(os.path.join(ROOT, "etc", "goose.py")).read(), re.M)
    if not m:
        raise GenError("no GO_TOOLCHAIN in etc/goose.py")
    return os.environ.get("GOTOOLCHAIN", m.group(1))


def derive():
    """pbdesc's dump of TYPES' roots, run in the examples' Go module."""
    mod = os.path.join(ROOT, "examples")
    tmp = tempfile.mkdtemp(prefix="_pbschemadump", dir=mod)
    try:
        pkgs = sorted({r.rsplit(".", 1)[0] for _, r, _ in TYPES})
        with open(os.path.join(tmp, "main.go"), "w") as fh:
            fh.write("package main\n\nimport (\n\t\"models.lab/pbdesc\"\n")
            for p in pkgs:
                fh.write(f"\t_ \"{p}\"\n")
            fh.write(")\n\nfunc main() { pbdesc.Main() }\n")
        env = dict(os.environ, GOWORK="off", GOTOOLCHAIN=go_toolchain(),
                   PATH="/usr/local/go/bin:" + os.path.expanduser("~/go/bin") + ":" + os.environ.get("PATH", ""))
        r = subprocess.run(["go", "run", "./" + os.path.basename(tmp)] + [r for _, r, _ in TYPES],
                           cwd=mod, env=env, capture_output=True, text=True)
        if r.returncode != 0:
            raise GenError(f"the descriptor dump failed (go run in {mod}):\n{r.stderr}")
        return json.loads(r.stdout)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def splice(cur, region):
    lines = cur.split("\n")
    b = [i for i, l in enumerate(lines) if l.startswith(BEGIN)]
    e = [i for i, l in enumerate(lines) if l.startswith(END)]
    if len(b) != 1 or len(e) != 1 or b[0] > e[0]:
        raise GenError(f"{TARGET}: expected one `{BEGIN}` line before one `{END}` line")
    return "\n".join(lines[:b[0]]) + "\n" + region + "\n".join(lines[e[0] + 1:])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--dump")
    ap.add_argument("--print-dump", action="store_true")
    a = ap.parse_args()
    try:
        if a.dump:
            dump = json.load(open(a.dump))
        else:
            dump = derive()
        if a.print_dump:
            json.dump(dump, sys.stdout, indent=1)
            print()
            return 0
        region = render(dump)
        path = os.path.join(ROOT, TARGET)
        cur = open(path, encoding="utf-8").read()
        new = splice(cur, region)
    except GenError as e:
        print(f"gen-pbschema: FAILED: {e}", file=sys.stderr)
        return 1
    if new == cur:
        print(f"gen-pbschema: ok ({len(TYPES)} schemas of {TARGET} agree with their descriptors)")
        return 0
    if a.check:
        print(f"gen-pbschema: FAILED: {TARGET} differs from the descriptors' schemas (rerun etc/gen-pbschema.py)")
        return 1
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(new)
    print(f"gen-pbschema: wrote {TARGET}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
