#!/usr/bin/env python3
"""pbgen: a protobuf codec, plain Go code per message type, from a [protobuf] table.

A model of google.golang.org/protobuf replaces reflection by a codec the program registers: an
encoder and a decoder for exactly the listed message types, over the wire-format helpers of
`netmodels.lab/pbcodec` (`netmodels/`, translated into the part `Net/`). This script generates the
codec, and the Go tests that check its trusted claims against the real module (v1.36.12): the
listed fields of each type are the message's (its descriptor: names, numbers, kinds,
cardinality, packedness, message and enum types; the Go struct: field names, Go types, tags), the
codec's Marshal of random values is real proto.Marshal's byte for byte (and nil-or-not), its
Unmarshal of real encodings of every listed type into every listed type (fresh and pre-filled
targets), and of mutations of them (truncations, byte changes, unknown fields of every wire type
including nested groups, repeated and reordered fields, packed and unpacked encodings, wrong wire
types, overlong varints, bad field numbers, invalid UTF-8, nesting at and past the recursion
limit), gives real proto.Unmarshal's error-or-not and, on success, its value (unknown fields
aside). Ported from dsverify-lab's `harness/kitgen/pbgen.py` (`348a866`), with no change to what
it generates but the import path of pbcodec, the comments, and the registration files made
optional (`--register`).

Use:

    etc/pbgen.py SECTION.toml OUTDIR --pkg NAME [--register] [--check]

writes into the Go package directory OUTDIR (package NAME, which must import the listed message
packages) `pb_gen.go` (the codec: `pbMarshal`, `pbUnmarshal`) and `pb_gen_test.go` (its tests
against the real module, `go test` in OUTDIR's module, which requires google.golang.org/protobuf);
with `--register` also `pb_model_gen.go`/`pb_real_gen.go` (`registerProto()`: the codec registered
with the model of google.golang.org/protobuf, `proto.SetCodec`, in a model build (tag `rpcmodel`
or `goose`); nothing in a real build). `--check` writes nothing and exits 1 if a file differs.
`etc/pbgen.py --from-pb FILE.pb.go... [--import ALIAS=PATH]` prints a [protobuf] table derived
from protoc-gen-go's generated structs (a starting point; the toml stays the audited source), and
lists as REFUSED the fields outside the subset. Examples: `netmodels/internal/pbdifftest/` (the
field kinds) and `examples/netmodels/pbetcd/` (etcd's message types).

The [protobuf] table (in any toml file):

    [protobuf]
    imports = { raxos = "raxos/replica/src/proto" }    # Go package aliases used below
    enums = ["pb.Op"]                                   # the listed enum types (Go types)
    [protobuf.messages]
    "raxos.ProposerMessage" = [["Sender", 1, "int64"], ["P", 3, "raxos.ProposerMessage_Proposal"],
                               ["DecidedSlots", 5, "[]raxos.ProposerMessage_DecidedSlot"]]
    "pb.Args" = [["Op", 4, "pb.Op"], ["Xs", 8, "[]int64"], ["Blob", 6, "bytes"]]

A message's fields are [GoName, field number, kind], all of the message's fields. A kind is a
scalar (int32 int64 uint32 uint64 sint32 sint64 fixed32 fixed64 sfixed32 sfixed64 bool string
bytes), a listed enum type, a listed message type T (the Go field is *T), or []K for a repeated
field of kind K ([]T: the Go field is []*T; repeated scalars and enums are packed, as proto3's
default). `pbgen.py --from-pb FILE.pb.go...` prints a [protobuf] section derived from the
generated structs' tags, as a starting point; the toml stays the audited source.

The subset: proto3 messages with implicit presence. Refused (an error here, or the generated
shape test fails): proto2 and editions, oneofs, maps, `optional` (explicit presence), groups,
float and double, unpacked repeated scalars, extensions.

What the codec does, as the real module does (tested): Marshal writes fields in field-number
order, omits proto3's zero values, a nil message field, and an empty repeated field; a non-nil
empty nested message is written (tag, length 0); a nil element of a repeated message field is
written as an empty message (the real one does so); a nil *T marshals to nil, a non-nil empty
message to an empty non-nil slice; a string that is not UTF-8 is an error. Unmarshal panics on
a nil *T (the real one's Reset does), resets *T, then merges each field occurrence: scalars last
wins, a message field merges into the one already there, repeated fields append, packed and
unpacked occurrences both accepted; a known field number with another wire type is an unknown
field; unknown fields are checked (protowire's ConsumeFieldValue: groups nested up to its limit)
and dropped (the real one keeps them in the message's unknown fields, and Marshal writes them
back: the model does neither; the tests compare values with the real one's without them); an
error where the real one errs: a malformed tag, value or length, a field number 0 or above
2^29-1, an end-group tag, a reserved wire type, invalid UTF-8 in a string field, messages nested
deeper than 10000.
Error values are the codec's own (only error-or-not is modeled). An empty bytes field decodes to
nil, an empty element of a repeated bytes field to a non-nil empty slice (the real one's).
"""

import argparse
import os
import re
import sys
import tomllib

MAX_NUM = (1 << 29) - 1

# scalar kind: (Go type, wire type, protoreflect kind, encode (x: the Go value) to the wire
# value, decode (v: the wire value) to the Go value, zero test)
SCALARS = {
    "int32": ("int32", "VarintType", "Int32Kind", "uint64(int64({x}))", "int32({v})"),
    "int64": ("int64", "VarintType", "Int64Kind", "uint64({x})", "int64({v})"),
    "uint32": ("uint32", "VarintType", "Uint32Kind", "uint64({x})", "uint32({v})"),
    "uint64": ("uint64", "VarintType", "Uint64Kind", "{x}", "{v}"),
    "sint32": ("int32", "VarintType", "Sint32Kind", "pbcodec.EncodeZigZag(int64({x}))",
               "pbcodec.DecodeZigZag32({v})"),
    "sint64": ("int64", "VarintType", "Sint64Kind", "pbcodec.EncodeZigZag({x})", "pbcodec.DecodeZigZag({v})"),
    "bool": ("bool", "VarintType", "BoolKind", "pbcodec.EncodeBool({x})", "{v} != 0"),
    "fixed32": ("uint32", "Fixed32Type", "Fixed32Kind", "{x}", "{v}"),
    "sfixed32": ("int32", "Fixed32Type", "Sfixed32Kind", "uint32({x})", "int32({v})"),
    "fixed64": ("uint64", "Fixed64Type", "Fixed64Kind", "{x}", "{v}"),
    "sfixed64": ("int64", "Fixed64Type", "Sfixed64Kind", "uint64({x})", "int64({v})"),
    "string": ("string", "BytesType", "StringKind", None, None),
    "bytes": ("[]byte", "BytesType", "BytesKind", None, None),
}

REFUSED_KINDS = {
    "float": "float fields are outside the model's subset",
    "double": "double fields are outside the model's subset",
    "group": "groups are outside the model's subset (proto2)",
}


class PbError(Exception):
    pass


def ident(name):
    """A Go identifier for a type name: raxos.ProposerMessage -> raxos_ProposerMessage."""
    return re.sub(r"[^A-Za-z0-9]", "_", name)


def go_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


class Field:
    def __init__(self, name, num, kind, rep, cat):
        self.name = name   # Go field name
        self.num = num     # field number
        self.kind = kind   # the element kind: a scalar's name, or a listed enum or message type
        self.rep = rep     # repeated
        self.cat = cat     # "scalar", "enum" or "message"

    @property
    def packed(self):
        return self.rep and self.cat != "message" and self.kind not in ("string", "bytes")

    def wire(self):
        """The wire type of an element (a scalar's, varint for an enum, bytes for a message)."""
        if self.cat == "scalar":
            return SCALARS[self.kind][1]
        if self.cat == "enum":
            return "VarintType"
        return "BytesType"

    def elem_go(self):
        if self.cat == "scalar":
            return SCALARS[self.kind][0]
        if self.cat == "enum":
            return self.kind
        return "*" + self.kind

    def go_type(self):
        return ("[]" if self.rep else "") + self.elem_go()

    def pr_kind(self):
        if self.cat == "scalar":
            return SCALARS[self.kind][2]
        return "EnumKind" if self.cat == "enum" else "MessageKind"


class Messages:
    """A [protobuf] table, checked."""

    def __init__(self, pb):
        if not isinstance(pb, dict):
            raise PbError("[protobuf] is a table")
        hints = {"syntax": "only proto3 is in the subset (no syntax key: proto3 is implied)",
                 "oneofs": "oneofs are outside the model's subset",
                 "maps": "maps are outside the model's subset",
                 "extensions": "extensions are outside the model's subset"}
        for k in pb:
            if k not in ("imports", "enums", "messages"):
                raise PbError(f"[protobuf]: unknown key {k!r}" + (f" ({hints[k]})" if k in hints else ""))
        self.imports = dict(pb.get("imports", {}))
        for a, p in self.imports.items():
            if not re.fullmatch(r"[A-Za-z_]\w*", a) or not isinstance(p, str) or not p:
                raise PbError(f"[protobuf].imports: {a} = {p!r}: an alias and an import path")
        self.enums = list(pb.get("enums", []))
        for e in self.enums:
            self.check_name(e, "enum")
        decl = pb.get("messages", {})
        if not decl:
            raise PbError("[protobuf.messages] is empty")
        for n in decl:
            self.check_name(n, "message")
            if n in self.enums:
                raise PbError(f"{n}: listed as both a message and an enum")
        self.names = list(decl)
        self.m = {n: self.parse_fields(n, decl[n]) for n in self.names}
        used = {f.kind for fs in self.m.values() for f in fs if f.cat == "enum"}
        for e in self.enums:
            if e not in used:
                raise PbError(f"enum {e}: no listed field has it")

    def check_name(self, n, what):
        m = re.fullmatch(r"([A-Za-z_]\w*)\.([A-Za-z_]\w*)", n) if isinstance(n, str) else None
        if not m:
            raise PbError(f"{what} {n!r}: pkg.T (a Go type, package alias from [protobuf].imports)")
        if m.group(1) not in self.imports:
            raise PbError(f"{what} {n}: package {m.group(1)} not in [protobuf].imports")

    def parse_fields(self, n, fields):
        if not isinstance(fields, list):
            raise PbError(f"message {n}: a list of [GoName, number, kind]")
        out = []
        for f in fields:
            if not isinstance(f, list) or len(f) != 3:
                raise PbError(f"message {n}: field {f!r}: [GoName, number, kind]")
            name, num, kind = f
            if not isinstance(name, str) or not re.fullmatch(r"[A-Z]\w*", name):
                raise PbError(f"message {n}: field {f!r}: an exported Go field name")
            if not isinstance(num, int) or isinstance(num, bool) or not 1 <= num <= MAX_NUM or 19000 <= num <= 19999:
                raise PbError(f"{n}.{name}: field number {num!r}: 1..2^29-1, not 19000..19999")
            if not isinstance(kind, str):
                raise PbError(f"{n}.{name}: kind {kind!r}: a string")
            out.append(self.parse_kind(n, name, num, kind))
        nums = [f.num for f in out]
        names = [f.name for f in out]
        if len(set(nums)) != len(nums):
            raise PbError(f"message {n}: a field number twice")
        if len(set(names)) != len(names):
            raise PbError(f"message {n}: a field name twice")
        return sorted(out, key=lambda f: f.num)

    def parse_kind(self, n, name, num, kind):
        k = kind.strip()
        where = f"{n}.{name}"
        low = k.lower()
        if low.startswith("optional"):
            raise PbError(f"{where}: {kind!r}: explicit presence (optional) is outside the model's subset")
        if low.startswith("map") or k.startswith("map["):
            raise PbError(f"{where}: {kind!r}: maps are outside the model's subset")
        if low.startswith("oneof"):
            raise PbError(f"{where}: {kind!r}: oneofs are outside the model's subset")
        rep = k.startswith("[]")
        base = k[2:] if rep else k
        if base in REFUSED_KINDS:
            raise PbError(f"{where}: {kind!r}: {REFUSED_KINDS[base]}")
        if base.startswith("[]") or base.startswith("*"):
            raise PbError(f"{where}: {kind!r}: a scalar, a listed type, or [] of one")
        if base in SCALARS:
            return Field(name, num, base, rep, "scalar")
        if base in self.enums:
            return Field(name, num, base, rep, "enum")
        if base in self.names:
            return Field(name, num, base, rep, "message")
        raise PbError(f"{where}: kind {kind!r}: not a scalar ({', '.join(SCALARS)}), "
                      "a listed enum (enums) or a listed message ([protobuf.messages])")

    def cycle(self, n):
        """The Go field names and numbers of a shortest path of message fields from n back to n,
        or None."""
        from collections import deque
        q = deque([(n, [])])
        seen = set()
        while q:
            t, path = q.popleft()
            for f in self.m[t]:
                if f.cat != "message":
                    continue
                p2 = path + [(f.name, f.num)]
                if f.kind == n:
                    return p2
                if f.kind not in seen:
                    seen.add(f.kind)
                    q.append((f.kind, p2))
        return None

    def unknown_num(self):
        """A field number no listed message has."""
        used = {f.num for fs in self.m.values() for f in fs}
        k = 1
        while k in used:
            k += 1
        return k


# ---------------------------------------------------------------------------------------------
# The codec (pb_gen.go)

CODEC_DOC = """// The protobuf codec (registered with a model of google.golang.org/protobuf, proto.SetCodec):
// pbMarshal and pbUnmarshal for exactly the message types listed in [protobuf], over the wire
// format of netmodels.lab/pbcodec. The trusted claim, tested against the real
// google.golang.org/protobuf v1.36.12 by pb_gen_test.go (pbgen.py's doc):
//
//   - pbMarshal(m), m a *T of a listed type: real proto.Marshal(m)'s bytes (fields in number
//     order, proto3's zero values omitted, a nil element of a repeated message field written as
//     an empty message; nil for a nil *T, an empty non-nil slice for an empty message), or an
//     error where the real one errs (a string field that is not UTF-8).
//   - pbUnmarshal(b, m), m a non-nil *T of a listed type: resets *m and decodes b into it as
//     real proto.Unmarshal does (merging repeated occurrences), or an error where the real one
//     errs (malformed input, a field number 0 or above 2^29-1, invalid UTF-8 in a string field,
//     messages nested deeper than 10000). Unknown fields are checked and skipped (the real one
//     keeps them in the message: the model does not). A nil *T panics, as the real one does.
//   - Any other value (an unlisted type, a non-pointer, a nil interface) panics: outside the
//     subset.
//
// Only error-or-not is modeled, not the error values."""


def enc_scalar_lines(f, x):
    """Go statements appending element value x (of field f's element kind; not a message)."""
    w = f.wire()
    if f.kind == "string":
        return [f"if !pbcodec.ValidString({x}) {{", "\treturn b, false", "}",
                f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
                f"b = pbcodec.AppendString(b, {x})"]
    if f.kind == "bytes":
        return [f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)", f"b = pbcodec.AppendBytes(b, {x})"]
    return [f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.{w})", f"b = {append_value('b', f, x)}"]


def enc_expr(f, x):
    if f.cat == "enum":
        return f"uint64(int64({x}))"
    return SCALARS[f.kind][3].format(x=x)


def append_value(buf, f, x):
    """A Go expression: buf with the wire value of x (a numeric element of f) appended."""
    w = f.wire()
    if w == "VarintType":
        return f"pbcodec.AppendVarint({buf}, {enc_expr(f, x)})"
    if w == "Fixed32Type":
        return f"pbcodec.AppendFixed32({buf}, {enc_expr(f, x)})"
    return f"pbcodec.AppendFixed64({buf}, {enc_expr(f, x)})"


def zero_test(f, x):
    if f.kind in ("string", "bytes"):
        return f"len({x}) > 0"
    if f.kind == "bool":
        return x
    return f"{x} != 0"


def gen_encoder(P, n):
    I = ident(n)
    out = [f"// pbenc_{I} appends the encoding of *m's fields (real proto.Marshal's, in field-number",
           "// order); false if a string field is not UTF-8. A nil m encodes as an empty message.",
           f"func pbenc_{I}(b []byte, m *{n}) ([]byte, bool) {{",
           "\tif m == nil {", "\t\treturn b, true", "\t}"]
    body = []
    for f in P.m[n]:
        x = f"m.{f.name}"
        if f.cat == "message":
            sub = [f"sub, ok := pbenc_{ident(f.kind)}(make([]byte, 0), {'e' if f.rep else x})",
                   "if !ok {", "\treturn b, false", "}",
                   f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
                   "b = pbcodec.AppendBytes(b, sub)"]
            if f.rep:
                body += [f"for _, e := range {x} {{"] + ["\t" + l for l in sub] + ["}"]
            else:
                body += [f"if {x} != nil {{"] + ["\t" + l for l in sub] + ["}"]
        elif not f.rep:
            body += [f"if {zero_test(f, x)} {{"] + ["\t" + l for l in enc_scalar_lines(f, x)] + ["}"]
        elif not f.packed:
            body += [f"for _, e := range {x} {{"] + ["\t" + l for l in enc_scalar_lines(f, "e")] + ["}"]
        else:
            body += [f"if len({x}) > 0 {{", "\tp := make([]byte, 0)", f"\tfor _, e := range {x} {{",
                     f"\t\tp = {append_value('p', f, 'e')}", "\t}",
                     f"\tb = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
                     "\tb = pbcodec.AppendBytes(b, p)", "}"]
    out += ["\t" + l for l in body] + ["\treturn b, true", "}", ""]
    return out


def dec_elem_lines(f, v, assign):
    """Go statements decoding numeric element wire value v (from Consume...) and storing it
    with assign(expr)."""
    if f.cat == "enum":
        e = f"{f.kind}(int32({v}))"
    else:
        e = SCALARS[f.kind][4].format(v=v)
    return assign(e)


def consume_fn(f):
    return {"VarintType": "pbcodec.ConsumeVarint", "Fixed32Type": "pbcodec.ConsumeFixed32",
            "Fixed64Type": "pbcodec.ConsumeFixed64"}[f.wire()]


def gen_decoder(P, n):
    I = ident(n)
    out = [f"// pbdec_{I} decodes b into *m, merging into what is there, as the real Unmarshal does;",
           "// depth is the nesting the real Unmarshal still allows (this message included); false",
           "// where the real Unmarshal errs.",
           f"func pbdec_{I}(b []byte, m *{n}, depth uint64) bool {{",
           "\tif depth == 0 {", "\t\treturn false", "\t}",
           "\ti := uint64(0)",
           "\tfor i < uint64(len(b)) {",
           "\t\tnum, typ, n, ok := pbcodec.ConsumeFieldTag(b[i:])",
           "\t\tif !ok {", "\t\t\treturn false", "\t\t}",
           "\t\ti = i + n",
           "\t\tif typ == pbcodec.EndGroupType {", "\t\t\treturn false", "\t\t}",
           f"\t\tk, ok2 := pbdecField_{I}(b[i:], num, typ, m, depth)",
           "\t\tif !ok2 {", "\t\t\treturn false", "\t\t}",
           "\t\ti = i + k",
           "\t}",
           "\treturn true",
           "}", "",
           f"// pbdecField_{I} decodes the value of field num (wire type typ) at the start of b into",
           "// *m: the length of the value, or false. A field *m does not have, or one with another",
           "// wire type than its own (or than packed, for a packed field), is skipped (unknown).",
           f"func pbdecField_{I}(b []byte, num uint64, typ uint64, m *{n}, depth uint64) (uint64, bool) {{"]
    body = []
    for f in P.m[n]:
        x = f"m.{f.name}"
        w = f.wire()
        if f.cat == "message":
            body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                     "\tv, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
            if f.rep:
                body += [f"\te := &{f.kind}{{}}",
                         f"\tif !pbdec_{ident(f.kind)}(v, e, depth-1) {{", "\t\treturn 0, false", "\t}",
                         f"\t{x} = append({x}, e)"]
            else:
                body += [f"\tif {x} == nil {{", f"\t\t{x} = &{f.kind}{{}}", "\t}",
                         f"\tif !pbdec_{ident(f.kind)}(v, {x}, depth-1) {{", "\t\treturn 0, false", "\t}"]
            body += ["\treturn k, true", "}"]
        elif f.kind in ("string", "bytes"):
            body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                     "\tv, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
            if f.kind == "string":
                body += ["\tif !pbcodec.ValidUTF8(v) {", "\t\treturn 0, false", "\t}"]
                val = "string(v)"
            else:
                val = "pbcodec.CopyBytes(v)" if f.rep else "pbcodec.CopyBytesOrNil(v)"
            body += [f"\t{x} = append({x}, {val})" if f.rep else f"\t{x} = {val}", "\treturn k, true", "}"]
        else:
            one = [f"v, k, ok := {consume_fn(f)}(b)", "if !ok {", "\treturn 0, false", "}"]
            if f.rep:
                one += dec_elem_lines(f, "v", lambda e: [f"{x} = append({x}, {e})"])
            else:
                one += dec_elem_lines(f, "v", lambda e: [f"{x} = {e}"])
            one += ["return k, true"]
            body += [f"if num == {f.num} && typ == pbcodec.{w} {{"] + ["\t" + l for l in one] + ["}"]
            if f.rep:
                body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                         "\tp, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}",
                         "\tj := uint64(0)", "\tfor j < uint64(len(p)) {",
                         f"\t\tv, k2, ok2 := {consume_fn(f)}(p[j:])", "\t\tif !ok2 {", "\t\t\treturn 0, false", "\t\t}"]
                body += ["\t\t" + l for l in dec_elem_lines(f, "v", lambda e: [f"{x} = append({x}, {e})"])]
                body += ["\t\tj = j + k2", "\t}", "\treturn k, true", "}"]
    body += ["return pbcodec.SkipField(num, typ, b)"]
    out += ["\t" + l for l in body] + ["}", ""]
    return out


def used_imports(P, text, extra=()):
    """Import lines (sorted by path, as gofmt sorts them) for the aliases text uses, and extra
    (import paths)."""
    lines = [(p, f'\t"{p}"') for p in extra]
    for a, p in P.imports.items():
        if re.search(r"\b" + re.escape(a) + r"\.", text):
            lines.append((p, f'\t{a} "{p}"'))
    return [l for _, l in sorted(lines)]


def gen_codec_go(P, header, go_name):
    """pb_gen.go: the codec (all builds)."""
    body = [CODEC_DOC, "",
            "// pbMarshal is the codec's Marshal.",
            "func pbMarshal(m interface{}) ([]byte, error) {",
            "\tswitch p := m.(type) {"]
    for n in P.names:
        body += [f"\tcase *{n}:", "\t\tif p == nil {", "\t\t\treturn nil, nil", "\t\t}",
                 f"\t\tb, ok := pbenc_{ident(n)}(make([]byte, 0), p)", "\t\tif !ok {",
                 "\t\t\treturn nil, &pbcodec.Error{Msg: \"string field contains invalid UTF-8\"}", "\t\t}",
                 "\t\treturn b, nil"]
    body += ["\t}", "\tpanic(\"protobuf model: marshaling a value of a type not listed in [protobuf]\")", "}", "",
             "// pbUnmarshal is the codec's Unmarshal.",
             "func pbUnmarshal(b []byte, m interface{}) error {",
             "\tswitch p := m.(type) {"]
    for n in P.names:
        body += [f"\tcase *{n}:", "\t\tif p == nil {",
                 "\t\t\tpanic(\"protobuf model: Unmarshal into a nil message pointer\")", "\t\t}",
                 f"\t\t*p = {n}{{}}",
                 f"\t\tif !pbdec_{ident(n)}(b, p, pbcodec.DefaultRecursionLimit) {{",
                 "\t\t\treturn &pbcodec.Error{Msg: \"cannot parse invalid wire-format data\"}", "\t\t}",
                 "\t\treturn nil"]
    body += ["\t}", "\tpanic(\"protobuf model: unmarshaling into a value of a type not listed in [protobuf]\")",
             "}", ""]
    for n in P.names:
        body += gen_encoder(P, n)
        body += gen_decoder(P, n)
    text = "\n".join(body)
    imps = used_imports(P, text, ["netmodels.lab/pbcodec"])
    return header + f"package {go_name}\n\nimport (\n" + "\n".join(imps) + "\n)\n\n" + text


def gen_model_go(header, go_name):
    """pb_model_gen.go: registerProto for the protobuf model (build tags rpcmodel, goose)."""
    return (header + "//go:build rpcmodel || goose\n\n" + f"package {go_name}\n\n"
            "import \"google.golang.org/protobuf/proto\"\n\n"
            "// registerProto registers the codec with the protobuf model (the first registration\n"
            "// stays).\n"
            "func registerProto() {\n"
            "\tproto.SetCodec(&proto.Codec{Marshal: pbMarshal, Unmarshal: pbUnmarshal})\n"
            "}\n")


def gen_real_go(header, go_name):
    """pb_real_gen.go: registerProto for the real module (no codec)."""
    return (header + "//go:build !rpcmodel && !goose\n\n" + f"package {go_name}\n\n"
            "// registerProto: the real google.golang.org/protobuf needs no codec.\n"
            "func registerProto() {}\n")


def audit_lines(P):
    nf = sum(len(fs) for fs in P.m.values())
    return (f"{len(P.names)} message types, {nf} fields, {len(P.enums)} enums "
            f"({', '.join(P.names + P.enums)})")


def files(P, header, go_name, register=True):
    """The generated files: {file name: contents} (the registration files only with `register`)."""
    out = {"pb_gen.go": gen_codec_go(P, header, go_name)}
    if register:
        out["pb_model_gen.go"] = gen_model_go(header, go_name)
        out["pb_real_gen.go"] = gen_real_go(header, go_name)
    out["pb_gen_test.go"] = gen_test_go(P, header, go_name)
    return out


# ---------------------------------------------------------------------------------------------
# The test of the trusted claims against the real module (pb_gen_test.go)

TEST_HELPERS = r'''
// pbType: a listed message type, with its fields as [protobuf] lists them.
type pbType struct {
	name   string
	new    func() proto.Message
	fields []pbField
	// nest: the Go field names and numbers of a path of message fields from the type back to
	// itself (nil: not recursive)
	nest     []string
	nestNums []protowire.Number
}

type pbField struct {
	goName string
	num    protowire.Number
	kind   protoreflect.Kind
	rep    bool
	packed bool
	ref    string // a message or enum field's type's full name
	goType reflect.Type
}

func pbFullName(m proto.Message) string {
	return string(m.ProtoReflect().Descriptor().FullName())
}

func pbTypeOf[T any]() reflect.Type {
	return reflect.TypeOf((*T)(nil)).Elem()
}

func pbNil(m proto.Message) proto.Message {
	return reflect.Zero(reflect.TypeOf(m)).Interface().(proto.Message)
}

// pbTagNumber: the field number in a protobuf struct tag ("varint,4,opt,name=op,...").
func pbTagNumber(tag string) protowire.Number {
	parts := strings.Split(tag, ",")
	if len(parts) < 2 {
		return -1
	}
	n, err := strconv.Atoi(parts[1])
	if err != nil {
		return -1
	}
	return protowire.Number(n)
}

// TestProtoShapes: each listed message's fields are exactly the message's (its descriptor and
// its Go struct), and the message is in the codec's subset.
func TestProtoShapes(t *testing.T) {
	for _, tp := range pbTypes() {
		m := tp.new()
		md := m.ProtoReflect().Descriptor()
		if pbFullName(m) == "" {
			t.Errorf("%s: no descriptor", tp.name)
			continue
		}
		if md.ParentFile().Syntax() != protoreflect.Proto3 {
			t.Errorf("%s: syntax %v, not proto3 (outside the codec)", tp.name, md.ParentFile().Syntax())
		}
		if md.Oneofs().Len() != 0 || md.ExtensionRanges().Len() != 0 {
			t.Errorf("%s: has oneofs or extension ranges (outside the codec)", tp.name)
		}
		if md.Fields().Len() != len(tp.fields) {
			t.Errorf("%s: the message has %d fields, [protobuf] lists %d", tp.name, md.Fields().Len(), len(tp.fields))
		}
		st := reflect.TypeOf(m).Elem()
		exported := 0
		for i := 0; i < st.NumField(); i++ {
			if st.Field(i).IsExported() {
				exported++
			}
		}
		if exported != len(tp.fields) {
			t.Errorf("%s: the Go struct has %d exported fields, [protobuf] lists %d", tp.name, exported, len(tp.fields))
		}
		for _, f := range tp.fields {
			fd := md.Fields().ByNumber(f.num)
			if fd == nil {
				t.Errorf("%s.%s: the message has no field %d", tp.name, f.goName, f.num)
				continue
			}
			if fd.Kind() != f.kind || fd.IsList() != f.rep || fd.IsMap() || fd.IsPacked() != f.packed {
				t.Errorf("%s.%s (%d): kind %v, list %v, map %v, packed %v; [protobuf] says %v, %v, false, %v",
					tp.name, f.goName, f.num, fd.Kind(), fd.IsList(), fd.IsMap(), fd.IsPacked(), f.kind, f.rep, f.packed)
			}
			if fd.ContainingOneof() != nil || fd.HasPresence() != (!f.rep && f.kind == protoreflect.MessageKind) {
				t.Errorf("%s.%s: explicit presence or a oneof (outside the codec)", tp.name, f.goName)
			}
			ref := ""
			if fd.Message() != nil {
				ref = string(fd.Message().FullName())
			} else if fd.Enum() != nil {
				ref = string(fd.Enum().FullName())
			}
			if ref != f.ref {
				t.Errorf("%s.%s: type %q, [protobuf] says %q", tp.name, f.goName, ref, f.ref)
			}
			sf, ok := st.FieldByName(f.goName)
			if !ok || sf.Type != f.goType || pbTagNumber(sf.Tag.Get("protobuf")) != f.num {
				t.Errorf("%s.%s: Go field %v (tag %q), [protobuf] says %v number %d", tp.name, f.goName,
					sf.Type, sf.Tag.Get("protobuf"), f.goType, f.num)
			}
		}
	}
}

// pbRndInt: an integer, often an edge value.
func pbRndInt(r *rand.Rand) int64 {
	switch r.Intn(10) {
	case 0:
		return 0
	case 1:
		return -1
	case 2:
		return 1
	case 3:
		return math.MinInt64
	case 4:
		return math.MaxInt64
	case 5:
		return int64(r.Intn(300)) - 150
	case 6:
		return []int64{math.MinInt32, math.MaxInt32, math.MaxUint32, 1 << 31, 1 << 32, 127, 128}[r.Intn(7)]
	}
	return int64(r.Uint64() >> uint(r.Intn(64)))
}

var pbPieces = []string{"a", "xyz", " ", "0", "é", "日本", "\U0001F600", "\x00", "\x7f", "￿"}
var pbBadPieces = []string{"\xff", "\xed\xa0\x80", "\xc0\x80", "\xe2\x82", "\xf4\x90\x80\x80", "\x80"}

// pbRndString: a string of valid UTF-8 pieces, rarely with an invalid one.
func pbRndString(r *rand.Rand) string {
	var sb strings.Builder
	for k := r.Intn(5); k > 0; k-- {
		if r.Intn(60) == 0 {
			sb.WriteString(pbBadPieces[r.Intn(len(pbBadPieces))])
		} else {
			sb.WriteString(pbPieces[r.Intn(len(pbPieces))])
		}
	}
	return sb.String()
}

// pbRandFill sets random values in the exported fields of a message struct v (some left zero).
func pbRandFill(r *rand.Rand, v reflect.Value, depth int) {
	for i := 0; i < v.NumField(); i++ {
		if !v.Type().Field(i).IsExported() || r.Intn(3) == 0 {
			continue
		}
		pbRandValue(r, v.Field(i), depth)
	}
}

func pbRandValue(r *rand.Rand, f reflect.Value, depth int) {
	switch f.Kind() {
	case reflect.Int32, reflect.Int64:
		f.SetInt(pbRndInt(r))
	case reflect.Uint32, reflect.Uint64:
		f.SetUint(uint64(pbRndInt(r)))
	case reflect.Bool:
		f.SetBool(r.Intn(2) == 0)
	case reflect.String:
		f.SetString(pbRndString(r))
	case reflect.Pointer:
		if depth >= 5 {
			return
		}
		p := reflect.New(f.Type().Elem())
		if r.Intn(4) != 0 {
			pbRandFill(r, p.Elem(), depth+1)
		}
		f.Set(p)
	case reflect.Slice:
		if f.Type().Elem().Kind() == reflect.Uint8 {
			switch r.Intn(4) {
			case 0:
				return
			case 1:
				f.SetBytes([]byte{})
			default:
				b := make([]byte, r.Intn(20))
				r.Read(b)
				f.SetBytes(b)
			}
			return
		}
		switch r.Intn(6) {
		case 0:
			return
		case 1:
			f.Set(reflect.MakeSlice(f.Type(), 0, r.Intn(2)))
			return
		}
		n := 1 + r.Intn(4)
		s := reflect.MakeSlice(f.Type(), n, n)
		for i := 0; i < n; i++ {
			if s.Index(i).Kind() == reflect.Pointer && r.Intn(8) == 0 {
				continue // a nil element
			}
			pbRandValue(r, s.Index(i), depth+1)
		}
		f.Set(s)
	default:
		panic("pbRandValue: kind " + f.Kind().String())
	}
}

// pbChain: a message of type tp nested d deep along tp.nest.
func pbChain(tp pbType, d int) proto.Message {
	m := tp.new()
	cur := reflect.ValueOf(m).Elem()
	for i := 0; i < d; i++ {
		f := cur.FieldByName(tp.nest[i%len(tp.nest)])
		var child reflect.Value
		if f.Kind() == reflect.Pointer {
			child = reflect.New(f.Type().Elem())
			f.Set(child)
		} else {
			child = reflect.New(f.Type().Elem().Elem())
			f.Set(reflect.Append(f, child))
		}
		cur = child.Elem()
	}
	return m
}

// pbEq: a and b are equal in their exported fields, strictly (nil and empty slices differ).
func pbEq(a, b reflect.Value) bool {
	switch a.Kind() {
	case reflect.Pointer:
		if a.IsNil() || b.IsNil() {
			return a.IsNil() == b.IsNil()
		}
		return pbEq(a.Elem(), b.Elem())
	case reflect.Struct:
		for i := 0; i < a.NumField(); i++ {
			if a.Type().Field(i).IsExported() && !pbEq(a.Field(i), b.Field(i)) {
				return false
			}
		}
		return true
	case reflect.Slice:
		if a.IsNil() != b.IsNil() || a.Len() != b.Len() {
			return false
		}
		for i := 0; i < a.Len(); i++ {
			if !pbEq(a.Index(i), b.Index(i)) {
				return false
			}
		}
		return true
	}
	return a.Interface() == b.Interface()
}

var pbStats struct {
	marshalErrs, marshalOK int
}

// pbCheckMarshal: the codec's Marshal is real proto.Marshal: bytes, nil-or-not, error-or-not.
func pbCheckMarshal(t *testing.T, m proto.Message) {
	t.Helper()
	want, werr := proto.Marshal(m)
	got, gerr := pbMarshal(m)
	if (werr != nil) != (gerr != nil) || (werr == nil && (!bytes.Equal(got, want) || (got == nil) != (want == nil))) {
		t.Fatalf("Marshal(%v):\n real  %x (nil %v) %v\n codec %x (nil %v) %v", m, want, want == nil, werr, got, got == nil, gerr)
	}
	if werr != nil {
		pbStats.marshalErrs++
	} else {
		pbStats.marshalOK++
	}
}

// TestProtoMarshal: random values of every listed type (edge integers, nil and empty slices,
// nil elements, nested nils, non-ASCII and invalid UTF-8), nil and empty messages, and deep
// nesting.
func TestProtoMarshal(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for _, tp := range pbTypes() {
		pbCheckMarshal(t, pbNil(tp.new()))
		pbCheckMarshal(t, tp.new())
		for it := 0; it < 3000; it++ {
			m := tp.new()
			pbRandFill(r, reflect.ValueOf(m).Elem(), 0)
			pbCheckMarshal(t, m)
		}
		if tp.nest != nil {
			for _, d := range []int{1, 2, 100, 10001, 10003} {
				pbCheckMarshal(t, pbChain(tp, d))
			}
		}
	}
	if pbHasStrings && pbStats.marshalErrs == 0 {
		t.Fatalf("no Marshal error (invalid UTF-8) seen")
	}
	t.Logf("%d encodings, %d errors", pbStats.marshalOK, pbStats.marshalErrs)
}

// pbSamples: real encodings of random values of every listed type.
func pbSamples(r *rand.Rand, n int) [][]byte {
	types := pbTypes()
	var out [][]byte
	for len(out) < n {
		tp := types[r.Intn(len(types))]
		m := tp.new()
		pbRandFill(r, reflect.ValueOf(m).Elem(), 0)
		b, err := proto.Marshal(m)
		if err == nil {
			out = append(out, b)
		}
	}
	return out
}

// pbCheckUnmarshal decodes data into a fresh and a pre-filled message of type tp, by real
// proto.Unmarshal and by the codec: error-or-not, and on success equal values (pbEq: exported
// fields, nil-or-not; proto.Equal to the real one's without unknown fields). It returns
// whether the real one succeeded.
func pbCheckUnmarshal(t *testing.T, r *rand.Rand, tp pbType, data []byte) bool {
	t.Helper()
	var werr error
	for _, fill := range []bool{false, true} {
		a, b := tp.new(), tp.new()
		if fill {
			s := r.Int63()
			pbRandFill(rand.New(rand.NewSource(s)), reflect.ValueOf(a).Elem(), 0)
			pbRandFill(rand.New(rand.NewSource(s)), reflect.ValueOf(b).Elem(), 0)
		}
		werr = proto.Unmarshal(data, a)
		gerr := pbUnmarshal(data, b)
		if (werr != nil) != (gerr != nil) {
			t.Fatalf("Unmarshal(%x) into %s (pre-filled %v): real %v, codec %v", data, tp.name, fill, werr, gerr)
		}
		if werr != nil {
			continue
		}
		if !pbEq(reflect.ValueOf(a), reflect.ValueOf(b)) {
			t.Fatalf("Unmarshal(%x) into %s (pre-filled %v):\n real  %v\n codec %v", data, tp.name, fill, a, b)
		}
		d := tp.new() // the real one's value, without unknown fields
		if err := (proto.UnmarshalOptions{DiscardUnknown: true}).Unmarshal(data, d); err != nil || !proto.Equal(d, b) {
			t.Fatalf("Unmarshal(%x) into %s: not proto.Equal:\n real  %v\n codec %v", data, tp.name, a, b)
		}
	}
	return werr == nil
}

// pbCheckUnmarshalFresh is pbCheckUnmarshal for a fresh target only (for large inputs).
func pbCheckUnmarshalFresh(t *testing.T, tp pbType, data []byte) bool {
	t.Helper()
	a, b := tp.new(), tp.new()
	werr := proto.Unmarshal(data, a)
	gerr := pbUnmarshal(data, b)
	if (werr != nil) != (gerr != nil) {
		t.Fatalf("Unmarshal(len %d) into %s: real %v, codec %v", len(data), tp.name, werr, gerr)
	}
	if werr == nil && !pbEq(reflect.ValueOf(a), reflect.ValueOf(b)) { // (a may have unknown fields)
		t.Fatalf("Unmarshal(len %d) into %s: values differ", len(data), tp.name)
	}
	return werr == nil
}

// TestProtoUnmarshal: real encodings of every listed type, decoded into every listed type.
func TestProtoUnmarshal(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	types := pbTypes()
	samples := pbSamples(r, 500)
	for _, s := range samples {
		for _, tp := range types {
			pbCheckUnmarshal(t, r, tp, s)
		}
	}
}

// pbRaw: a field of an encoding, as protowire splits it.
type pbRaw struct {
	tag []byte
	num protowire.Number
	typ protowire.Type
	val []byte
}

// pbSplit splits b into its fields, and the rest that does not parse.
func pbSplit(b []byte) ([]pbRaw, []byte) {
	var fs []pbRaw
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			break
		}
		m := protowire.ConsumeFieldValue(num, typ, b[n:])
		if m < 0 {
			break
		}
		fs = append(fs, pbRaw{b[:n], num, typ, b[n : n+m]})
		b = b[n+m:]
	}
	return fs, b
}

func pbJoin(fs []pbRaw, rest []byte) []byte {
	var out []byte
	for _, f := range fs {
		out = append(out, f.tag...)
		out = append(out, f.val...)
	}
	return append(out, rest...)
}

// pbOverlong: v as a varint of exactly n bytes (n >= its size; n > 10 is malformed).
func pbOverlong(v uint64, n int) []byte {
	b := protowire.AppendVarint(nil, v)
	for len(b) < n {
		b[len(b)-1] |= 0x80
		b = append(b, 0)
	}
	return b
}

// pbRndVarint: a varint value, often an edge one.
func pbRndVarint(r *rand.Rand) uint64 {
	return uint64(pbRndInt(r))
}

// pbRndField: a random field of number num and wire type typ (any of 0..7; 6 and 7 are
// reserved), with a value of that type (a group: random fields inside, nested, ended by its
// own number, or rarely another).
func pbRndField(r *rand.Rand, num protowire.Number, typ protowire.Type, samples [][]byte, depth int) []byte {
	b := protowire.AppendTag(nil, num, typ)
	switch typ {
	case protowire.VarintType:
		return protowire.AppendVarint(b, pbRndVarint(r))
	case protowire.Fixed32Type:
		return protowire.AppendFixed32(b, r.Uint32())
	case protowire.Fixed64Type:
		return protowire.AppendFixed64(b, r.Uint64())
	case protowire.BytesType:
		switch r.Intn(4) {
		case 0:
			return protowire.AppendBytes(b, samples[r.Intn(len(samples))])
		case 1:
			return protowire.AppendString(b, pbRndString(r))
		case 2:
			var p []byte
			for k := r.Intn(4); k > 0; k-- {
				p = protowire.AppendVarint(p, pbRndVarint(r))
			}
			return protowire.AppendBytes(b, p)
		}
		p := make([]byte, r.Intn(9))
		r.Read(p)
		return protowire.AppendBytes(b, p)
	case protowire.StartGroupType:
		for k := r.Intn(4); k > 0; k-- {
			t2 := protowire.Type(r.Intn(6))
			if t2 == protowire.EndGroupType || (t2 == protowire.StartGroupType && depth > 2) {
				t2 = protowire.VarintType
			}
			n2 := protowire.Number(1 + r.Intn(20))
			if r.Intn(10) == 0 {
				n2 = protowire.Number(1<<31 - 1) // above MaxValidNumber: protowire skips it in a group
			}
			b = append(b, pbRndField(r, n2, t2, samples, depth+1)...)
		}
		end := num
		if r.Intn(10) == 0 {
			end = num + 1
		}
		return protowire.AppendTag(b, end, protowire.EndGroupType)
	}
	return b
}

func pbRndNum(r *rand.Rand) protowire.Number {
	if r.Intn(3) == 0 {
		return protowire.Number(1 + r.Intn(20))
	}
	return pbNums[r.Intn(len(pbNums))]
}

// pbMutate: a mutation of an encoding.
func pbMutate(r *rand.Rand, b []byte, samples [][]byte, depth int) []byte {
	fs, rest := pbSplit(b)
	insert := func(i int, f []byte) []byte {
		pos := 0
		if len(fs) > 0 {
			pos = len(pbJoin(fs[:i], nil))
		}
		return append(append(append([]byte{}, b[:pos]...), f...), b[pos:]...)
	}
	k := r.Intn(17)
	if len(fs) == 0 && k >= 3 && k <= 11 {
		k = 2
	}
	var i int
	if len(fs) > 0 {
		i = r.Intn(len(fs))
	}
	switch k {
	case 0: // cut short
		return b[:r.Intn(len(b)+1)]
	case 1: // a byte changed
		if len(b) == 0 {
			return []byte{byte(r.Intn(256))}
		}
		c := append([]byte{}, b...)
		c[r.Intn(len(c))] = []byte{0, 0x7f, 0x80, 0xff, 0x08, 0x0b, 0x0c, 0x0e, 0x0f, byte(r.Intn(256))}[r.Intn(10)]
		return c
	case 2: // an unknown or known field of any wire type inserted
		return insert(r.Intn(len(fs)+1), pbRndField(r, pbRndNum(r), protowire.Type(r.Intn(8)), samples, 0))
	case 3: // a field repeated
		return insert(r.Intn(len(fs)+1), pbJoin(fs[i:i+1], nil))
	case 4: // two fields swapped
		j := r.Intn(len(fs))
		fs[i], fs[j] = fs[j], fs[i]
		return pbJoin(fs, rest)
	case 5: // a length-delimited field read as packed varints, written unpacked
		if fs[i].typ != protowire.BytesType {
			return b
		}
		p, _ := protowire.ConsumeBytes(fs[i].val)
		var out []byte
		for len(p) > 0 {
			v, n := protowire.ConsumeVarint(p)
			if n < 0 {
				return b
			}
			out = protowire.AppendVarint(protowire.AppendTag(out, fs[i].num, protowire.VarintType), v)
			p = p[n:]
		}
		fs[i] = pbRaw{nil, fs[i].num, protowire.VarintType, out}
		return pbJoin(fs, rest)
	case 6: // a varint field (and the next ones of its number) written packed
		if fs[i].typ != protowire.VarintType {
			return b
		}
		var p []byte
		j := i
		for j < len(fs) && fs[j].num == fs[i].num && fs[j].typ == protowire.VarintType {
			p = append(p, fs[j].val...)
			j++
		}
		nf := pbRaw{protowire.AppendTag(nil, fs[i].num, protowire.BytesType), fs[i].num, protowire.BytesType, protowire.AppendBytes(nil, p)}
		return pbJoin(append(append(append([]pbRaw{}, fs[:i]...), nf), fs[j:]...), rest)
	case 7: // an overlong tag or varint value (up to 11 bytes: malformed)
		n := 1 + r.Intn(11)
		if r.Intn(2) == 0 || fs[i].typ != protowire.VarintType {
			v, _ := protowire.ConsumeVarint(fs[i].tag)
			if m := protowire.SizeVarint(v); n < m {
				n = m
			}
			fs[i].tag = pbOverlong(v, n)
		} else {
			v, _ := protowire.ConsumeVarint(fs[i].val)
			if m := protowire.SizeVarint(v); n < m {
				n = m
			}
			fs[i].val = pbOverlong(v, n)
		}
		return pbJoin(fs, rest)
	case 8: // a field number 0, at or past the largest, or past protowire's
		nums := []uint64{0, 1<<29 - 1, 1 << 29, 1<<31 - 1, 1 << 31, 1 << 32, 1 << 60}
		fs[i].tag = protowire.AppendVarint(nil, nums[r.Intn(len(nums))]<<3|uint64(fs[i].typ))
		return pbJoin(fs, rest)
	case 9: // another wire type (the value kept, or a value of the new type)
		typ := protowire.Type(r.Intn(8))
		if r.Intn(2) == 0 {
			fs[i].tag = protowire.AppendTag(nil, fs[i].num, typ)
			return pbJoin(fs, rest)
		}
		f := pbRndField(r, fs[i].num, typ, samples, 0)
		fs[i] = pbRaw{nil, fs[i].num, typ, f}
		return pbJoin(fs, rest)
	case 10: // a nested encoding mutated
		if fs[i].typ != protowire.BytesType || depth > 3 {
			return b
		}
		p, _ := protowire.ConsumeBytes(fs[i].val)
		fs[i].val = protowire.AppendBytes(nil, pbMutate(r, append([]byte{}, p...), samples, depth+1))
		return pbJoin(fs, rest)
	case 11: // invalid UTF-8 in a length-delimited field
		if fs[i].typ != protowire.BytesType {
			return b
		}
		p, _ := protowire.ConsumeBytes(fs[i].val)
		q := append([]byte{}, p...)
		bad := pbBadPieces[r.Intn(len(pbBadPieces))]
		at := r.Intn(len(q) + 1)
		q = append(q[:at], append([]byte(bad), q[at:]...)...)
		fs[i].val = protowire.AppendBytes(nil, q)
		return pbJoin(fs, rest)
	case 12: // a stray end-group, start-group or reserved tag
		typ := []protowire.Type{protowire.EndGroupType, protowire.StartGroupType, 6, 7}[r.Intn(4)]
		return insert(r.Intn(len(fs)+1), protowire.AppendTag(nil, pbRndNum(r), typ))
	case 13: // random bytes appended
		c := make([]byte, 1+r.Intn(4))
		r.Read(c)
		return append(append([]byte{}, b...), c...)
	case 14: // another encoding appended (merged)
		return append(append([]byte{}, b...), samples[r.Intn(len(samples))]...)
	case 15: // a field dropped
		if len(fs) == 0 {
			return b
		}
		return pbJoin(append(append([]pbRaw{}, fs[:i]...), fs[i+1:]...), rest)
	}
	// a length-delimited field replaced by another encoding (another message type)
	if len(fs) == 0 || fs[i].typ != protowire.BytesType {
		return b
	}
	fs[i].val = protowire.AppendBytes(nil, samples[r.Intn(len(samples))])
	return pbJoin(fs, rest)
}

// TestProtoMutations: mutated encodings decoded into every listed type.
func TestProtoMutations(t *testing.T) {
	r := rand.New(rand.NewSource(3))
	types := pbTypes()
	samples := pbSamples(r, 300)
	nOK, nErr := 0, 0
	for it := 0; it < 40000; it++ {
		data := samples[r.Intn(len(samples))]
		for m := 1 + r.Intn(3); m > 0; m-- {
			data = pbMutate(r, data, samples, 0)
		}
		if pbCheckUnmarshal(t, r, types[r.Intn(len(types))], data) {
			nOK++
		} else {
			nErr++
		}
	}
	t.Logf("%d decoded, %d errors", nOK, nErr)
	if nOK < 4000 || nErr < 4000 {
		t.Fatalf("too few of one outcome: %d decoded, %d errors", nOK, nErr)
	}
}

// pbPayloads: values of each wire type (after a tag), edge ones and malformed ones.
func pbPayloads(samples [][]byte) map[protowire.Type][][]byte {
	v := func(x uint64) []byte { return protowire.AppendVarint(nil, x) }
	out := map[protowire.Type][][]byte{}
	for _, x := range []uint64{0, 1, 2, 127, 128, 300, 1<<31 - 1, 1 << 31, 1<<32 - 1, 1 << 32, 1<<32 + 5,
		1<<63 - 1, 1 << 63, 1<<64 - 1} {
		out[protowire.VarintType] = append(out[protowire.VarintType], v(x))
	}
	out[protowire.VarintType] = append(out[protowire.VarintType], pbOverlong(0, 10), pbOverlong(1, 10),
		pbOverlong(1, 11), []byte{0x80}, []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02}, nil)
	for _, x := range []uint32{0, 1, 1<<31 - 1, 1 << 31, 1<<32 - 1} {
		out[protowire.Fixed32Type] = append(out[protowire.Fixed32Type], protowire.AppendFixed32(nil, x))
	}
	out[protowire.Fixed32Type] = append(out[protowire.Fixed32Type], []byte{1, 2, 3})
	for _, x := range []uint64{0, 1, 1<<63 - 1, 1 << 63, 1<<64 - 1} {
		out[protowire.Fixed64Type] = append(out[protowire.Fixed64Type], protowire.AppendFixed64(nil, x))
	}
	out[protowire.Fixed64Type] = append(out[protowire.Fixed64Type], []byte{1, 2, 3, 4, 5, 6, 7})
	packed := append(append(v(1), v(300)...), v(1<<63)...)
	for _, b := range [][]byte{{}, []byte("a"), []byte("\xff"), []byte("\u00e9"), []byte("\xed\xa0\x80"),
		packed, {0x80}, {1, 2, 3, 4}, {1, 2, 3, 4, 5}, {1, 2, 3, 4, 5, 6, 7, 8}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		protowire.AppendBytes(protowire.AppendTag(nil, 1, protowire.BytesType), nil)} {
		out[protowire.BytesType] = append(out[protowire.BytesType], protowire.AppendBytes(nil, b))
	}
	for _, s := range samples[:8] {
		out[protowire.BytesType] = append(out[protowire.BytesType], protowire.AppendBytes(nil, s))
	}
	out[protowire.BytesType] = append(out[protowire.BytesType], []byte{5, 1}, []byte{0x80})
	return out
}

// TestProtoFields: every listed field number (and an unknown one) of every listed type, with
// values of every wire type (edge and malformed ones), once and twice (merging), into fresh and
// pre-filled targets.
func TestProtoFields(t *testing.T) {
	r := rand.New(rand.NewSource(5))
	pl := pbPayloads(pbSamples(r, 8))
	for _, tp := range pbTypes() {
		nums := []protowire.Number{pbUnknownNum}
		for _, f := range tp.fields {
			nums = append(nums, f.num)
		}
		for _, num := range nums {
			var fields [][]byte
			for typ := protowire.Type(0); typ < 8; typ++ {
				tag := protowire.AppendTag(nil, num, typ)
				switch typ {
				case protowire.StartGroupType:
					end := protowire.AppendTag(nil, num, protowire.EndGroupType)
					inner := protowire.AppendVarint(protowire.AppendTag(nil, 1, protowire.VarintType), 1)
					fields = append(fields, append(append([]byte{}, tag...), end...),
						append(append(append([]byte{}, tag...), inner...), end...), tag,
						append(append([]byte{}, tag...), protowire.AppendTag(nil, num+1, protowire.EndGroupType)...))
				case protowire.EndGroupType, 6, 7:
					fields = append(fields, tag)
				default:
					for _, p := range pl[typ] {
						fields = append(fields, append(append([]byte{}, tag...), p...))
					}
				}
			}
			for _, a := range fields {
				pbCheckUnmarshal(t, r, tp, a)
			}
			for k := 0; k < 80; k++ {
				a, b := fields[r.Intn(len(fields))], fields[r.Intn(len(fields))]
				pbCheckUnmarshal(t, r, tp, append(append([]byte{}, a...), b...))
			}
		}
		// a message field twice or three times, with encodings of its own type (merged)
		for _, f := range tp.fields {
			if f.kind != protoreflect.MessageKind {
				continue
			}
			var ft pbType
			for _, u := range pbTypes() {
				if pbFullName(u.new()) == f.ref {
					ft = u
				}
			}
			for k := 0; k < 40; k++ {
				var data []byte
				for j := 2 + r.Intn(2); j > 0; j-- {
					m := ft.new()
					pbRandFill(r, reflect.ValueOf(m).Elem(), 0)
					e, err := proto.Marshal(m)
					if err != nil {
						continue
					}
					data = protowire.AppendBytes(protowire.AppendTag(data, f.num, protowire.BytesType), e)
				}
				pbCheckUnmarshal(t, r, tp, data)
			}
		}
	}
}

// pbGroup: an unknown group field num with d groups nested (d >= 1), each with a field.
func pbGroup(num protowire.Number, d int) []byte {
	var b []byte
	for i := 0; i < d; i++ {
		b = protowire.AppendTag(b, num, protowire.StartGroupType)
	}
	b = protowire.AppendVarint(protowire.AppendTag(b, num, protowire.VarintType), 5)
	for i := 0; i < d; i++ {
		b = protowire.AppendTag(b, num, protowire.EndGroupType)
	}
	return b
}

// pbNest: messages nested k deep along the field numbers nums (cyclically), with inner in the
// innermost.
func pbNest(nums []protowire.Number, k int, inner []byte) []byte {
	b := inner
	for i := k - 1; i >= 0; i-- {
		c := protowire.AppendTag(make([]byte, 0, len(b)+16), nums[i%len(nums)], protowire.BytesType)
		b = protowire.AppendBytes(c, b)
	}
	return b
}

// TestProtoDepth: messages nested at and past the recursion limit (10000 messages, the
// outermost included), and unknown groups nested at and past protowire's (inside the outermost
// message, and inside a deeply nested one).
func TestProtoDepth(t *testing.T) {
	r := rand.New(rand.NewSource(4))
	for _, tp := range pbTypes() {
		for _, d := range []int{1, 2, 10001, 10002} {
			ok := pbCheckUnmarshal(t, r, tp, pbGroup(pbUnknownNum, d))
			if ok != (d <= 10001) {
				t.Fatalf("%s: a group nested %d deep: real %v", tp.name, d, ok)
			}
		}
		if tp.nest == nil {
			continue
		}
		for _, k := range []int{1, 2, 9999, 10000, 10001} {
			ok := pbCheckUnmarshalFresh(t, tp, pbNest(tp.nestNums, k, nil))
			if ok != (k < 10000) {
				t.Fatalf("%s: nested %d deep: real %v", tp.name, k, ok)
			}
		}
		// groups at protowire's limit inside messages at the recursion limit
		if !pbCheckUnmarshalFresh(t, tp, pbNest(tp.nestNums, 9999, pbGroup(pbUnknownNum, 10001))) ||
			pbCheckUnmarshalFresh(t, tp, pbNest(tp.nestNums, 9999, pbGroup(pbUnknownNum, 10002))) {
			t.Fatalf("%s: groups inside deep nesting: the real one's limits are not as expected", tp.name)
		}
	}
}

func pbPanics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}

// TestProtoPanics: Unmarshal into a nil *T panics, as the real one does; the codec panics on a
// value outside the listed types.
func TestProtoPanics(t *testing.T) {
	for _, tp := range pbTypes() {
		for _, data := range [][]byte{nil, {8, 1}} {
			nilm := pbNil(tp.new())
			wp := pbPanics(func() { proto.Unmarshal(data, nilm) })
			gp := pbPanics(func() { pbUnmarshal(data, nilm) })
			if !wp || !gp {
				t.Fatalf("%s: Unmarshal into nil: real panics %v, codec %v (both should)", tp.name, wp, gp)
			}
		}
	}
	for _, v := range []interface{}{nil, "x", 1, struct{}{}, &struct{}{}} {
		if !pbPanics(func() { pbMarshal(v) }) || !pbPanics(func() { pbUnmarshal(nil, v) }) {
			t.Fatalf("the codec does not panic on %#v", v)
		}
	}
}
'''


def gen_test_go(P, header, go_name):
    """pb_gen_test.go: the tests against the real module (real builds only)."""
    lines = [header + "//go:build !rpcmodel && !goose\n", f"package {go_name}", "",
             "import (", '\t"bytes"', '\t"math"', '\t"math/rand"', '\t"reflect"', '\t"strconv"',
             '\t"strings"', '\t"testing"', ""]
    pbpkgs = ["google.golang.org/protobuf/encoding/protowire", "google.golang.org/protobuf/proto",
              "google.golang.org/protobuf/reflect/protoreflect"]
    table = ["// pbTypes: the listed message types ([protobuf]).", "func pbTypes() []pbType {",
             "\treturn []pbType{"]
    for n in P.names:
        table.append(f"\t\t{{name: {go_str(n)}, new: func() proto.Message {{ return &{n}{{}} }},")
        cyc = P.cycle(n)
        if cyc:
            table.append("\t\t\tnest:     []string{" + ", ".join(go_str(a) for a, _ in cyc) + "},")
            table.append("\t\t\tnestNums: []protowire.Number{" + ", ".join(str(b) for _, b in cyc) + "},")
        if not P.m[n]:
            table += ["\t\t\tfields: []pbField{},", "\t\t},"]
            continue
        table.append("\t\t\tfields: []pbField{")
        for f in P.m[n]:
            if f.cat == "message":
                ref = f"pbFullName(&{f.kind}{{}})"
            elif f.cat == "enum":
                ref = f"string({f.kind}(0).Descriptor().FullName())"
            else:
                ref = '""'
            table.append(f"\t\t\t\t{{{go_str(f.name)}, {f.num}, protoreflect.{f.pr_kind()}, "
                         f"{str(f.rep).lower()}, {str(f.packed).lower()}, {ref}, pbTypeOf[{f.go_type()}]()}},")
        table += ["\t\t\t},", "\t\t},"]
    table += ["\t}", "}", ""]
    nums = sorted({f.num for fs in P.m.values() for f in fs} | {P.unknown_num()})
    has_strings = any(f.kind == "string" for fs in P.m.values() for f in fs)
    consts = [f"// pbUnknownNum: a field number no listed message has.",
              f"const pbUnknownNum protowire.Number = {P.unknown_num()}", "",
              "// pbNums: the listed field numbers (and pbUnknownNum), for mutations.",
              "var pbNums = []protowire.Number{" + ", ".join(map(str, nums)) + "}", "",
              "// pbHasStrings: some listed message has a string field.",
              f"const pbHasStrings = {str(has_strings).lower()}", ""]
    text = "\n".join(table)
    lines += used_imports(P, text, pbpkgs) + [")", ""]
    return "\n".join(lines + consts + table) + TEST_HELPERS


# ---------------------------------------------------------------------------------------------
# --from-pb: a [protobuf] section from protoc-gen-go's generated structs


def from_pb(paths, aliases):
    """A [protobuf] section (toml text) for the messages of the given .pb.go files."""
    msgs = []
    enums = []
    pkgs = {}
    problems = []
    for path in paths:
        src = open(path).read()
        pm = re.search(r"^package (\w+)", src, re.M)
        if not pm:
            raise PbError(f"{path}: no package clause")
        pkg = pm.group(1)
        pkgs[pkg] = aliases.get(pkg, "TODO: the Go import path of " + os.path.dirname(os.path.abspath(path)))
        for m in re.finditer(r"^type (\w+) struct \{\n(.*?)^\}", src, re.M | re.S):
            name, body = m.group(1), m.group(2)
            fields = []
            for line in body.split("\n"):
                fm = re.match(r"\s*(\w+)\s+(\S+)\s+`(.*)`", line)
                if not fm:
                    continue
                gname, gtype, tags = fm.groups()
                if "protobuf_oneof" in tags:
                    problems.append(f"{pkg}.{name}.{gname}: a oneof (outside the subset)")
                    continue
                if "protobuf_key" in tags:
                    problems.append(f"{pkg}.{name}.{gname}: a map (outside the subset)")
                    continue
                tm = re.search(r'protobuf:"([^"]*)"', tags)
                if not tm:
                    continue
                parts = tm.group(1).split(",")
                enc, num, card = parts[0], int(parts[1]), parts[2]
                opts = parts[3:]
                where = f"{pkg}.{name}.{gname}"
                if "proto3" not in opts:
                    problems.append(f"{where}: not proto3 (outside the subset)")
                if "oneof" in opts or (gtype.startswith("*") and enc != "bytes"):
                    problems.append(f"{where}: explicit presence (optional; outside the subset)")
                    continue
                rep = card == "rep"
                t = gtype[2:] if rep else gtype
                if rep and enc not in ("bytes",) and "packed" not in opts:
                    problems.append(f"{where}: an unpacked repeated scalar (outside the subset)")
                kind = None
                if enc == "group":
                    problems.append(f"{where}: a group (outside the subset)")
                    continue
                if enc in ("fixed32", "fixed64") and t in ("float32", "float64"):
                    problems.append(f"{where}: float/double (outside the subset)")
                    continue
                if any(o.startswith("enum=") for o in opts):
                    en = f"{pkg}.{t}" if "." not in t else t
                    kind = en
                    if en not in enums:
                        enums.append(en)
                elif t.startswith("*"):
                    kind = f"{pkg}.{t[1:]}" if "." not in t else t[1:]
                elif enc == "varint":
                    kind = {"int32": "int32", "int64": "int64", "uint32": "uint32", "uint64": "uint64",
                            "bool": "bool"}.get(t)
                elif enc == "zigzag32":
                    kind = "sint32"
                elif enc == "zigzag64":
                    kind = "sint64"
                elif enc == "fixed32":
                    kind = {"uint32": "fixed32", "int32": "sfixed32"}.get(t)
                elif enc == "fixed64":
                    kind = {"uint64": "fixed64", "int64": "sfixed64"}.get(t)
                elif enc == "bytes":
                    kind = {"string": "string", "[]byte": "bytes"}.get(t)
                if kind is None:
                    problems.append(f"{where}: {enc} {gtype}: not in the subset")
                    continue
                fields.append(f'["{gname}", {num}, "{"[]" if rep else ""}{kind}"]')
            if fields or "protoimpl.MessageState" in body:
                msgs.append((f"{pkg}.{name}", fields))
    out = ["# [protobuf] derived by pbgen.py --from-pb " + " ".join(os.path.basename(p) for p in paths),
           "# (a starting point: review it; the toml is the audited source)"]
    for p in problems:
        out.append(f"# REFUSED: {p}")
    out.append("[protobuf]")
    out.append("imports = { " + ", ".join(f'{a} = "{p}"' for a, p in sorted(pkgs.items())) + " }")
    if enums:
        out.append("enums = [" + ", ".join(f'"{e}"' for e in enums) + "]")
    out.append("[protobuf.messages]")
    for n, fs in msgs:
        if not fs:
            out.append(f'"{n}" = []')
        else:
            out.append(f'"{n}" = [' + (",\n    ".join(fs)) + "]")
    return "\n".join(out) + "\n"


def write_files(fs, outdir, check):
    """Write {file name: contents} into outdir (with `check`, compare only); False if a file
    differed under `check`."""
    ok = True
    for f, c in fs.items():
        p = os.path.join(outdir, f)
        cur = open(p).read() if os.path.exists(p) else None
        if cur == c:
            continue
        if check:
            print(f"not current: {p}", file=sys.stderr)
            ok = False
        else:
            os.makedirs(outdir, exist_ok=True)
            with open(p, "w") as fh:
                fh.write(c)
            print(f"wrote {p}")
    return ok


def main():
    ap = argparse.ArgumentParser(description="A protobuf codec for a [protobuf] table.")
    ap.add_argument("toml", nargs="?", help="a toml file holding a [protobuf] table")
    ap.add_argument("outdir", nargs="?", help="the Go package directory to write the files into")
    ap.add_argument("--pkg", help="the Go package name")
    ap.add_argument("--register", action="store_true",
                    help="also write registerProto (pb_model_gen.go, pb_real_gen.go)")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if a file differs")
    ap.add_argument("--from-pb", nargs="+", metavar="FILE.pb.go",
                    help="print a [protobuf] section derived from generated .pb.go files")
    ap.add_argument("--import", dest="imports", action="append", default=[], metavar="ALIAS=PATH",
                    help="with --from-pb: a package's import path")
    a = ap.parse_args()
    try:
        if a.from_pb:
            aliases = dict(x.split("=", 1) for x in a.imports)
            sys.stdout.write(from_pb(a.from_pb, aliases))
            return 0
        if not (a.toml and a.outdir and a.pkg):
            ap.error("pbgen.py SECTION.toml OUTDIR --pkg NAME, or --from-pb FILE.pb.go...")
        with open(a.toml, "rb") as fh:
            doc = tomllib.load(fh)
        if "protobuf" not in doc:
            raise PbError(f"{a.toml}: no [protobuf] table")
        P = Messages(doc["protobuf"])
        header = f"// Code generated by pbgen.py from {os.path.basename(a.toml)}. DO NOT EDIT.\n\n"
        if not write_files(files(P, header, a.pkg, a.register), a.outdir, a.check):
            return 1
        if not a.check:
            print(f"{a.outdir}: {audit_lines(P)}")
        return 0
    except PbError as e:
        print(f"pbgen: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
