"""pbgen's trusted core: a protobuf codec (plain Go code, per message type) from a schema dump.

This module is the trusted part of etc/pbgen.py (the decision of 2026-11-19, `notes/decisions.md`,
"Trusted generated code: the generator is the trusted artifact"). Nothing in Lean fixes
protobuf's wire format: a program's proof uses whatever `PbCodec` its generated code is proved to
meet, and its final statement does not mention it. What is trusted is that running the program
with `proto.Marshal`/`proto.Unmarshal` replaced by the code this module emits behaves as with the
real google.golang.org/protobuf v1.36.12, for every schema this module accepts. Everything else
of pbgen (the command line, reading the toml, running the dump, the tests: `pbgen.py`,
`pbgen_testgen.py`) is untrusted: a bug there makes a test weaker or a run fail, never wrong code
accepted.

THE INPUT is a schema dump (`netmodels.lab/pbdesc`, `netmodels/pbdesc/pbdesc.go`): the facts of
the registered descriptors (`protoregistry`) that protoc-gen-go embeds in the `.pb.go` files of
the root message types and of every message and enum they reach, which are the descriptors the
real proto.Marshal and Unmarshal run on, and the generated Go structs' exported fields with their
`protobuf:"..."` tags (field number to Go field name and Go type). No field list is written by
hand. `Schema` checks the dump and refuses (PbRefused, every reason, naming the message and the
field) everything outside the subset; on a refusal no code is emitted.

THE SUBSET (accepted): messages of proto3 files (`syntax = "proto3"`), each mapped by protoc-gen-go
to a Go struct whose every field is an exported struct field of the expected Go type; fields of
kind int32 int64 uint32 uint64 sint32 sint64 fixed32 fixed64 sfixed32 sfixed64 bool string bytes,
open enums (of proto3 files), and messages (of the subset); singular with implicit presence
(scalars, enums), singular messages (a `*T`, presence by nil), repeated fields (scalars and enums
packed: proto3's default; strings, bytes, messages one record per element). Field numbers are
whatever the descriptor says (1..2^29-1 but 19000..19999, which protoc enforces; checked again).

REFUSED, by `Schema` (an error naming message and field; the reasons are `REFUSALS`'s keys):
proto2 and editions files (explicit presence by default, closed enums, unchecked strings, groups,
required fields, defaults, extensions); proto3 `optional` (explicit presence: a synthetic oneof);
oneofs; maps (and map-entry messages); groups; float and double; `[packed = false]` repeated
scalars and enums; required fields; fields with defaults; weak and lazy fields; messages with
extension ranges or the MessageSet wire format; enums that are closed or not of a proto3 file;
string fields without UTF-8 enforcement; a message or enum with no registered Go type; a field
with no exported Go struct field, or a Go type other than protoc-gen-go's open-struct one
(e.g. the opaque API's hidden fields); exported Go struct fields that are no descriptor field's
(a oneof's holder); Go package aliases or generated function names that collide.

THE EMITTED CODE, per field kind (the protobuf encoding spec, protobuf.dev/programming-guides/
encoding/, by section name; protobuf-go v1.36.12 by file and line in the Go module cache,
`google.golang.org/protobuf@v1.36.12/`; the wire helpers are `netmodels.lab/pbcodec`, each the
protowire function of the same name, tested in `netmodels/pbcodec/protowire_test.go`):

  Marshal (pbenc_T), the fields in increasing field-number order ("Field Order": the spec allows
  any order; protobuf-go sorts its coder fields by number, internal/impl/codec_message.go:158,
  and walks them in that order, internal/impl/encode.go:176), each as tag = varint(num<<3|wire
  type) ("Message Structure"; protowire.AppendTag, encoding/protowire/wire.go:162) then:
  - int32, int64, uint32, uint64 (wire type 0, "Base 128 Varints"): varint of the value, int32
    sign-extended to 64 bits ("Signed Integers": int32 negatives take 10 bytes; appendInt32NoZero
    etc., internal/impl/codec_gen.go:653).
  - sint32, sint64 (wire type 0): varint of the ZigZag encoding ("Signed Integers";
    protowire.EncodeZigZag, wire.go:550; sint32 widened to int64 first, codec_gen.go:1068).
  - bool (wire type 0): varint 0 or 1 (protowire.EncodeBool, wire.go:566).
  - enum (wire type 0): as int32 ("Enumerations" are int32 on the wire).
  - fixed32, sfixed32 (wire type 5), fixed64, sfixed64 (wire type 1): little-endian 4 or 8 bytes
    ("Non-varint Numbers"; wire.go:402, 426).
  - string, bytes (wire type 2, "Length-Delimited Records"): varint length then the bytes
    (wire.go:454, 478); a string that is not valid UTF-8 makes Marshal fail (proto3 strings are
    validated, internal/strs/strings.go:19-25, appendStringNoZeroValidateUTF8, codec_gen.go:5107;
    the spec leaves invalid UTF-8 to the implementation).
  - singular scalar or enum: omitted when zero (0, false, "" , a nil or empty []byte)
    ("Implicit presence"/"Default Values"; protobuf-go's NoZero coders, codec_tables.go:200).
  - singular message: omitted when nil; otherwise tag, varint length, the message's encoding (a
    non-nil empty message is written, tag and length 0; "Embedded Messages"; appendMessageInfo,
    internal/impl/codec_field.go:163).
  - repeated scalar or enum: one packed record (tag, wire type 2, length, the values' encodings
    without tags), omitted when empty ("Packed Repeated Fields": proto3's default; protobuf-go's
    PackedSlice coders, e.g. appendInt32PackedSlice, codec_gen.go:823, omit an empty slice).
  - repeated string, bytes, message: one record per element, in order ("Repeated Elements"); a
    nil element of a repeated message field is written as an empty message (tag, length 0:
    appendMessageSliceInfo, codec_field.go:419, sizes and appends a nil pointer as empty); a
    repeated string element is UTF-8 checked (appendStringSliceValidateUTF8, codec_gen.go:5250).
  - Marshal of a nil *T returns nil, of a non-nil *T with no field written a non-nil empty slice
    (proto/encode.go:105-146, emptyBytesForMessage). Unknown fields are never written (below).

  Unmarshal (pbUnmarshal: *m reset, `*m = T{}`, as proto.Unmarshal's Reset, proto/decode.go:95;
  then pbdec_T with depth 10000), a loop over the input's fields as protobuf-go's
  unmarshalPointerEager (internal/impl/decode.go:125-236):
  - the tag: a varint (malformed: error), field number 1..2^29-1 (else error, decode.go:154),
    an end-group tag is an error (no group is open at a message's level, decode.go:161).
  - a known field number with its own wire type: decoded and stored; a varint field's value is
    truncated to the Go type (int32(v), uint32(v), bool v != 0, enum int32(v); sint32 zigzag of
    the low 32 bits: consumeInt32, codec_gen.go:611, consumeSint32, codec_gen.go:1026); a scalar
    or enum occurrence replaces the field ("Last One Wins"); a message occurrence merges into the
    message already there, allocating it if nil (consumeMessageInfo, codec_field.go:175; "Merging
    of embedded messages"); a repeated field appends, a fresh message per occurrence
    (consumeMessageSliceInfo, codec_field.go:438).
  - a repeated scalar or enum accepts both packed (wire type 2: values until the record's end; a
    value cut short is an error) and unpacked (its own wire type) occurrences ("Packed Repeated
    Fields": parsers must accept both; consumeInt32Slice, codec_gen.go:741).
  - a string field's bytes must be valid UTF-8 (else error: consumeStringValidateUTF8,
    codec_gen.go:5053, unicode/utf8.Valid); a singular bytes field decodes an empty value to nil
    (consumeBytesNoZero, codec_gen.go:5489: append to nil), a repeated bytes element to a non-nil
    empty slice (consumeBytesSlice, codec_gen.go:5568).
  - a field number the message does not have, or a known one with another wire type (the coder
    returns errUnknown, e.g. codec_gen.go:612): an unknown field, skipped by
    protowire.ConsumeFieldValue (decode.go:222; groups nested up to its own limit of 10000,
    wire.go:112-160; a malformed value, an unmatched end group, a reserved wire type 6 or 7: error).
  - nesting: each message decoded takes one level of the recursion limit 10000 (the outermost
    included; deeper is an error: decode.go:105, proto/decode.go:62, protowire.DefaultRecursionLimit).
  - Unmarshal into a nil *T panics (protobuf-go's Reset of a nil message panics too).

  Where the claim stops (documented deviations, outside "behaves as protobuf-go"):
  - unknown fields: protobuf-go keeps them in the message (decode.go:225) and Marshal writes
    them back; the emitted code checks and drops them (it cannot reach the struct's unexported
    unknownFields). A program that re-sends a message decoded from input carrying fields its
    schema does not know (a peer with a newer schema, or a corrupted input) behaves differently;
    between peers of the same schema none arise.
  - error values: only error-or-not is the real one's (*pbcodec.Error, not protobuf-go's types).
  - only proto.Marshal and proto.Unmarshal with default options, on *T of the derived types;
    any other value panics ("not modelled"). proto.Size, Equal, Clone, Merge, MarshalOptions
    (Deterministic is moot: no maps), protojson, prototext are not covered.

The evidence (untrusted, pbgen.py --help): the generator's differential test over random schemas
of the subset (`netmodels/internal/pbgenrand`), the per-schema regression tests generated beside
each codec (pb_gen_test.go), and the independent review `notes/axiom-review/pbgen.md`.
"""

import re

MAX_NUM = (1 << 29) - 1

# scalar kind (protoreflect.Kind's name): (Go type, wire type, encode (x: the Go value) to the
# wire value, decode (v: the wire value) to the Go value)
SCALARS = {
    "int32": ("int32", "VarintType", "uint64(int64({x}))", "int32({v})"),
    "int64": ("int64", "VarintType", "uint64({x})", "int64({v})"),
    "uint32": ("uint32", "VarintType", "uint64({x})", "uint32({v})"),
    "uint64": ("uint64", "VarintType", "{x}", "{v}"),
    "sint32": ("int32", "VarintType", "pbcodec.EncodeZigZag(int64({x}))", "pbcodec.DecodeZigZag32({v})"),
    "sint64": ("int64", "VarintType", "pbcodec.EncodeZigZag({x})", "pbcodec.DecodeZigZag({v})"),
    "bool": ("bool", "VarintType", "pbcodec.EncodeBool({x})", "{v} != 0"),
    "fixed32": ("uint32", "Fixed32Type", "{x}", "{v}"),
    "sfixed32": ("int32", "Fixed32Type", "uint32({x})", "int32({v})"),
    "fixed64": ("uint64", "Fixed64Type", "{x}", "{v}"),
    "sfixed64": ("int64", "Fixed64Type", "uint64({x})", "int64({v})"),
    "string": ("string", "BytesType", None, None),
    "bytes": ("[]byte", "BytesType", None, None),
}

# reflect's String of each scalar's Go type ([]byte prints as []uint8)
REFLECT_GO = {k: ("[]uint8" if v[0] == "[]byte" else v[0]) for k, v in SCALARS.items()}

# The identifiers the emitted code uses for itself: no package alias may be one.
RESERVED = {"pbcodec", "b", "m", "p", "i", "num", "typ", "n", "ok", "ok2", "k", "k2", "v", "e",
            "sub", "j", "depth", "pbMarshal", "pbUnmarshal", "interface", "nil", "uint64", "make",
            "append", "panic", "string", "len", "true", "false", "error", "byte", "bool", "int32",
            "int64", "uint32",
            # the packages the generated test (pb_gen_test.go) imports
            "bytes", "math", "rand", "os", "reflect", "strconv", "strings", "testing", "proto",
            "protowire", "protoreflect"}


class PbRefused(Exception):
    """The schema is outside the subset: every reason, one per line."""

    def __init__(self, reasons):
        self.reasons = reasons
        super().__init__("\n".join(reasons))


def ident(name):
    """A Go identifier for a type reference: raxos.ProposerMessage -> raxos_ProposerMessage."""
    return re.sub(r"[^A-Za-z0-9]", "_", name)


class Field:
    def __init__(self, name, num, kind, rep, cat, proto_name=""):
        self.name = name   # Go field name
        self.num = num     # field number
        self.kind = kind   # the element kind: a scalar's name, or an enum or message type (alias.T)
        self.rep = rep     # repeated
        self.cat = cat     # "scalar", "enum" or "message"
        self.proto_name = proto_name

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


class Schema:
    """A schema dump (pbdesc's JSON), checked against the subset.

    names: the message types (Go references alias.T, sorted); m: name -> fields (by number);
    enums: the enum types (alias.T); imports: alias -> Go import path; full: name -> protobuf
    full name. aliases: the toml's {alias: import path}, used for those paths; another path's
    alias is its package name (with "_" appended until it is free)."""

    def __init__(self, dump, aliases=None):
        aliases = dict(aliases or {})
        why = []
        msgs = {d["full_name"]: d for d in dump["messages"]}
        enums = {d["full_name"]: d for d in dump["enums"]}

        # Go package aliases
        self.imports = {}
        by_path = {}
        for a, p in sorted(aliases.items()):
            if not re.fullmatch(r"[A-Za-z_]\w*", a) or a in RESERVED:
                why.append(f"import alias {a!r}: not a Go identifier the codec may use")
            if p in by_path:
                why.append(f"import path {p}: two aliases")
            by_path[p] = a
            self.imports[a] = p
        gos = [d["go"] for d in list(msgs.values()) + list(enums.values()) if d.get("go")]
        for g in sorted(gos, key=lambda g: g["pkg"]):
            if g["pkg"] in by_path:
                continue
            a = g["pkg_name"]
            while a in self.imports or a in RESERVED or not re.fullmatch(r"[A-Za-z_]\w*", a):
                a = (a if re.fullmatch(r"[A-Za-z_]\w*", a) else "pkg") + "_"
            by_path[g["pkg"]] = a
            self.imports[a] = g["pkg"]

        def ref(g):
            return f"{by_path[g['pkg']]}.{g['name']}"

        # enums
        self.enums = []
        enum_ref = {}
        for fn, e in sorted(enums.items()):
            where = f"enum {fn} ({e['file']})"
            if e["syntax"] != "proto3":
                why.append(f"{where}: an enum of a {e['syntax']} file (outside the subset: proto3 only)")
            if e["closed"]:
                why.append(f"{where}: a closed enum (outside the subset)")
            if not e.get("go"):
                why.append(f"{where}: no registered Go type")
                continue
            if e.get("go_kind") != "int32":
                why.append(f"{where}: Go type of kind {e.get('go_kind')}, not int32")
            enum_ref[fn] = ref(e["go"])
            self.enums.append(enum_ref[fn])

        msg_ref = {fn: ref(d["go"]) for fn, d in msgs.items() if d.get("go")}

        # messages
        self.m = {}
        self.full = {}
        for fn, d in sorted(msgs.items()):
            where = f"message {fn} ({d['file']})"
            if d["syntax"] != "proto3":
                why.append(f"{where}: a {d['syntax']} file (outside the subset: proto3 only)")
            if d["map_entry"]:
                why.append(f"{where}: a map entry (maps are outside the subset)")
            if d["message_set"]:
                why.append(f"{where}: the MessageSet wire format (outside the subset)")
            if d["extension_ranges"]:
                why.append(f"{where}: extension ranges (extensions are outside the subset)")
            if d["oneofs"]:
                why.append(f"{where}: {d['oneofs']} oneof(s) (outside the subset; proto3 `optional` "
                           "fields are synthetic oneofs)")
            if not d.get("go"):
                why.append(f"{where}: no registered Go type")
                continue
            for x in d["go_extra"]:
                why.append(f"{where}: Go field {x} is no descriptor field's (a oneof's holder?)")
            fields = []
            for f in d["fields"]:
                fx = self._field(fn, f, msgs, enums, enum_ref, msg_ref, why)
                if fx is not None:
                    fields.append(fx)
            nums = [f["number"] for f in d["fields"]]
            if len(set(nums)) != len(nums):
                why.append(f"{where}: a field number twice")
            r = msg_ref[fn]
            self.m[r] = sorted(fields, key=lambda f: f.num)
            self.full[r] = fn
        self.names = sorted(self.m)
        self.enums.sort()

        # generated names must not collide
        ids = {}
        for n in self.names + self.enums:
            ids.setdefault(ident(n), []).append(n)
        for i, ns in ids.items():
            if len(ns) > 1:
                why.append(f"types {', '.join(ns)}: the same generated name {i}")
        if not self.names:
            why.append("no message types")
        if why:
            raise PbRefused(why)

    @staticmethod
    def _field(mfn, f, msgs, enums, enum_ref, msg_ref, why):
        """The Field of descriptor field f of message mfn, or None (reasons added to why)."""
        where = f"field {mfn}.{f['name']} (number {f['number']})"
        n0 = len(why)
        kind, card = f["kind"], f["cardinality"]
        rep = card == "repeated"
        if f["oneof"]:
            if f["synthetic_oneof"]:
                why.append(f"{where}: proto3 `optional`, explicit presence (outside the subset)")
            else:
                why.append(f"{where}: in oneof {f['oneof']} (outside the subset)")
        if f["is_map"]:
            why.append(f"{where}: a map (outside the subset)")
        if card == "required":
            why.append(f"{where}: required (outside the subset)")
        if f["has_default"]:
            why.append(f"{where}: an explicit default (outside the subset)")
        if f["is_weak"] or f["lazy"]:
            why.append(f"{where}: weak or lazy (outside the subset)")
        if kind in ("float", "double"):
            why.append(f"{where}: {kind} (outside the subset)")
        elif kind == "group":
            why.append(f"{where}: a group (outside the subset)")
        elif kind not in SCALARS and kind not in ("enum", "message"):
            why.append(f"{where}: kind {kind} (outside the subset)")
        if not (1 <= f["number"] <= MAX_NUM) or 19000 <= f["number"] <= 19999:
            why.append(f"{where}: field number outside 1..2^29-1 or in 19000..19999")
        if rep and kind not in ("string", "bytes", "message", "group") and not f["packed"]:
            why.append(f"{where}: a repeated {kind} not packed ([packed = false]; outside the subset)")
        if rep and kind in ("string", "bytes", "message") and f["packed"]:
            why.append(f"{where}: a packed {kind} (impossible)")
        if not rep and kind != "message" and f["has_presence"] and not f["oneof"]:
            why.append(f"{where}: explicit presence (outside the subset)")
        if kind == "string" and not f["enforce_utf8"]:
            why.append(f"{where}: a string without UTF-8 validation (outside the subset)")
        if not f["go_field"]:
            why.append(f"{where}: no exported Go struct field with its number")
        if len(why) > n0:
            return None
        # the element and the Go type protoc-gen-go's open struct API gives it
        if kind == "enum":
            if f["enum"] not in enum_ref:
                why.append(f"{where}: enum {f['enum']} has no Go type")
                return None
            el, cat, want_el = enum_ref[f["enum"]], "enum", None
        elif kind == "message":
            d = msgs.get(f["message"])
            if d is None or f["message"] not in msg_ref:
                why.append(f"{where}: message {f['message']} not in the dump or with no Go type")
                return None
            el, cat, want_el = msg_ref[f["message"]], "message", "*"
        else:
            el, cat, want_el = kind, "scalar", None
        g = f.get("go_elem")
        if cat == "scalar":
            want = ("[]" if rep else "") + REFLECT_GO[kind]
        else:
            if not g:
                why.append(f"{where}: Go field {f['go_field']} of type {f['go_type']}, not a named type")
                return None
            want = ("[]" if rep else "") + (want_el or "") + f"{g['pkg_name']}.{g['name']}"
            exp = (msgs[f["message"]] if cat == "message" else enums[f["enum"]])["go"]
            if (exp["pkg"], exp["name"]) != (g["pkg"], g["name"]):
                why.append(f"{where}: Go field type {f['go_type']} is not the {cat}'s registered Go type")
                return None
        if f["go_type"] != want:
            why.append(f"{where}: Go field {f['go_field']} of type {f['go_type']}, expected {want}")
            return None
        return Field(f["go_field"], f["number"], el, rep, cat, f["name"])


# ---------------------------------------------------------------------------------------------
# The codec (pb_gen.go)

CODEC_DOC = """// The protobuf codec (registered with a model of google.golang.org/protobuf, proto.SetCodec):
// pbMarshal and pbUnmarshal for exactly the message types below, derived by etc/pbgen.py from
// their registered descriptors, over the wire format of netmodels.lab/pbcodec. The trusted claim
// is the generator's (etc/pbgen_core.py's doc, field kind by field kind, against protobuf-go
// v1.36.12):
//
//   - pbMarshal(m), m a *T of a type below: real proto.Marshal(m)'s bytes (fields in number
//     order, proto3's zero values omitted, a nil element of a repeated message field written as
//     an empty message; nil for a nil *T, an empty non-nil slice for an empty message), or an
//     error where the real one errs (a string field that is not UTF-8).
//   - pbUnmarshal(b, m), m a non-nil *T of a type below: resets *m and decodes b into it as
//     real proto.Unmarshal does (merging repeated occurrences), or an error where the real one
//     errs (malformed input, a field number 0 or above 2^29-1, invalid UTF-8 in a string field,
//     messages nested deeper than 10000). Unknown fields are checked and skipped (the real one
//     keeps them in the message: the model does not). A nil *T panics, as the real one does.
//   - Any other value (another type, a non-pointer, a nil interface) panics: outside the
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
    return SCALARS[f.kind][2].format(x=x)


def append_value(buf, f, x):
    """A Go expression: buf with the wire value of x (a numeric element of f) appended."""
    w = f.wire()
    if w == "VarintType":
        return f"pbcodec.AppendVarint({buf}, {enc_expr(f, x)})"
    if w == "Fixed32Type":
        return f"pbcodec.AppendFixed32({buf}, {enc_expr(f, x)})"
    return f"pbcodec.AppendFixed64({buf}, {enc_expr(f, x)})"


def zero_test(f, x):
    """A Go condition: x (a singular scalar or enum) is not its zero value."""
    if f.kind in ("string", "bytes"):
        return f"len({x}) > 0"
    if f.kind == "bool":
        return x
    return f"{x} != 0"


def gen_encoder(S, n):
    I = ident(n)
    out = [f"// pbenc_{I} appends the encoding of *m's fields (real proto.Marshal's, in field-number",
           "// order); false if a string field is not UTF-8. A nil m encodes as an empty message.",
           f"func pbenc_{I}(b []byte, m *{n}) ([]byte, bool) {{",
           "\tif m == nil {", "\t\treturn b, true", "\t}"]
    body = []
    for f in S.m[n]:
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


def dec_elem(f, v):
    """A Go expression: the Go value of numeric element wire value v (from Consume...)."""
    if f.cat == "enum":
        return f"{f.kind}(int32({v}))"
    return SCALARS[f.kind][3].format(v=v)


def consume_fn(f):
    return {"VarintType": "pbcodec.ConsumeVarint", "Fixed32Type": "pbcodec.ConsumeFixed32",
            "Fixed64Type": "pbcodec.ConsumeFixed64"}[f.wire()]


def gen_decoder(S, n):
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
    for f in S.m[n]:
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
            one += [f"{x} = append({x}, {dec_elem(f, 'v')})" if f.rep else f"{x} = {dec_elem(f, 'v')}"]
            one += ["return k, true"]
            body += [f"if num == {f.num} && typ == pbcodec.{w} {{"] + ["\t" + l for l in one] + ["}"]
            if f.rep:
                body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                         "\tp, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}",
                         "\tj := uint64(0)", "\tfor j < uint64(len(p)) {",
                         f"\t\tv, k2, ok2 := {consume_fn(f)}(p[j:])", "\t\tif !ok2 {", "\t\t\treturn 0, false", "\t\t}",
                         f"\t\t{x} = append({x}, {dec_elem(f, 'v')})",
                         "\t\tj = j + k2", "\t}", "\treturn k, true", "}"]
    body += ["return pbcodec.SkipField(num, typ, b)"]
    out += ["\t" + l for l in body] + ["}", ""]
    return out


def used_imports(S, text, extra=()):
    """Import lines (sorted by path, as gofmt sorts them) for the aliases text uses, and extra
    (import paths)."""
    lines = [(p, f'\t"{p}"') for p in extra]
    for a, p in S.imports.items():
        if re.search(r"(?<![\w.])" + re.escape(a) + r"\.", text):
            lines.append((p, f'\t{a} "{p}"'))
    return [l for _, l in sorted(lines)]


def codec_go(S, header, go_name):
    """pb_gen.go: the codec (all builds)."""
    body = [CODEC_DOC, "",
            "// pbMarshal is the codec's Marshal.",
            "func pbMarshal(m interface{}) ([]byte, error) {",
            "\tswitch p := m.(type) {"]
    for n in S.names:
        body += [f"\tcase *{n}:", "\t\tif p == nil {", "\t\t\treturn nil, nil", "\t\t}",
                 f"\t\tb, ok := pbenc_{ident(n)}(make([]byte, 0), p)", "\t\tif !ok {",
                 "\t\t\treturn nil, &pbcodec.Error{Msg: \"string field contains invalid UTF-8\"}", "\t\t}",
                 "\t\treturn b, nil"]
    body += ["\t}", "\tpanic(\"protobuf model: marshaling a value of a type the codec was not generated for\")",
             "}", "",
             "// pbUnmarshal is the codec's Unmarshal.",
             "func pbUnmarshal(b []byte, m interface{}) error {",
             "\tswitch p := m.(type) {"]
    for n in S.names:
        body += [f"\tcase *{n}:", "\t\tif p == nil {",
                 "\t\t\tpanic(\"protobuf model: Unmarshal into a nil message pointer\")", "\t\t}",
                 f"\t\t*p = {n}{{}}",
                 f"\t\tif !pbdec_{ident(n)}(b, p, pbcodec.DefaultRecursionLimit) {{",
                 "\t\t\treturn &pbcodec.Error{Msg: \"cannot parse invalid wire-format data\"}", "\t\t}",
                 "\t\treturn nil"]
    body += ["\t}", "\tpanic(\"protobuf model: unmarshaling into a value of a type the codec was not generated for\")",
             "}", ""]
    for n in S.names:
        body += gen_encoder(S, n)
        body += gen_decoder(S, n)
    text = "\n".join(body)
    imps = used_imports(S, text, ["netmodels.lab/pbcodec"])
    return header + f"package {go_name}\n\nimport (\n" + "\n".join(imps) + "\n)\n\n" + text


def model_go(header, go_name):
    """pb_model_gen.go: registerProto for the protobuf model (build tags rpcmodel, goose)."""
    return (header + "//go:build rpcmodel || goose\n\n" + f"package {go_name}\n\n"
            "import \"google.golang.org/protobuf/proto\"\n\n"
            "// registerProto registers the codec with the protobuf model (the first registration\n"
            "// stays).\n"
            "func registerProto() {\n"
            "\tproto.SetCodec(&proto.Codec{Marshal: pbMarshal, Unmarshal: pbUnmarshal})\n"
            "}\n")


def real_go(header, go_name):
    """pb_real_gen.go: registerProto for the real module (no codec)."""
    return (header + "//go:build !rpcmodel && !goose\n\n" + f"package {go_name}\n\n"
            "// registerProto: the real google.golang.org/protobuf needs no codec.\n"
            "func registerProto() {}\n")
