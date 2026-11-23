"""pbgen's trusted core: a protobuf codec (plain Go code, per message type) from a schema dump.

This module is the trusted part of models/protobuf/pbgen.py (the decision of 2026-11-19, `notes/decisions.md`,
"Trusted generated code: the generator is the trusted artifact"). Nothing in Lean fixes
protobuf's wire format: a program's proof uses whatever `PbCodec` its generated code is proved to
meet, and its final statement does not mention it. What is trusted is that running the program
with `proto.Marshal`/`proto.Unmarshal` replaced by the code this module emits behaves as with the
real google.golang.org/protobuf v1.36.12, for every schema this module accepts. Everything else
of pbgen (the command line, reading the toml, running the dump, the tests: `pbgen.py`,
`pbgen_testgen.py`) is untrusted: a bug there makes a test weaker or a run fail, never wrong code
accepted. `models/pbdesc` (the Go program that produces the dump this module reads) is trusted
with it: a wrong fact there would be wrong code accepted.

THE INPUT is a schema dump (`models.lab/pbdesc`, `models/pbdesc/pbdesc.go`): the facts of
the registered descriptors (`protoregistry`) that protoc-gen-go embeds in the `.pb.go` files of
the root message types and of every message and enum they reach, which are the descriptors the
real proto.Marshal and Unmarshal run on, and the generated Go structs' exported fields with their
`protobuf:"..."` tags (field number to Go field name and Go type). No field list is written by
hand. The dump is made in the Go module the codec is generated into (pbgen.py runs it there), so
it reads the very `.pb.go` files the program links. `Schema` checks the dump and refuses (PbRefused, every reason, naming the message and the
field) everything outside the subset; on a refusal no code is emitted.

THE SUBSET (accepted): messages of proto2 and proto3 files (`syntax = "proto2"` or "proto3"), each
mapped by protoc-gen-go to a Go struct whose every field is an exported struct field of the
expected Go type (or a oneof's holder); fields of kind int32 int64 uint32 uint64 sint32 sint64
fixed32 fixed64 sfixed32 sfixed64 bool string bytes, enums (open ones of proto3 files, closed ones
of proto2 files), and messages (of the subset); singular with implicit presence (proto3 scalars
and enums), singular with explicit presence (proto2 `optional` and `required` scalars and enums,
proto3 `optional`: a `*T`, a `[]byte` for bytes, present when non-nil), singular messages (a `*T`,
presence by nil), oneofs (an interface holder, one wrapper struct per member: scalars, enums,
strings, bytes, messages), repeated fields (scalars and enums packed or unpacked, as the
descriptor says: proto3's default packed, proto2's unpacked, either changed by `[packed = ...]`;
strings, bytes, messages one record per element). Required fields, and explicit defaults (which
only the generated getters read: no coder of protobuf-go looks at them, below). Strings of proto3
files are UTF-8 checked, those of proto2 files not (as protobuf-go: strs.EnforceUTF8). Field
numbers are whatever the descriptor says (1..2^29-1 but 19000..19999, which protoc enforces;
checked again).

REFUSED, by `Schema` (an error naming the message and the field, every reason listed):
editions files (features per field: delimited encoding, presence, UTF-8, packing); maps (and
map-entry messages); groups (in or out of a oneof); float and double; weak and lazy fields;
messages with extension ranges or the MessageSet wire format; a message or enum with no
registered Go type; a field with no exported Go struct field (for a oneof member: no registered
wrapper type implementing its holder), or a Go type other than protoc-gen-go's open-struct one
(e.g. the opaque API's hidden fields, or the hybrid API's `XXX_presence`); exported Go struct
fields that are no descriptor field's nor a oneof's holder; APIv1 oneofs (an `XXX_OneofFuncs` or
`XXX_OneofWrappers` method); Go package aliases or generated function names that collide. And
two schemas where protobuf-go's own required-field checks are not what the descriptors say
(`models/internal/pbgenrand`'s TestProtobufQuirks shows both on protobuf-go; the review
`notes/axiom-review/pbgen.md`, "The proto2 and oneof extension"): a message type that reaches required
fields only through a cycle of two or more message types (protobuf-go's needsInitCheck caches a
false for it, depending on which type the program uses first: internal/impl/checkinit.go:137-170);
a oneof member other than the oneof's first declared one, of a message type that reaches required
fields (Unmarshal's fast path consults the isInit of the field's own coder, decode.go:189, which
only the first member's coder has, codec_field.go:83-118: a missing required field in it passes
Unmarshal; Marshal's check sees it).

THE EMITTED CODE, per field kind (the protobuf encoding spec, protobuf.dev/programming-guides/
encoding/, by section name; protobuf-go v1.36.12 by file and line in the Go module cache,
`google.golang.org/protobuf@v1.36.12/`; the wire helpers are `models.lab/pbcodec`, each the
protowire function of the same name, tested in `models/pbcodec/protowire_test.go`):

  Marshal (pbenc_T), the fields in no oneof in increasing field-number order, then each oneof's
  one set member, the oneofs in declaration order ("Field Order": the spec allows any order;
  protobuf-go sorts its coder fields by number, internal/impl/codec_message.go:158, and walks them
  in that order, internal/impl/encode.go:176, but a message with oneofs is sorted again by
  order.LegacyFieldOrder, codec_message.go:177-184 and internal/order/order.go:21-41: fields in
  no (non-synthetic) oneof first, by number, then the oneofs by declaration index), each as tag =
  varint(num<<3|wire type) ("Message Structure"; protowire.AppendTag,
  encoding/protowire/wire.go:162) then:
  - int32, int64, uint32, uint64 (wire type 0, "Base 128 Varints"): varint of the value, int32
    sign-extended to 64 bits ("Signed Integers": int32 negatives take 10 bytes; appendInt32NoZero
    etc., internal/impl/codec_gen.go:653).
  - sint32, sint64 (wire type 0): varint of the ZigZag encoding ("Signed Integers";
    protowire.EncodeZigZag, wire.go:550; sint32 widened to int64 first, codec_gen.go:1068).
  - bool (wire type 0): varint 0 or 1 (protowire.EncodeBool, wire.go:566).
  - enum (wire type 0): as int32 ("Enumerations" are int32 on the wire; coderEnumPtr and
    coderEnumSlice are the int32 coders, internal/impl/codec_unsafe.go:12-13).
  - fixed32, sfixed32 (wire type 5), fixed64, sfixed64 (wire type 1): little-endian 4 or 8 bytes
    ("Non-varint Numbers"; wire.go:402, 426).
  - string, bytes (wire type 2, "Length-Delimited Records"): varint length then the bytes
    (wire.go:454, 478); a UTF-8-checked string (a proto3 file's) that is not valid UTF-8 makes
    Marshal fail (internal/strs/strings.go:19-25, appendStringNoZeroValidateUTF8,
    codec_gen.go:5107, appendStringPtrValidateUTF8, codec_gen.go:5170); a proto2 file's string
    is written as it is (appendString, codec_gen.go:5013, appendStringPtr, codec_gen.go:5136;
    the spec leaves invalid UTF-8 to the implementation). Which coder a field gets is
    fieldCoder's choice, internal/impl/codec_tables.go:37-365, by the descriptor and the Go type.
  - singular scalar or enum with implicit presence: omitted when zero (0, false, "" , a nil or
    empty []byte) ("Implicit presence"/"Default Values"; the NoZero coders, codec_tables.go:200).
  - singular scalar or enum with explicit presence (proto2 `optional` and `required`, proto3
    `optional`): written when the pointer (for bytes: the slice) is non-nil, whatever its value,
    zero or the field's default included ("Explicit presence"; the Ptr coders,
    codec_tables.go:281, e.g. appendUint64Ptr, codec_gen.go:2754; bytes: coderBytes,
    codec_tables.go:352, appendBytes, codec_gen.go:5402; the coder field isPointer,
    codec_message.go:136, skipped when nil, encode.go:212).
  - singular message: omitted when nil; otherwise tag, varint length, the message's encoding (a
    non-nil empty message is written, tag and length 0; "Embedded Messages"; appendMessageInfo,
    internal/impl/codec_field.go:163).
  - oneof: nothing when the holder is nil or holds a nil wrapper pointer; otherwise the member of
    the wrapper's type, written whatever its value (zero, nil or empty bytes included; a nil
    message as an empty one: tag, length 0) (initOneofFieldCoders' getInfo and marshal,
    codec_field.go:72-97, the member's coder chosen for the wrapper's field type with presence,
    codec_tables.go:352, and appendMessageInfo over a nil pointer, codec_field.go:163).
  - repeated scalar or enum, packed (the descriptor's IsPacked: proto3's default, proto2's with
    `[packed = true]`): one record (tag, wire type 2, length, the values' encodings without
    tags), omitted when empty ("Packed Repeated Fields"; the PackedSlice coders, e.g.
    appendInt32PackedSlice, codec_gen.go:823, omit an empty slice); unpacked (proto2's default,
    proto3's with `[packed = false]`): one record per element with the element's own wire type,
    in order (the Slice coders, codec_tables.go:41, e.g. appendUint64Slice, codec_gen.go:2806).
  - repeated string, bytes, message: one record per element, in order ("Repeated Elements"); a
    nil element of a repeated message field is written as an empty message (tag, length 0:
    appendMessageSliceInfo, codec_field.go:419, sizes and appends a nil pointer as empty); a
    repeated string element of a proto3 file is UTF-8 checked (appendStringSliceValidateUTF8,
    codec_gen.go:5250).
  - Marshal of a nil *T returns nil, of a non-nil *T with no field written a non-nil empty slice
    (proto/encode.go:105-146, emptyBytesForMessage). Unknown fields are never written (below).
  - required fields (proto2): after encoding, Marshal fails unless the message is initialized:
    every required field of it is set (non-nil), and every message it holds is initialized (a
    singular one when non-nil, every element of a repeated one, a nil element included, the
    message of a oneof's set member, a nil one included), where a nil message is initialized iff
    its type has no required field of its own (proto/encode.go:205-209, checkInitialized;
    internal/impl/checkinit.go:25-96, checkInitializedPointer, which checks only the types that
    reach a required field, needsInitCheck, checkinit.go:126-170, and a oneof through its first
    member's isInit, codec_field.go:110-118). Marshal of a nil *T of a type with a required field
    fails too (checkInitializedPointer of nil, checkinit.go:30-37).

  Unmarshal (pbUnmarshal: *m reset, `*m = T{}`, as proto.Unmarshal's Reset, proto/decode.go:95;
  then pbdec_T with depth 10000), a loop over the input's fields as protobuf-go's
  unmarshalPointerEager (internal/impl/decode.go:125-236):
  - the tag: a varint (malformed: error), field number 1..2^29-1 (else error, decode.go:154),
    an end-group tag is an error (no group is open at a message's level, decode.go:161).
  - a known field number with its own wire type: decoded and stored; a varint field's value is
    truncated to the Go type (int32(v), uint32(v), bool v != 0, enum int32(v); sint32 zigzag of
    the low 32 bits: consumeInt32, codec_gen.go:611, consumeSint32, codec_gen.go:1026); a scalar
    or enum occurrence replaces the field ("Last One Wins"); a field with explicit presence is
    stored through its pointer, allocated when nil (consumeUint64Ptr, codec_gen.go:2762-2785;
    the same in every Ptr consumer); a message occurrence merges into the message already there,
    allocating it if nil (consumeMessageInfo, codec_field.go:175; "Merging of embedded
    messages"); a repeated field appends, a fresh message per occurrence
    (consumeMessageSliceInfo, codec_field.go:438).
  - an enum's value is stored as it is, a closed (proto2) enum's too, even one that names no
    value: protobuf-go treats closed enums as open (no coder of internal/impl looks at the enum's
    values or closedness; the enum guide, protobuf.dev/programming-guides/enum, lists Go as not
    conformant for closed enums), where a conformant parser would keep an unknown value of a
    closed enum as an unknown field.
  - an explicit default is never stored nor checked: it is the generated getter's (`GetX`
    returns `Default_T_X` when the pointer is nil); no coder reads it (internal/impl's only use of
    a field's Default is a map entry's key, codec_map.go:44).
  - a oneof member: if the holder already holds a non-nil wrapper of this member's type, the
    value goes into it (a message merges into the one there, allocated if nil), else into a new
    wrapper, which becomes the oneof's value (initOneofFieldCoders' unmarshal,
    codec_field.go:53-70); so the last member decoded wins (the encoding guide's "Oneofs": a
    parser keeps the last member seen) and a member with another wire type than its own is
    unknown, leaving the oneof as it was (the member's coder returns errUnknown before the
    wrapper is set, codec_field.go:61-63).
  - a repeated scalar or enum accepts both packed (wire type 2: values until the record's end; a
    value cut short is an error) and unpacked (its own wire type) occurrences, whatever the
    descriptor's packing ("Packed Repeated Fields": parsers must accept both; consumeInt32Slice,
    codec_gen.go:741, the consumer of both the packed and the unpacked coder, e.g.
    coderUint64PackedSlice, codec_gen.go:2915).
  - a UTF-8-checked string field's (a proto3 file's) bytes must be valid UTF-8 (else error:
    consumeStringValidateUTF8, codec_gen.go:5053, unicode/utf8.Valid); a proto2 file's are not
    checked (consumeString, codec_gen.go:5021, consumeStringPtr, codec_gen.go:5144,
    consumeStringSlice, codec_gen.go:5228); a singular bytes field with implicit presence decodes
    an empty value to nil (consumeBytesNoZero, codec_gen.go:5489: append to nil), one with
    explicit presence, a oneof member and a repeated element to a non-nil empty slice
    (consumeBytes, codec_gen.go:5410, and consumeBytesSlice, codec_gen.go:5568: append to
    emptyBuf[:]).
  - a field number the message does not have, or a known one with another wire type (the coder
    returns errUnknown, e.g. codec_gen.go:612): an unknown field, skipped by
    protowire.ConsumeFieldValue (decode.go:222; groups nested up to its own limit of 10000,
    wire.go:112-160; a malformed value, an unmatched end group, a reserved wire type 6 or 7: error).
  - nesting: each message decoded takes one level of the recursion limit 10000 (the outermost
    included; deeper is an error: decode.go:105, proto/decode.go:62, protowire.DefaultRecursionLimit).
  - required fields (proto2): after decoding, Unmarshal fails unless the message is initialized,
    as Marshal checks it (above; proto/decode.go:132-135). protobuf-go skips that check when its
    decoding saw every required field of each message decoded and the messages they hold were
    initialized (the UnmarshalInitialized flag, internal/impl/decode.go:186-191, 237-242; past 64
    required fields in a message the mask never fills and the check always runs); with the
    refusal above (a oneof's non-first member) the skip happens only where the check would pass.
  - Unmarshal into a nil *T panics (protobuf-go's Reset of a nil message panics too).

  Where the claim stops (documented deviations, outside "behaves as protobuf-go"):
  - unknown fields: protobuf-go keeps them in the message (decode.go:225) and Marshal writes
    them back; the emitted code checks and drops them (it cannot reach the struct's unexported
    unknownFields). A program that re-sends a message decoded from input carrying fields its
    schema does not know (a peer with a newer schema, or a corrupted input) behaves differently;
    between peers of the same schema none arise.
  - error values: only error-or-not is the real one's (*pbcodec.Error, not protobuf-go's types).
  - what comes with an error (found by the review, notes/axiom-review/pbgen.md): Marshal returns
    nil with its error where protobuf-go returns the bytes written so far (proto/encode.go:111);
    after a failed Unmarshal the message's contents are not the real one's (e.g. a packed record
    cut short: the emitted code has appended the values before the bad one, protobuf-go leaves
    the field's length as it was, codec_gen.go:741-777). A program must not use either; protobuf-go
    promises nothing of them.
  - slice capacities and aliasing (the review): the emitted code builds slices by `append` and
    exact-length copies, protobuf-go pre-sizes them (Marshal's buffer by a size pass,
    proto/encode.go:190; packed slices by a count of their varints; a singular bytes field by
    `append([]byte(nil), v...)`), so cap() and what two appends to a decoded slice share differ;
    lengths and contents do not.
  - only proto.Marshal and proto.Unmarshal with default options, on *T of the derived types;
    any other value panics ("not modelled"). proto.Size, Equal, Clone, Merge, MarshalOptions
    (Deterministic is moot: no maps; AllowPartial, which skips the required-field checks),
    protojson, prototext are not covered.

The evidence (untrusted, pbgen.py --help): the generator's differential test over random schemas
of the subset (`models/internal/pbgenrand`), the per-schema regression tests generated beside
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
            "sub", "j", "depth", "o", "pbMarshal", "pbUnmarshal", "interface", "nil", "uint64", "make",
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
    def __init__(self, name, num, kind, rep, cat, proto_name="", packed=False, pres=False, req=False,
                 utf8=True, oneof=None, wrapper=None, holder=None):
        self.name = name   # Go field name (of a oneof member: its wrapper's one field)
        self.num = num     # field number
        self.kind = kind   # the element kind: a scalar's name, or an enum or message type (alias.T)
        self.rep = rep     # repeated
        self.cat = cat     # "scalar", "enum" or "message"
        self.proto_name = proto_name
        self.packed = packed  # a repeated scalar or enum written packed (the descriptor's IsPacked)
        # explicit presence, singular, not a message and not in a oneof: a *T (a []byte for
        # bytes, present when non-nil)
        self.pres = pres
        self.req = req     # required (proto2)
        self.utf8 = utf8   # a string field whose UTF-8 protobuf-go checks (strs.EnforceUTF8)
        self.oneof = oneof      # the (non-synthetic) oneof's name, or None
        self.wrapper = wrapper  # a oneof member's wrapper type (alias.W)
        self.holder = holder    # a oneof member's holder field (Go name, in the message)

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
        """The Go type of the struct field (of a oneof member: of its wrapper's field)."""
        if self.rep:
            return "[]" + self.elem_go()
        if self.pres and self.kind != "bytes":
            return "*" + self.elem_go()
        return self.elem_go()

    def x(self, m="m"):
        """The Go expression of the field's value in message m (not for a oneof member)."""
        return f"{m}.{self.name}"


class Schema:
    """A schema dump (pbdesc's JSON), checked against the subset.

    names: the message types (Go references alias.T, sorted); m: name -> fields (by number, the
    oneofs' members included); plain: name -> the fields in no oneof (by number); oneofs: name ->
    [(holder Go field, oneof name, its members by number)] in declaration order; direct_req: the
    types with a required field; needs_init: the types whose Marshal and Unmarshal check required
    fields (protobuf-go's needsInitCheck: a required field reachable through message fields);
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
            if e["syntax"] not in ("proto2", "proto3"):
                why.append(f"{where}: an enum of a {e['syntax']} file (outside the subset: proto2 and "
                           "proto3 only)")
            # closed (proto2) enums are accepted: protobuf-go decodes them as open (the core's doc)
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
        self.plain = {}
        self.oneofs = {}
        self.full = {}
        first_member = {}  # (message, oneof) -> the number of its first declared member
        for fn, d in sorted(msgs.items()):
            where = f"message {fn} ({d['file']})"
            if d["syntax"] not in ("proto2", "proto3"):
                why.append(f"{where}: a {d['syntax']} file (outside the subset: proto2 and proto3 only)")
            if d["map_entry"]:
                why.append(f"{where}: a map entry (maps are outside the subset)")
            if d["message_set"]:
                why.append(f"{where}: the MessageSet wire format (outside the subset)")
            if d["extension_ranges"]:
                why.append(f"{where}: extension ranges (extensions are outside the subset)")
            if not d.get("go"):
                why.append(f"{where}: no registered Go type")
                continue
            for x in d["go_extra"]:
                why.append(f"{where}: Go field {x} is no descriptor field's nor a oneof's holder")
            for x in d["go_hidden"]:
                why.append(f"{where}: Go field {x} (presence or lazy state: not the open struct API)")
            if d["legacy_oneof_funcs"]:
                why.append(f"{where}: an XXX_OneofFuncs or XXX_OneofWrappers method (APIv1 oneofs)")
            decls = [o for o in d["oneof_decls"] if not o["synthetic"]]
            holder = {}
            for o in decls:
                if not o["go_field"] or o["go_kind"] != "interface":
                    why.append(f"{where}: oneof {o['name']}: no Go holder field of interface type")
                else:
                    holder[o["name"]] = o["go_field"]
            fields = []
            for f in d["fields"]:
                fx = self._field(fn, f, msgs, enums, enum_ref, msg_ref, holder, by_path, why)
                if fx is not None:
                    fields.append(fx)
            nums = [f["number"] for f in d["fields"]]
            if len(set(nums)) != len(nums):
                why.append(f"{where}: a field number twice")
            r = msg_ref[fn]
            for f in d["fields"]:
                if f["oneof"] and not f["synthetic_oneof"]:
                    first_member.setdefault((r, f["oneof"]), f["number"])
            self.m[r] = sorted(fields, key=lambda f: f.num)
            self.plain[r] = [f for f in self.m[r] if f.oneof is None]
            self.oneofs[r] = [(holder.get(o["name"]), o["name"], [f for f in self.m[r] if f.oneof == o["name"]])
                              for o in decls]
            self.full[r] = fn
        self.names = sorted(self.m)
        self.enums.sort()

        # required fields: the types that have one, and those that reach one (protobuf-go's
        # needsInitCheck, internal/impl/checkinit.go:121-160)
        self.direct_req = {n for n in self.names if any(f.req for f in self.m[n])}
        self.needs_init = set(self.direct_req)
        changed = True
        while changed:
            changed = False
            for n in self.names:
                if n not in self.needs_init and any(f.cat == "message" and f.kind in self.needs_init
                                                    for f in self.m[n]):
                    self.needs_init.add(n)
                    changed = True
        # where protobuf-go's own required-field checks are not what the emitted code checks:
        # (a) a type that needs them only through a cycle of two or more message types: the
        # cache of needsInitCheck (internal/impl/checkinit.go:121-160) keeps a wrong false for it,
        # depending on which type the program uses first; (b) a oneof member other than the
        # oneof's first declared one, of a type that needs them: Unmarshal's fast path consults
        # the isInit of the field's own coder (internal/impl/decode.go:189), which only the first
        # member's coder has (internal/impl/codec_field.go:83-118), so a missing required field
        # in it passes Unmarshal (and fails Marshal)
        succ = {n: {f.kind for f in self.m[n] if f.cat == "message"} for n in self.names}
        reach = {}
        for n in self.names:
            seen, todo = set(), list(succ[n])
            while todo:
                t = todo.pop()
                if t not in seen:
                    seen.add(t)
                    todo += succ.get(t, ())
            reach[n] = seen
        for n in sorted(self.needs_init - self.direct_req):
            if any(t != n and n in reach.get(t, ()) for t in reach[n]):
                why.append(f"message {self.full[n]}: reaches required fields only through a cycle of "
                           "message types (protobuf-go's needsInitCheck may cache false for it; outside "
                           "the subset)")
        for n in self.names:
            for _, on, mem in self.oneofs[n]:
                for f in mem:
                    if f.cat == "message" and f.kind in self.needs_init and f.num != first_member[(n, on)]:
                        why.append(f"field {self.full[n]}.{f.proto_name} (number {f.num}): a oneof member "
                                   f"(not the first of {on}) of a message type with required fields "
                                   "(protobuf-go's Unmarshal does not check them; outside the subset)")

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
    def _field(mfn, f, msgs, enums, enum_ref, msg_ref, holder, by_path, why):
        """The Field of descriptor field f of message mfn, or None (reasons added to why).
        holder: oneof name -> its Go holder field; by_path: Go import path -> alias."""
        where = f"field {mfn}.{f['name']} (number {f['number']})"
        n0 = len(why)
        kind, card = f["kind"], f["cardinality"]
        rep = card == "repeated"
        oneof = f["oneof"] if f["oneof"] and not f["synthetic_oneof"] else None
        if oneof is not None and oneof not in holder:
            why.append(f"{where}: in oneof {oneof}, which has no Go holder field")
        if oneof is not None and not f.get("go_wrapper"):
            why.append(f"{where}: in oneof {oneof}, with no registered wrapper type implementing its holder")
        if oneof is not None and (rep or card == "required"):
            why.append(f"{where}: a {card} field in oneof {oneof} (impossible)")
        if f["is_map"]:
            why.append(f"{where}: a map (outside the subset)")
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
        if f["packed"] and (not rep or kind in ("string", "bytes", "message", "group")):
            why.append(f"{where}: a packed {card} {kind} (impossible)")
        # explicit presence: a singular field that is not a message nor in a oneof, with
        # has_presence (proto2 optional and required, proto3 `optional`); rep fields never have it
        pres = not rep and kind != "message" and oneof is None and f["has_presence"]
        if rep and f["has_presence"]:
            why.append(f"{where}: a repeated field with presence (impossible)")
        if card == "required" and not f["has_presence"]:
            why.append(f"{where}: a required field without presence (impossible)")
        if (kind == "message" or oneof is not None) and not f["has_presence"] and not rep:
            why.append(f"{where}: a message or oneof field without presence (impossible)")
        if not f["go_field"]:
            why.append(f"{where}: no exported Go struct field with its number")
        if len(why) > n0:
            return None
        # the element and the Go type protoc-gen-go's open struct API gives it
        if kind == "enum":
            if f["enum"] not in enum_ref:
                why.append(f"{where}: enum {f['enum']} has no Go type")
                return None
            el, cat, want_el = enum_ref[f["enum"]], "enum", ("*" if pres else "")
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
            want = ("[]" if rep else "") + ("*" if pres and kind != "bytes" else "") + REFLECT_GO[kind]
        else:
            if not g:
                why.append(f"{where}: Go field {f['go_field']} of type {f['go_type']}, not a named type")
                return None
            want = ("[]" if rep else "") + want_el + f"{g['pkg_name']}.{g['name']}"
            exp = (msgs[f["message"]] if cat == "message" else enums[f["enum"]])["go"]
            if (exp["pkg"], exp["name"]) != (g["pkg"], g["name"]):
                why.append(f"{where}: Go field type {f['go_type']} is not the {cat}'s registered Go type")
                return None
        if f["go_type"] != want:
            why.append(f"{where}: Go field {f['go_field']} of type {f['go_type']}, expected {want}")
            return None
        wrapper = None
        if oneof is not None:
            w = f["go_wrapper"]
            if w["pkg"] not in by_path:
                why.append(f"{where}: wrapper type {w['pkg']}.{w['name']} of a package with no alias")
                return None
            wrapper = f"{by_path[w['pkg']]}.{w['name']}"
        return Field(f["go_field"], f["number"], el, rep, cat, f["name"], packed=f["packed"], pres=pres,
                     req=card == "required", utf8=(kind != "string" or f["enforce_utf8"]),
                     oneof=oneof, wrapper=wrapper, holder=holder.get(oneof))


# ---------------------------------------------------------------------------------------------
# The codec (pb_gen.go)

CODEC_DOC = """// The protobuf codec (registered with a model of google.golang.org/protobuf, proto.SetCodec):
// pbMarshal and pbUnmarshal for exactly the message types below, derived by models/protobuf/pbgen.py from
// their registered descriptors, over the wire format of models.lab/pbcodec. The trusted claim
// is the generator's (models/protobuf/pbgen_core.py's doc, field kind by field kind, against protobuf-go
// v1.36.12):
//
//   - pbMarshal(m), m a *T of a type below: real proto.Marshal(m)'s bytes (the fields in no
//     oneof in number order, then the oneofs' set members; proto3's zero values omitted, fields
//     with explicit presence written when set, a nil element of a repeated message field
//     written as an empty message; nil for a nil *T, an empty non-nil slice for an empty
//     message), or an error where the real one errs (a proto3 string field that is not UTF-8, a
//     required field not set).
//   - pbUnmarshal(b, m), m a non-nil *T of a type below: resets *m and decodes b into it as
//     real proto.Unmarshal does (merging repeated occurrences, the last member of a oneof
//     winning), or an error where the real one errs (malformed input, a field number 0 or above
//     2^29-1, invalid UTF-8 in a proto3 string field, messages nested deeper than 10000, a
//     required field missing). Unknown fields are checked and skipped (the real one keeps them
//     in the message: the model does not). A nil *T panics, as the real one does.
//   - Any other value (another type, a non-pointer, a nil interface) panics: outside the
//     subset.
//
// Only error-or-not is modeled, not the error values."""


def enc_scalar_lines(f, x):
    """Go statements appending element value x (of field f's element kind; not a message), its
    tag first."""
    w = f.wire()
    if f.kind == "string":
        chk = [f"if !pbcodec.ValidString({x}) {{", "\treturn b, false", "}"] if f.utf8 else []
        return chk + [f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
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


def enc_message_lines(f, x):
    """Go statements appending message value x (a *M, nil encoding as an empty message) as
    field f."""
    return [f"sub, ok := pbenc_{ident(f.kind)}(make([]byte, 0), {x})",
            "if !ok {", "\treturn b, false", "}",
            f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
            "b = pbcodec.AppendBytes(b, sub)"]


def ind(lines, k=1):
    return ["\t" * k + l for l in lines]


def gen_encoder(S, n):
    I = ident(n)
    out = [f"// pbenc_{I} appends the encoding of *m's fields (real proto.Marshal's: the fields in no",
           "// oneof in field-number order, then the oneofs in declaration order); false if a",
           "// UTF-8-checked string field is not UTF-8. A nil m encodes as an empty message.",
           f"func pbenc_{I}(b []byte, m *{n}) ([]byte, bool) {{",
           "\tif m == nil {", "\t\treturn b, true", "\t}"]
    body = []
    for f in S.plain[n]:
        x = f.x()
        if f.cat == "message":
            if f.rep:
                body += [f"for _, e := range {x} {{"] + ind(enc_message_lines(f, "e")) + ["}"]
            else:
                body += [f"if {x} != nil {{"] + ind(enc_message_lines(f, x)) + ["}"]
        elif f.pres:
            v = x if f.kind == "bytes" else f"*{x}"
            body += [f"if {x} != nil {{"] + ind(enc_scalar_lines(f, v)) + ["}"]
        elif not f.rep:
            body += [f"if {zero_test(f, x)} {{"] + ind(enc_scalar_lines(f, x)) + ["}"]
        elif not f.packed:
            body += [f"for _, e := range {x} {{"] + ind(enc_scalar_lines(f, "e")) + ["}"]
        else:
            body += [f"if len({x}) > 0 {{", "\tp := make([]byte, 0)", f"\tfor _, e := range {x} {{",
                     f"\t\tp = {append_value('p', f, 'e')}", "\t}",
                     f"\tb = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
                     "\tb = pbcodec.AppendBytes(b, p)", "}"]
    for h, _, mem in S.oneofs[n]:
        body.append(f"switch o := m.{h}.(type) {{")
        for f in mem:
            v = f"o.{f.name}"
            lines = enc_message_lines(f, v) if f.cat == "message" else enc_scalar_lines(f, v)
            body += [f"case *{f.wrapper}:", "\tif o != nil {"] + ind(lines, 2) + ["\t}"]
        body.append("}")
    out += ind(body) + ["\treturn b, true", "}", ""]
    return out


def dec_elem(f, v):
    """A Go expression: the Go value of numeric element wire value v (from Consume...)."""
    if f.cat == "enum":
        return f"{f.kind}(int32({v}))"
    return SCALARS[f.kind][3].format(v=v)


def consume_fn(f):
    return {"VarintType": "pbcodec.ConsumeVarint", "Fixed32Type": "pbcodec.ConsumeFixed32",
            "Fixed64Type": "pbcodec.ConsumeFixed64"}[f.wire()]


def store_lines(f, val):
    """Go statements storing the decoded element value val into singular field f (a plain
    field: replaced; explicit presence: through its pointer, allocated if nil, as protobuf-go's
    consume...Ptr; a oneof member: into its wrapper, reused if the oneof holds one of this
    member, else a new one, then set as the oneof's value)."""
    if f.oneof is not None:
        return [f"o, _ := m.{f.holder}.(*{f.wrapper})", "if o == nil {", f"\to = &{f.wrapper}{{}}", "}",
                f"o.{f.name} = {val}", f"m.{f.holder} = o"]
    x = f.x()
    if f.pres and f.kind != "bytes":
        return [f"if {x} == nil {{", f"\t{x} = new({f.elem_go()})", "}", f"*{x} = {val}"]
    return [f"{x} = {val}"]


def gen_decoder(S, n):
    I = ident(n)
    out = [f"// pbdec_{I} decodes b into *m, merging into what is there, as the real Unmarshal does;",
           "// depth is the nesting the real Unmarshal still allows (this message included); false",
           "// where the real Unmarshal errs (required fields aside: pbinit_ checks them).",
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
           "// wire type than its own (or than packed, for a repeated scalar), is skipped (unknown).",
           f"func pbdecField_{I}(b []byte, num uint64, typ uint64, m *{n}, depth uint64) (uint64, bool) {{"]
    body = []
    for f in S.m[n]:
        x = f.x()
        w = f.wire()
        if f.cat == "message":
            body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                     "\tv, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
            if f.rep:
                body += [f"\te := &{f.kind}{{}}",
                         f"\tif !pbdec_{ident(f.kind)}(v, e, depth-1) {{", "\t\treturn 0, false", "\t}",
                         f"\t{x} = append({x}, e)"]
            elif f.oneof is not None:
                y = f"o.{f.name}"
                body += [f"\to, _ := m.{f.holder}.(*{f.wrapper})", "\tif o == nil {", f"\t\to = &{f.wrapper}{{}}",
                         "\t}", f"\tif {y} == nil {{", f"\t\t{y} = &{f.kind}{{}}", "\t}",
                         f"\tif !pbdec_{ident(f.kind)}(v, {y}, depth-1) {{", "\t\treturn 0, false", "\t}",
                         f"\tm.{f.holder} = o"]
            else:
                body += [f"\tif {x} == nil {{", f"\t\t{x} = &{f.kind}{{}}", "\t}",
                         f"\tif !pbdec_{ident(f.kind)}(v, {x}, depth-1) {{", "\t\treturn 0, false", "\t}"]
            body += ["\treturn k, true", "}"]
        elif f.kind in ("string", "bytes"):
            body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                     "\tv, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
            if f.kind == "string":
                if f.utf8:
                    body += ["\tif !pbcodec.ValidUTF8(v) {", "\t\treturn 0, false", "\t}"]
                val = "string(v)"
            else:
                # a bytes field with presence (explicit, or a oneof member) or a repeated element
                # decodes an empty value to a non-nil empty slice; a proto3 one to nil
                val = "pbcodec.CopyBytes(v)" if (f.rep or f.pres or f.oneof is not None) else \
                    "pbcodec.CopyBytesOrNil(v)"
            body += ([f"\t{x} = append({x}, {val})"] if f.rep else ind(store_lines(f, val))) + \
                ["\treturn k, true", "}"]
        else:
            one = [f"v, k, ok := {consume_fn(f)}(b)", "if !ok {", "\treturn 0, false", "}"]
            one += [f"{x} = append({x}, {dec_elem(f, 'v')})"] if f.rep else store_lines(f, dec_elem(f, "v"))
            one += ["return k, true"]
            body += [f"if num == {f.num} && typ == pbcodec.{w} {{"] + ind(one) + ["}"]
            if f.rep:
                body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                         "\tp, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}",
                         "\tj := uint64(0)", "\tfor j < uint64(len(p)) {",
                         f"\t\tv, k2, ok2 := {consume_fn(f)}(p[j:])", "\t\tif !ok2 {", "\t\t\treturn 0, false", "\t\t}",
                         f"\t\t{x} = append({x}, {dec_elem(f, 'v')})",
                         "\t\tj = j + k2", "\t}", "\treturn k, true", "}"]
    body += ["return pbcodec.SkipField(num, typ, b)"]
    out += ind(body) + ["}", ""]
    return out


def gen_init(S, n):
    """pbinit_T, for a type in needs_init: protobuf-go's checkInitializedPointer
    (internal/impl/checkinit.go:26-95) on an open struct."""
    I = ident(n)
    out = [f"// pbinit_{I}: *m has every required field, and so do the messages it holds (singular,",
           "// repeated elements, nil ones included, and a oneof's), as the real Marshal and Unmarshal",
           "// check them; a nil m: the type has no required field of its own.",
           f"func pbinit_{I}(m *{n}) bool {{",
           "\tif m == nil {", f"\t\treturn {'false' if n in S.direct_req else 'true'}", "\t}"]
    body = []
    for f in S.plain[n]:
        x = f.x()
        sub = f.cat == "message" and f.kind in S.needs_init
        if f.req:
            body += [f"if {x} == nil {{", "\treturn false", "}"]
        if sub and f.rep:
            body += [f"for _, e := range {x} {{", f"\tif !pbinit_{ident(f.kind)}(e) {{", "\t\treturn false",
                     "\t}", "}"]
        elif sub:
            body += [f"if {x} != nil && !pbinit_{ident(f.kind)}({x}) {{", "\treturn false", "}"]
    for h, _, mem in S.oneofs[n]:
        mem = [f for f in mem if f.cat == "message" and f.kind in S.needs_init]
        if not mem:
            continue
        body.append(f"switch o := m.{h}.(type) {{")
        for f in mem:
            body += [f"case *{f.wrapper}:", f"\tif o != nil && !pbinit_{ident(f.kind)}(o.{f.name}) {{",
                     "\t\treturn false", "\t}"]
        body.append("}")
    out += ind(body) + ["\treturn true", "}", ""]
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
    req_err = "&pbcodec.Error{Msg: \"required field not set\"}"
    for n in S.names:
        body += [f"\tcase *{n}:", "\t\tif p == nil {"]
        if n in S.direct_req:
            body += [f"\t\t\treturn nil, {req_err}"]
        else:
            body += ["\t\t\treturn nil, nil"]
        body += ["\t\t}",
                 f"\t\tb, ok := pbenc_{ident(n)}(make([]byte, 0), p)", "\t\tif !ok {",
                 "\t\t\treturn nil, &pbcodec.Error{Msg: \"string field contains invalid UTF-8\"}", "\t\t}"]
        if n in S.needs_init:
            body += [f"\t\tif !pbinit_{ident(n)}(p) {{", f"\t\t\treturn nil, {req_err}", "\t\t}"]
        body += ["\t\treturn b, nil"]
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
                 "\t\t\treturn &pbcodec.Error{Msg: \"cannot parse invalid wire-format data\"}", "\t\t}"]
        if n in S.needs_init:
            body += [f"\t\tif !pbinit_{ident(n)}(p) {{", f"\t\t\treturn {req_err}", "\t\t}"]
        body += ["\t\treturn nil"]
    body += ["\t}", "\tpanic(\"protobuf model: unmarshaling into a value of a type the codec was not generated for\")",
             "}", ""]
    for n in S.names:
        body += gen_encoder(S, n)
        body += gen_decoder(S, n)
        if n in S.needs_init:
            body += gen_init(S, n)
    text = "\n".join(body)
    imps = used_imports(S, text, ["models.lab/pbcodec"])
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
