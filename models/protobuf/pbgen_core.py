"""pbgen's trusted core: a protobuf codec (plain Go code, per message type) from a schema dump.

This module is the trusted part of models/protobuf/pbgen.py (the decision of 2026-11-19, `notes/decisions.md`,
"Trusted generated code: the generator is the trusted artifact"). Nothing in Lean fixes
protobuf's wire format: a program's proof uses whatever `PbCodec` its generated code is proved to
meet, and its final statement does not mention it. What is trusted is that running the program
with `proto.Marshal`/`proto.Unmarshal` replaced by the code this module emits behaves as with the
real google.golang.org/protobuf v1.36.12, for every schema this module accepts: in its codec mode
a codec in a package of its own (pb_gen.go, registered with a model by proto.SetCodec), in its
pbmodel mode methods in each message's own package (pbmodel_gen.go, which the proto model,
models/protobuf-go/proto, dispatches to: THE SAME-PACKAGE METHODS below). Everything else
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
`XXX_OneofWrappers` method); a Go type that is not an APIv2 message or has its own codec methods
(`Marshal`, `Unmarshal`, `XXX_Marshal`, `XXX_Unmarshal`, `XXX_Size`: APIv1 and gogo types, which
protobuf-go runs through its legacy path); Go package aliases or generated function names that collide. And
two schemas where protobuf-go's own required-field checks are not what the descriptors say
(`models/internal/pbgenrand`'s TestProtobufQuirks shows both on protobuf-go; the review
`notes/axiom-review/pbgen.md`, "The proto2 and oneof extension"): a message type with no required field of
its own that reaches one and lies on a cycle of two or more message types, whether or not it also
reaches required fields outside the cycle (protobuf-go's needsInitCheck can cache a false for
such a type, depending on which type the program uses first: internal/impl/checkinit.go:137-170;
refusing every such type, not only those that reach required fields through the cycle alone, is
conservative);
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
    returns `Default_T_X` when the pointer is nil); no coder reads it (internal/impl reads a
    field's Default only in its reflection and getter paths, convert.go:95, 380,
    message_reflect_field.go:41, 53, legacy_message.go:535, and for a map entry's key,
    codec_map.go:44).
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
  - Unmarshal into a nil *T panics, a nil dereference (protobuf-go's generated Reset of a nil
    message panics so too, `*x = T{}`).

  Where the codec mode's claim stops (documented deviations, outside "behaves as protobuf-go"):
  - unknown fields (the codec mode only; the pbmodel mode keeps them, below): protobuf-go keeps
    them in the message (decode.go:226-229) and Marshal writes them back; the codec, in a package
    of its own, cannot reach the struct's unexported unknownFields, so it checks and drops them. A
    program that re-sends a message decoded from input carrying fields its schema does not know
    (a peer with a newer schema, or a corrupted input) behaves differently; between peers of the
    same schema none arise. (The codec mode stays for the dsverify kits that register it,
    proto.SetCodec, e.g. quepaxa, until they move to the pbmodel mode: #37.)
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
    any other value blocks forever (`select {}`: not modelled; never a panic, which a program
    could recover from and so observe a behavior protobuf-go does not have). proto.Size, Equal,
    Clone, Merge, MarshalOptions
    (Deterministic is moot: no maps; AllowPartial, which skips the required-field checks),
    protojson, prototext are not covered.

THE SAME-PACKAGE METHODS (the pbmodel mode, `pbgen.py --pbmodel`; #37 stage S3, decisions D1, D2
and the size cache's D-A): for each Go package of the closure, a file pbmodel_gen.go in that
package (build tag `goose || pbmodel`: the real build never compiles it; no init, no package
variable, no package-level function, only methods on the message types' pointer types, all named
PbModel*, which no other code may name: Schema refuses a type with such a method or field), over
pbcodec and sync/atomic (imported as pbmodelcodec, pbmodelatomic). The proto model
(models/protobuf-go/proto) calls them through an interface in place of protobuf-go's reflection.
The claim: each method is the internal/impl function of protobuf-go v1.36.12 it names, run on
this type: its result (bytes, sizes, nil-ness, the class of an error: Marshal's invalid UTF-8,
size mismatch or required field missing; Unmarshal's required field missing or another error)
and its effect on the message (fields, unknown fields, size caches) are the real one's, what
comes with an error included; not claimed:
the error values (*pbcodec.Error), slice capacities and which appends share an array (lengths and
contents are claimed). The encoding of each field kind is the codec mode's (above); what differs:
  - Schema refuses a message without protoc-gen-go's `sizeCache int32` and `unknownFields []byte`
    fields (the ones internal/impl/message.go:158-170 finds by those names; pbdesc reports them).
  - PbModelSize(cached) is sizePointer (internal/impl/encode.go:47-132): 0 for a nil message; under
    cached (MarshalInputFlags' UseCachedSize), a size cache above 0 gives it minus one (52-58,
    an atomic load) and nothing below is walked; otherwise the fields' sizes (the sizers of
    codec_gen.go: tag size plus value size; a packed field's tag, length and values, nothing if
    empty; a message field's tag, its size's varint and its size, by the field type's
    PbModelSize with the same cached, a nil element or oneof member as 0, codec_field.go:159-161,
    410-417) plus the unknown fields' length (113-117), stored into the size cache atomically, plus
    one, or 0 past math.MaxInt32-1 (118-130). So a stale cache below a level being recomputed
    gives a stale-derived size, stored into that level (the "stale-derived write").
  - PbModelAppend(b, cached) is marshalAppendPointer (encode.go:148-226): b for a nil message; the
    fields in the order of the codec mode; a message field (codec_field.go:163-173 singular,
    419-436 repeated) writes its tag, the field type's PbModelSize(cached) as the length, then
    the message's bytes, and if they are not that long returns nil and a size mismatch (the
    check skipped when the message's own append fails: that error and what was appended return);
    a UTF-8-checked string is appended, then checked: on failure what was appended returns with
    the error (codec_gen.go:5042-5050 and the Ptr, NoZero and Slice variants); then the unknown
    fields, as they are (220-224). The top level's cache is never read by the append: only a
    nested level's length prefix is (so a stale top-level cache changes only the capacity
    proto's size pass reserves).
  - PbModelDecode(b, depth) and PbModelDecodeField are unmarshalPointerEager (decode.go:124-245)
    as the codec mode's decoder, but an unknown field (a number the message does not have, or
    another wire type than the field's) is appended to the message's unknown fields: its tag
    re-encoded by AppendTag from the number and wire type read, then its value's bytes as
    ConsumeFieldValue delimits them (218-231); a nested message's unknown fields go into it.
    A packed record first grows the slice by the count of values it may hold (the bytes below
    0x80 of a varint record, the length over 4 or 8 of a fixed one; growInt32Slice etc.,
    internal/impl/pointer_unsafe.go:146-184: a new array, stored at once, so a nil slice becomes
    non-nil, even if the record then fails), then appends the values to a copy of the header,
    stored once the record parsed (consumeInt32Slice, codec_gen.go:741-777, and the 12 others).
    What a failed decode leaves in the message is therefore the real one's: every store happens
    where the real consumer's does (a string after its UTF-8 check, codec_gen.go:5053-5067; a
    singular message allocated before its decode, codec_field.go:183-186; a repeated message
    appended only after, 446-452; a oneof's wrapper set only after, 53-70).
  - PbModelUnmarshal(b) is proto.Unmarshal(b, m) (proto/decode.go:61-64, 90-136): the generated
    Reset's `*m = T{}` (reset.go:17-19; a nil m panics there, a nil dereference), the decode with
    depth 10000, the required-field check (decode.go:132-135, as the codec mode's).
  - PbModelIsInit is checkInitializedPointer (checkinit.go:26-95), as the codec mode's pbinit_
    (true for a type that reaches no required field).
  - PbModelMergeFrom(src) is mergePointer (internal/impl/merge.go:36-113): a nil m panics, a nil
    src merges nothing; per field, the merger of its coder (codec_tables.go's fieldCoder): an
    implicit-presence scalar copied when not zero (mergeInt32NoZero etc., merge_gen.go), bytes
    into a new non-nil slice when not empty (mergeBytesNoZero, merge.go:191-196: so an empty
    non-nil slice stays nil); an explicit-presence scalar into a new pointer when set
    (mergeInt32Ptr), bytes into a new non-nil slice when non-nil (mergeBytes, 187-189; the field is
    a pointer field, codec_message.go:136, so a nil one is skipped, merge.go:76);
    a repeated scalar or string appended when non-nil (mergeInt32Slice: an empty non-nil one adds
    nothing, so a fresh copy has nil), bytes elements each copied into a new non-nil slice, a nil
    one included (mergeBytesSlice, 198-203), message elements each merged into a new message, a
    nil one giving an empty one (mergeMessageSlice, 175-185); a singular message merged into the
    destination's, allocated if nil (mergeMessage, 159-173); a oneof's set member (a non-nil
    wrapper) into the destination's wrapper of that type or a new one set in place (the first
    member's merge, codec_field.go:98-109), by the member's coder chosen with presence, which
    copies unconditionally: a scalar copied, bytes into a new non-nil slice even when nil
    (mergeBytes), a message allocated and merged even when nil (so a wrapper holding a nil message
    copies to one holding an empty message); src's unknown fields appended when not empty
    (merge.go:106-112). The size cache is not merged.
  - PbModelClone is proto.Clone (proto/merge.go:41-60): the receiver itself if nil (a typed nil:
    Clone of an invalid message is that type's nil, `src.Type().Zero()`), else a new message
    merged from it; PbModelIsNil reports a nil receiver (emptyBytesForMessage, encode.go:141-146).
  - PbModelReset is proto.Reset (proto/reset.go:16-22): a message of protoc-gen-go has a Reset
    method and the build has the fast path (hasProtoMethods, proto_methods.go:16), so it calls the
    generated Reset, `*x = T{}` (e.g. types/known/emptypb/empty.pb.go:57-62; a nil x panics, a nil
    dereference), whose other store (the message state's MessageInfo) is not a field of the model.
  - PbModelMerge(src) is proto.Merge(m, src) (proto/merge.go:25-37) for src the source's
    PbModelSelf (the *T itself, promoted through an embedding as ProtoReflect is): a source of
    another type gives false and changes nothing (protobuf-go panics, a descriptor mismatch,
    merge.go:28-33: proto/model.go does not model it), else PbModelMergeFrom (mergeMessage calls
    the type's Merge method, internal/impl/merge.go:23-34: mergePointer).
  - proto.CheckInitialized (proto/checkinit.go:14-33) is PbModelIsInit through the model's
    composition: nil for a nil interface, else the type's CheckInitialized method,
    checkInitializedPointer (internal/impl/checkinit.go:15-23).
  A message type embedded in another struct (etcd embeds raftpb and etcdserverpb types) promotes
  these methods as it promotes ProtoReflect, so the model and protobuf-go act on the same
  embedded message.

The evidence (untrusted, pbgen.py --help): the generator's differential test over random schemas
of the subset (`models/internal/pbgenrand`, both modes), the per-schema regression tests
generated beside each codec (pb_gen_test.go) and in each package (pbmodel_gen_test.go: also the
bytes and message that come with an error, unknown fields, Size and Clone, and random
interleavings of real and generated operations on shared messages with changes, garbage caches and
shared sub-messages, comparing every level's size cache; a concurrent run under -race), the size
cache's characterisation (`models/internal/pbcachetest`) and its fixed cases on the generated
methods (`models/internal/pbgenrand/cache_test.go`), and the independent review
`notes/axiom-review/pbgen.md`.
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
            "sub", "j", "depth", "o", "new", "pbMarshal", "pbUnmarshal", "interface", "nil", "uint64", "make",
            "append", "panic", "string", "len", "true", "false", "error", "byte", "bool", "int32",
            "int64", "uint32",
            # the packages the generated test (pb_gen_test.go) imports
            "bytes", "math", "rand", "os", "reflect", "runtime", "strconv", "strings", "testing", "time", "proto",
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

    def __init__(self, dump, aliases=None, pbmodel=False):
        aliases = dict(aliases or {})
        why = []
        self.pbmodel = pbmodel
        self.pkg = {}   # name -> the Go import path of its package (messages and enums)
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
            self.pkg[enum_ref[fn]] = e["go"]["pkg"]

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
            if d["legacy_codec"]:
                why.append(f"{where}: not an APIv2 message, or with its own Marshal/Unmarshal methods "
                           "(APIv1 or gogo: protobuf-go's legacy path)")
            if d["legacy_oneof_funcs"]:
                why.append(f"{where}: an XXX_OneofFuncs or XXX_OneofWrappers method (APIv1 oneofs)")
            if pbmodel:
                # the same-package methods read and write the fields protobuf-go's struct reader
                # takes as the size cache and the unknown fields (internal/impl/message.go:158-170),
                # under protoc-gen-go's names, and must not collide with a method or field
                if d.get("go_size_cache") != "sizeCache int32":
                    why.append(f"{where}: no size cache field `sizeCache int32` (protoc-gen-go's; found "
                               f"{d.get('go_size_cache')!r})")
                if d.get("go_unknown_fields") != "unknownFields []uint8":
                    why.append(f"{where}: no unknown fields field `unknownFields []byte` (protoc-gen-go's; "
                               f"found {d.get('go_unknown_fields')!r})")
                for x in d.get("go_pbmodel_methods", []):
                    why.append(f"{where}: a method {x} of the generated methods' prefix PbModel")
                for f in d["fields"]:
                    if f["go_field"].startswith("PbModel"):
                        why.append(f"{where}: Go field {f['go_field']} of the generated methods' prefix PbModel")
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
            self.pkg[r] = d["go"]["pkg"]
        self.names = sorted(self.m)
        self.enums.sort()

        # required fields: the types that have one, and those that reach one (protobuf-go's
        # needsInitCheck, internal/impl/checkinit.go:126-170)
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
        # (a) a type with no required field of its own that reaches one and lies on a cycle of
        # two or more message types (conservatively, also when it reaches one outside the
        # cycle): the cache of needsInitCheck (internal/impl/checkinit.go:137-170) keeps a wrong false for it,
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
                why.append(f"message {self.full[n]}: no required field of its own, reaches one, and lies "
                           "on a cycle of two or more message types (protobuf-go's needsInitCheck may "
                           "cache false for it; outside the subset)")
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
//     in the message: the model does not). A nil *T panics, a nil dereference, as the real
//     one does.
//   - Any other value (another type, a non-pointer, a nil interface) blocks forever: outside
//     the subset, not modelled (models/README.md: a not-modelled point is stuck, never a panic
//     a program could recover from).
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
    body += ["\t}", "\t// MODEL: not modelled (stuck): marshaling a value of a type the codec was not generated for",
             "\tselect {}", "}", "",
             "// pbUnmarshal is the codec's Unmarshal.",
             "func pbUnmarshal(b []byte, m interface{}) error {",
             "\tswitch p := m.(type) {"]
    for n in S.names:
        body += [f"\tcase *{n}:",
                 "\t\t// a nil p panics here, a nil dereference, as protobuf-go's generated Reset does",
                 f"\t\t*p = {n}{{}}",
                 f"\t\tif !pbdec_{ident(n)}(b, p, pbcodec.DefaultRecursionLimit) {{",
                 "\t\t\treturn &pbcodec.Error{Msg: \"cannot parse invalid wire-format data\"}", "\t\t}"]
        if n in S.needs_init:
            body += [f"\t\tif !pbinit_{ident(n)}(p) {{", f"\t\t\treturn {req_err}", "\t\t}"]
        body += ["\t\treturn nil"]
    body += ["\t}", "\t// MODEL: not modelled (stuck): unmarshaling into a value of a type the codec was not generated for",
             "\tselect {}", "}", ""]
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


# ---------------------------------------------------------------------------------------------
# The same-package methods (pbmodel_gen.go; the core's doc, "THE SAME-PACKAGE METHODS")

PBMODEL_TAG = "//go:build goose || pbmodel"

# The errors the methods return (only their class is modelled: the core's doc).
ERR_UTF8 = '&pbcodec.Error{Msg: "string field contains invalid UTF-8"}'
ERR_REQ = '&pbcodec.Error{Msg: "required field not set"}'
ERR_PARSE = '&pbcodec.Error{Msg: "cannot parse invalid wire-format data"}'
ERR_MISMATCH = '&pbcodec.Error{Msg: "size mismatch"}'


def tag_size(f, wire=None):
    """The size of field f's tag (protowire.SizeTag; the coder's tagsize, codec_message.go:131)."""
    w = {"VarintType": 0, "Fixed64Type": 1, "BytesType": 2, "Fixed32Type": 5}[wire or f.wire()]
    v, n = f.num << 3 | w, 1
    while v >= 0x80:
        v >>= 7
        n += 1
    return n


class Local:
    """Type references as the package `path` sees them: its own types without their alias."""

    def __init__(self, S, path):
        self.own = {a for a, p in S.imports.items() if p == path}

    def __call__(self, ref):
        a, _, t = ref.partition(".")
        return t if a in self.own else ref


def pm_value_size(f, x):
    """A Go int expression: the size of numeric, string or bytes element x of f, without its tag
    (protowire.SizeVarint of the varint value, 4 or 8, or the length prefix and the bytes; the
    sizers of internal/impl/codec_gen.go)."""
    w = f.wire()
    if f.kind in ("string", "bytes"):
        return f"int(pbcodec.SizeVarint(uint64(len({x})))) + len({x})"
    if w == "VarintType":
        return f"int(pbcodec.SizeVarint({enc_expr(f, x)}))"
    return "4" if w == "Fixed32Type" else "8"


def pm_size_lines(S, f, x, always=False):
    """Go statements adding to n the size of field f's value x (a plain field, or with
    always=True a oneof member's value, written whatever it is)."""
    ts = tag_size(f)
    if f.cat == "message":
        one = lambda v: [f"k := {v}.PbModelSize(cached)", f"n = n + {ts} + int(pbcodec.SizeVarint(uint64(k))) + k"]
        if f.rep:
            return [f"for _, e := range {x} {{"] + ind(one("e")) + ["}"]
        if always:
            return one(x)
        return [f"if {x} != nil {{"] + ind(one(x)) + ["}"]
    if always:
        return [f"n = n + {ts} + {pm_value_size(f, x)}"]
    fixed = f.wire() in ("Fixed32Type", "Fixed64Type")
    if f.rep and f.packed and fixed:
        return [f"if len({x}) > 0 {{", f"\tc := {pm_value_size(f, '')} * len({x})",
                f"\tn = n + {tag_size(f, 'BytesType')} + int(pbcodec.SizeVarint(uint64(c))) + c", "}"]
    if f.rep and fixed:
        return [f"n = n + ({ts}+{pm_value_size(f, '')})*len({x})"]
    if f.rep and f.packed:
        return [f"if len({x}) > 0 {{", "\tc := 0", f"\tfor _, e := range {x} {{",
                f"\t\tc = c + {pm_value_size(f, 'e')}", "\t}",
                f"\tn = n + {tag_size(f, 'BytesType')} + int(pbcodec.SizeVarint(uint64(c))) + c", "}"]
    if f.rep:
        return [f"for _, e := range {x} {{", f"\tn = n + {ts} + {pm_value_size(f, 'e')}", "}"]
    if f.pres:
        v = x if f.kind == "bytes" else f"*{x}"
        return [f"if {x} != nil {{", f"\tn = n + {ts} + {pm_value_size(f, v)}", "}"]
    return [f"if {zero_test(f, x)} {{", f"\tn = n + {ts} + {pm_value_size(f, x)}", "}"]


def pm_append_scalar(f, x):
    """Go statements appending element x of f (not a message), its tag first; a UTF-8-checked
    string is appended before it is checked, and the error returns what was appended (the
    ValidateUTF8 appenders, codec_gen.go:5042-5050, 5107-5118, 5170-5178, 5250-5260)."""
    if f.kind == "string":
        out = [f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)", f"b = pbcodec.AppendString(b, {x})"]
        if f.utf8:
            out += [f"if !pbcodec.ValidString({x}) {{", f"\treturn b, {ERR_UTF8}", "}"]
        return out
    if f.kind == "bytes":
        return [f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)", f"b = pbcodec.AppendBytes(b, {x})"]
    return [f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.{f.wire()})", f"b = {append_value('b', f, x)}"]


def pm_append_message(f, v):
    """Go statements appending message v (a *M; nil: an empty one) as field f: tag, the size the
    size pass gives (the size cache under `cached`), the message, then the check that the
    message's bytes have that length (appendMessageInfo, internal/impl/codec_field.go:163-173;
    appendMessageSliceInfo, 419-436: a mismatch returns nil, an error returns what was appended)."""
    return [f"k := {v}.PbModelSize(cached)",
            f"b = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
            "b = pbcodec.AppendVarint(b, uint64(k))",
            "before := len(b)",
            f"b2, err := {v}.PbModelAppend(b, cached)",
            "if err != nil {", "\treturn b2, err", "}",
            "if len(b2)-before != k {", f"\treturn nil, {ERR_MISMATCH}", "}",
            "b = b2"]


def pm_size(S, n, L):
    T = L(n)
    out = [f"// PbModelSize is the size of *m's encoding, as protobuf-go's sizePointer",
           "// (internal/impl/encode.go:47-132): 0 for a nil m; under cached, the size cache minus one",
           "// if the cache is above 0 (encode.go:52-58); otherwise the fields' sizes (a message field's",
           "// by its own PbModelSize, with the same cached) and the unknown fields', stored into the",
           "// size cache, atomically, plus one (0 past math.MaxInt32-1: encode.go:118-130).",
           f"func (m *{T}) PbModelSize(cached bool) int {{",
           "\tif m == nil {", "\t\treturn 0", "\t}",
           "\tif cached {", "\t\tc := atomic.LoadInt32(&m.sizeCache)", "\t\tif c > 0 {", "\t\t\treturn int(c - 1)",
           "\t\t}", "\t}", "\tn := 0"]
    body = []
    for f in S.plain[n]:
        body += pm_size_lines(S, f, f.x())
    for h, _, mem in S.oneofs[n]:
        body.append(f"switch o := m.{h}.(type) {{")
        for f in mem:
            body += [f"case *{L(f.wrapper)}:", "\tif o != nil {"] + ind(pm_size_lines(S, f, f"o.{f.name}", True), 2) + ["\t}"]
        body.append("}")
    body += ["n = n + len(m.unknownFields)",
             "if n > 2147483646 {", "\tatomic.StoreInt32(&m.sizeCache, 0)", "} else {",
             "\tatomic.StoreInt32(&m.sizeCache, int32(n+1))", "}", "return n"]
    return out + ind(body) + ["}", ""]


def pm_append(S, n, L):
    T = L(n)
    out = [f"// PbModelAppend appends *m's encoding to b, as protobuf-go's marshalAppendPointer",
           "// (internal/impl/encode.go:148-226): nothing for a nil m; the fields in no oneof in number",
           "// order, then the oneofs in declaration order (codec_message.go:158, 177-184), then the",
           "// unknown fields as they are (encode.go:220-224). A message field's length prefix is its",
           "// PbModelSize(cached); its bytes must have that length (else nil and a size mismatch). A",
           "// UTF-8-checked string that is not UTF-8: what was appended, with it, and an error.",
           f"func (m *{T}) PbModelAppend(b []byte, cached bool) ([]byte, error) {{",
           "\tif m == nil {", "\t\treturn b, nil", "\t}"]
    body = []
    for f in S.plain[n]:
        x = f.x()
        if f.cat == "message":
            if f.rep:
                body += [f"for _, e := range {x} {{"] + ind(pm_append_message(f, "e")) + ["}"]
            else:
                body += [f"if {x} != nil {{"] + ind(pm_append_message(f, x)) + ["}"]
        elif f.pres:
            v = x if f.kind == "bytes" else f"*{x}"
            body += [f"if {x} != nil {{"] + ind(pm_append_scalar(f, v)) + ["}"]
        elif not f.rep:
            body += [f"if {zero_test(f, x)} {{"] + ind(pm_append_scalar(f, x)) + ["}"]
        elif not f.packed:
            body += [f"for _, e := range {x} {{"] + ind(pm_append_scalar(f, "e")) + ["}"]
        else:
            body += [f"if len({x}) > 0 {{", "\tp := make([]byte, 0)", f"\tfor _, e := range {x} {{",
                     f"\t\tp = {append_value('p', f, 'e')}", "\t}",
                     f"\tb = pbcodec.AppendTag(b, {f.num}, pbcodec.BytesType)",
                     "\tb = pbcodec.AppendBytes(b, p)", "}"]
    for h, _, mem in S.oneofs[n]:
        body.append(f"switch o := m.{h}.(type) {{")
        for f in mem:
            v = f"o.{f.name}"
            lines = pm_append_message(f, v) if f.cat == "message" else pm_append_scalar(f, v)
            body += [f"case *{L(f.wrapper)}:", "\tif o != nil {"] + ind(lines, 2) + ["\t}"]
        body.append("}")
    body += ["b = append(b, m.unknownFields...)", "return b, nil"]
    return out + ind(body) + ["}", ""]


def pm_decode(S, n, L):
    T = L(n)
    out = [f"// PbModelDecode decodes b into *m, merging into what is there, as protobuf-go's",
           "// unmarshalPointerEager (internal/impl/decode.go:124-245); depth is the nesting still",
           "// allowed (this message included: decode.go:105); false where it errs (required fields",
           "// aside: PbModelIsInit checks them).",
           f"func (m *{T}) PbModelDecode(b []byte, depth uint64) bool {{",
           "\tif depth == 0 {", "\t\treturn false", "\t}",
           "\ti := uint64(0)",
           "\tfor i < uint64(len(b)) {",
           "\t\tnum, typ, n, ok := pbcodec.ConsumeFieldTag(b[i:])",
           "\t\tif !ok {", "\t\t\treturn false", "\t\t}",
           "\t\ti = i + n",
           "\t\tif typ == pbcodec.EndGroupType {", "\t\t\treturn false", "\t\t}",
           "\t\tk, ok2 := m.PbModelDecodeField(b[i:], num, typ, depth)",
           "\t\tif !ok2 {", "\t\t\treturn false", "\t\t}",
           "\t\ti = i + k",
           "\t}",
           "\treturn true",
           "}", "",
           f"// PbModelDecodeField decodes the value of field num (wire type typ) at the start of b into",
           "// *m: the length of the value, or false. A field *m does not have, or one with another wire",
           "// type than its own (or than packed, for a repeated scalar), is unknown: skipped as",
           "// protowire.ConsumeFieldValue skips it and kept, its tag re-encoded, in *m's unknown fields",
           "// (decode.go:218-231).",
           f"func (m *{T}) PbModelDecodeField(b []byte, num uint64, typ uint64, depth uint64) (uint64, bool) {{"]
    body = []
    for f in S.m[n]:
        x = f.x()
        w = f.wire()
        sub = L(f.kind)
        if f.cat == "message":
            body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                     "\tv, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
            if f.rep:
                body += [f"\te := &{sub}{{}}",
                         "\tif !e.PbModelDecode(v, depth-1) {", "\t\treturn 0, false", "\t}",
                         f"\t{x} = append({x}, e)"]
            elif f.oneof is not None:
                y = f"o.{f.name}"
                body += [f"\to, _ := m.{f.holder}.(*{L(f.wrapper)})", "\tif o == nil {",
                         f"\t\to = &{L(f.wrapper)}{{}}", "\t}", f"\tif {y} == nil {{", f"\t\t{y} = &{sub}{{}}", "\t}",
                         f"\tif !{y}.PbModelDecode(v, depth-1) {{", "\t\treturn 0, false", "\t}",
                         f"\tm.{f.holder} = o"]
            else:
                body += [f"\tif {x} == nil {{", f"\t\t{x} = &{sub}{{}}", "\t}",
                         f"\tif !{x}.PbModelDecode(v, depth-1) {{", "\t\treturn 0, false", "\t}"]
            body += ["\treturn k, true", "}"]
        elif f.kind in ("string", "bytes"):
            body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                     "\tv, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
            if f.kind == "string":
                if f.utf8:
                    body += ["\tif !pbcodec.ValidUTF8(v) {", "\t\treturn 0, false", "\t}"]
                val = "string(v)"
            else:
                val = "pbcodec.CopyBytes(v)" if (f.rep or f.pres or f.oneof is not None) else \
                    "pbcodec.CopyBytesOrNil(v)"
            st = [f"\t{x} = append({x}, {val})"] if f.rep else ind(store_lines(f, val))
            body += [l.replace(f"*{f.wrapper}", f"*{L(f.wrapper)}").replace(f"&{f.wrapper}{{", f"&{L(f.wrapper)}{{")
                     if f.wrapper else l for l in st] + ["\treturn k, true", "}"]
        else:
            el = dec_elem(f, "v").replace(f.kind + "(", L(f.kind) + "(") if f.cat == "enum" else dec_elem(f, "v")
            one = [f"v, k, ok := {consume_fn(f)}(b)", "if !ok {", "\treturn 0, false", "}"]
            st = [f"{x} = append({x}, {el})"] if f.rep else store_lines(f, el)
            if f.wrapper:
                st = [l.replace(f"*{f.wrapper}", f"*{L(f.wrapper)}").replace(f"&{f.wrapper}{{", f"&{L(f.wrapper)}{{")
                      for l in st]
            if f.pres and f.cat == "enum":
                st = [l.replace(f"new({f.kind})", f"new({L(f.kind)})") for l in st]
            one += st + ["return k, true"]
            body += [f"if num == {f.num} && typ == pbcodec.{w} {{"] + ind(one) + ["}"]
            if f.rep:
                # packed: the slice first grown by the count of values the record may hold (the
                # bytes below 0x80 of a varint record, its length over 4 or 8 for a fixed one),
                # its elements copied into a new array (stored even if the record then fails to
                # parse); then the values appended to a copy of its header, stored once the record
                # parsed (consumeInt32Slice, codec_gen.go:741-777, consumeFixed32Slice, 3528-3551,
                # and the 11 others alike; growInt32Slice, internal/impl/pointer_unsafe.go:154-160)
                if f.wire() == "VarintType":
                    count = ["\tcount := 0", "\tfor _, c := range p {", "\t\tif c < 0x80 {",
                             "\t\t\tcount = count + 1", "\t\t}", "\t}"]
                else:
                    count = [f"\tcount := len(p) / {4 if f.wire() == 'Fixed32Type' else 8}"]
                body += [f"if num == {f.num} && typ == pbcodec.BytesType {{",
                         "\tp, k, ok := pbcodec.ConsumeBytes(b)", "\tif !ok {", "\t\treturn 0, false", "\t}"]
                body += count + ["\tif count > 0 {", f"\t\tg := make([]{L(f.elem_go())}, len({x}), len({x})+count)",
                                 f"\t\tcopy(g, {x})", f"\t\t{x} = g", "\t}"]
                body += [f"\ts := {x}",
                         "\tj := uint64(0)", "\tfor j < uint64(len(p)) {",
                         f"\t\tv, k2, ok2 := {consume_fn(f)}(p[j:])", "\t\tif !ok2 {", "\t\t\treturn 0, false", "\t\t}",
                         f"\t\ts = append(s, {el})",
                         "\t\tj = j + k2", "\t}", f"\t{x} = s", "\treturn k, true", "}"]
    body += ["k, ok := pbcodec.SkipField(num, typ, b)", "if !ok {", "\treturn 0, false", "}",
             "m.unknownFields = pbcodec.AppendTag(m.unknownFields, num, typ)",
             "m.unknownFields = append(m.unknownFields, b[:k]...)",
             "return k, true"]
    return out + ind(body) + ["}", ""]


def pm_init(S, n, L):
    T = L(n)
    out = [f"// PbModelIsInit: *m has every required field, and so do the messages it holds (singular,",
           "// repeated elements, nil ones included, and a oneof's), as protobuf-go's",
           "// checkInitializedPointer (internal/impl/checkinit.go:26-95) checks them; a nil m: the type",
           "// has no required field of its own (checkinit.go:30-37).",
           f"func (m *{T}) PbModelIsInit() bool {{"]
    if n not in S.needs_init:
        return out + ["\treturn true", "}", ""]
    out += ["\tif m == nil {", f"\t\treturn {'false' if n in S.direct_req else 'true'}", "\t}"]
    body = []
    for f in S.plain[n]:
        x = f.x()
        sub = f.cat == "message" and f.kind in S.needs_init
        if f.req:
            body += [f"if {x} == nil {{", "\treturn false", "}"]
        if sub and f.rep:
            body += [f"for _, e := range {x} {{", "\tif !e.PbModelIsInit() {", "\t\treturn false", "\t}", "}"]
        elif sub:
            body += [f"if {x} != nil && !{x}.PbModelIsInit() {{", "\treturn false", "}"]
    for h, _, mem in S.oneofs[n]:
        mem = [f for f in mem if f.cat == "message" and f.kind in S.needs_init]
        if not mem:
            continue
        body.append(f"switch o := m.{h}.(type) {{")
        for f in mem:
            body += [f"case *{L(f.wrapper)}:", f"\tif o != nil && !o.{f.name}.PbModelIsInit() {{",
                     "\t\treturn false", "\t}"]
        body.append("}")
    return out + ind(body) + ["\treturn true", "}", ""]


def pm_merge_value(f, d, s):
    """Go statements merging oneof member f's value s into d (the member's own coder, chosen
    with presence: mergeInt32 etc. copy, mergeBytes copies into a non-nil slice,
    internal/impl/merge.go:187-189, mergeMessage allocates and merges, merge.go:159-173)."""
    if f.cat == "message":
        return [f"if {d} == nil {{", f"\t{d} = &{f.kind}{{}}", "}", f"{d}.PbModelMergeFrom({s})"]
    if f.kind == "bytes":
        return [f"{d} = append([]byte{{}}, {s}...)"]
    return [f"{d} = {s}"]


def pm_merge(S, n, L):
    T = L(n)
    out = [f"// PbModelMergeFrom merges *src into *m, as protobuf-go's mergePointer",
           "// (internal/impl/merge.go:36-113, the field mergers of merge.go and merge_gen.go): a nil",
           "// m panics, a nil src changes nothing; a set scalar or bytes field is copied (bytes into a",
           "// new non-nil slice), a repeated field appended to (each bytes element copied, each message",
           "// element, a nil one included, merged into a new message), a message field merged into",
           "// (allocated if nil), a oneof's set member copied into a new wrapper (unless m's oneof holds",
           "// one of its type: then into that), src's unknown fields appended to m's.",
           f"func (m *{T}) PbModelMergeFrom(src *{T}) {{",
           "\tif m == nil {", "\t\tpanic(\"invalid value: merging into nil message\")", "\t}",
           "\tif src == nil {", "\t\treturn", "\t}"]
    body = []
    for f in S.plain[n]:
        x, y = f.x(), f.x("src")
        sub = L(f.kind)
        if f.cat == "message":
            if f.rep:
                body += [f"for _, e := range {y} {{", f"\tc := &{sub}{{}}", "\tc.PbModelMergeFrom(e)",
                         f"\t{x} = append({x}, c)", "}"]
            else:
                body += [f"if {y} != nil {{", f"\tif {x} == nil {{", f"\t\t{x} = &{sub}{{}}", "\t}",
                         f"\t{x}.PbModelMergeFrom({y})", "}"]
        elif f.rep:
            if f.kind == "bytes":
                body += [f"for _, e := range {y} {{", f"\t{x} = append({x}, append([]byte{{}}, e...))", "}"]
            else:
                body += [f"if {y} != nil {{", f"\t{x} = append({x}, {y}...)", "}"]
        elif f.pres:
            if f.kind == "bytes":
                body += [f"if {y} != nil {{", f"\t{x} = append([]byte{{}}, {y}...)", "}"]
            else:
                body += [f"if {y} != nil {{", f"\tv := *{y}", f"\t{x} = &v", "}"]
        elif f.kind == "bytes":
            body += [f"if len({y}) > 0 {{", f"\t{x} = append([]byte{{}}, {y}...)", "}"]
        else:
            body += [f"if {zero_test(f, y)} {{", f"\t{x} = {y}", "}"]
    for h, _, mem in S.oneofs[n]:
        body.append(f"switch o := src.{h}.(type) {{")
        for f in mem:
            W = L(f.wrapper)
            mv = pm_merge_value(f, f"d.{f.name}", f"o.{f.name}")
            if f.cat == "message":
                mv = [l.replace(f"&{f.kind}{{", f"&{L(f.kind)}{{") for l in mv]
            body += [f"case *{W}:", "\tif o != nil {", f"\t\td, _ := m.{h}.(*{W})", "\t\tif d == nil {",
                     f"\t\t\td = &{W}{{}}", f"\t\t\tm.{h} = d", "\t\t}"] + ind(mv, 2) + ["\t}"]
        body.append("}")
    body += ["if len(src.unknownFields) > 0 {", "\tm.unknownFields = append(m.unknownFields, src.unknownFields...)", "}"]
    return out + ind(body) + ["}", ""]


def pm_entry(S, n, L):
    T = L(n)
    out = [f"// PbModelUnmarshal is proto.Unmarshal(b, m): *m reset (the generated Reset, `*m = {T}{{}}`,",
           "// a nil m panicking: proto/decode.go:95, reset.go:17-19), b decoded into it with the",
           "// recursion limit 10000 (proto/decode.go:62), then its required fields checked",
           "// (proto/decode.go:132-135).",
           f"func (m *{T}) PbModelUnmarshal(b []byte) error {{",
           f"\t*m = {T}{{}}",
           "\tif !m.PbModelDecode(b, pbcodec.DefaultRecursionLimit) {", f"\t\treturn {ERR_PARSE}", "\t}"]
    if n in S.needs_init:
        out += ["\tif !m.PbModelIsInit() {", f"\t\treturn {ERR_REQ}", "\t}"]
    out += ["\treturn nil", "}", "",
            f"// PbModelClone is proto.Clone(m) (proto/merge.go:41-60): m itself if nil (a typed nil),",
            "// else a new message with *m merged into it (the size cache not copied).",
            f"func (m *{T}) PbModelClone() interface{{}} {{",
            "\tif m == nil {", "\t\treturn m", "\t}",
            f"\tc := &{T}{{}}", "\tc.PbModelMergeFrom(m)", "\treturn c", "}", "",
            "// PbModelIsNil: m is nil (proto.Marshal's emptyBytesForMessage, proto/encode.go:141-146:",
            "// a nil *T is not a valid message).",
            f"func (m *{T}) PbModelIsNil() bool {{", "\treturn m == nil", "}", "",
            f"// PbModelReset is proto.Reset(m) (proto/reset.go:16-22): protoc-gen-go's generated Reset,",
            f"// `*m = {T}{{}}` (a nil m panicking, a nil dereference), the size cache and unknown fields",
            "// included; what it stores besides (the message state's MessageInfo, internal/impl) is not",
            "// a field of the model.",
            f"func (m *{T}) PbModelReset() {{", f"\t*m = {T}{{}}", "}", "",
            "// PbModelSelf: m, as proto.Merge's source (a type embedding this one promotes it, as it",
            "// promotes ProtoReflect: the model then merges from the embedded message, as protobuf-go).",
            f"func (m *{T}) PbModelSelf() interface{{}} {{", "\treturn m", "}", "",
            "// PbModelMerge is proto.Merge(m, src) (proto/merge.go:25-37, then mergeMessage's",
            "// internal/impl merge, merge.go:23-34) for src another message's PbModelSelf: false, and",
            f"// nothing changed, if src is not a *{T} (protobuf-go panics there, a descriptor mismatch;",
            f"// the model does not model it), else m.PbModelMergeFrom(src) (a nil m panics, a nil src",
            "// changes nothing).",
            f"func (m *{T}) PbModelMerge(src interface{{}}) bool {{",
            f"\to, ok := src.(*{T})", "\tif !ok {", "\t\treturn false", "\t}",
            "\tm.PbModelMergeFrom(o)", "\treturn true", "}", ""]
    return out


PBMODEL_DOC = """// The protobuf model's methods (models/protobuf-go/proto calls them in place of protobuf-go's
// reflection: proto.Marshal, Unmarshal, Size, Clone, Merge, Reset, CheckInitialized,
// MarshalOptions), for the message types of
// this package below, derived by models/protobuf/pbgen.py (its pbmodel mode) from their
// registered descriptors, over the wire format of models.lab/pbcodec. The trusted claim is the
// generator's (models/protobuf/pbgen_core.py's doc, "THE SAME-PACKAGE METHODS", against
// protobuf-go v1.36.12): each method is protobuf-go's internal/impl function it names, on this
// type, bytes, values, unknown fields and size caches included; only the class of an error is
// modelled, not its value. Built only for the model (tags goose, pbmodel): the real build never
// sees these methods. No init, no package variable; methods only, all named PbModel*."""


def pbmodel_go(S, path, header, go_name):
    """pbmodel_gen.go for Go package `path`: the methods of its message types in S."""
    L = Local(S, path)
    names = [n for n in S.names if S.pkg[n] == path]
    body = [PBMODEL_DOC, ""]
    for n in names:
        body += [f"// --- {S.full[n]}", ""]
        body += pm_size(S, n, L) + pm_append(S, n, L) + pm_decode(S, n, L) + pm_init(S, n, L)
        body += pm_merge(S, n, L) + pm_entry(S, n, L)
    # the two imports under names no package-level identifier of a message package is expected to
    # have (the gate on the forks checks that nothing but generated code names the prefix)
    text = re.sub(r"\batomic\.(?=[A-Z])", "pbmodelatomic.",
                  re.sub(r"\bpbcodec\.(?=[A-Z])", "pbmodelcodec.", "\n".join(body)))
    code = "\n".join(l for l in body if not l.lstrip().startswith("//"))
    imps = [l for l in used_imports(S, code) if f'"{path}"' not in l]
    imps = sorted(imps + ['\tpbmodelcodec "models.lab/pbcodec"', '\tpbmodelatomic "sync/atomic"'],
                  key=lambda l: l.split('"')[1])
    return (header + PBMODEL_TAG + "\n\n" + f"package {go_name}\n\nimport (\n" + "\n".join(imps) +
            "\n)\n\n" + text)
