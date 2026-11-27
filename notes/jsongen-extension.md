# jsongen's subset extended: embedded structs, pointers, JSON methods (design, 2026-11-23)

Proving session 2 (#18), JSON track handed over on #24 (upamanyus-agent's split, item 1; kaashoek's vr
requirement). Branch `ps2-jsongen/2026-11-23`. A change to a trusted generator (`models/json/jsongen_core.py`
and `models/jsondesc`, trusted with it): this note is the design, written before the code, for
Upamanyu's review (as pbgen's proto2/oneof extension, `notes/decisions.md` "pbgen's subset extended to
proto2 and oneofs", `notes/axiom-review/pbgen.md`). Nothing lands without that review.

**Why.** jsongen refuses every etcd type the membership axioms need (`/shared/tmp/ps2/json/triage.md`):
`membership.Member` and `ConfigChangeContext` (embedded structs), `raftpb.ConfState` (`AutoLeave *bool`),
`cluster_util`'s `[]*membership.Member` (pointer elements), and go-vsr's `log.Logs` (its own
`MarshalJSON`/`UnmarshalJSON`), so the vr kit has no codec (`RegisterJSON` empty).

**The claim does not change.** For every set of types the core accepts, the emitted code behaves as Go
1.27.3's default-build encoding/json (`jsonv2.Marshal/Unmarshal(…, DefaultOptionsV1())`), with the same
documented deviations (error values: only error-or-not; contents after an error; slice capacities). Every
rule below is cited, in the core's doc, to `$GOROOT/src/encoding/json/` of go1.27.3 (`etc/goose.py`'s
`GO_TOOLCHAIN`); line numbers are filled in with the code.

## 1. Embedded struct fields

Go: `v2/fields.go` `makeStructFields` (breadth-first walk, dominance), `parseFieldOptions`,
`arshal_default.go` `makeStructArshaler` (marshal: `fieldByIndex(…, false)`, a nil embedded pointer skips
the field; unmarshal: `fieldByIndex(…, true)` allocates through an exported nil embedded pointer, and records
`errNilField` for an unsettable one), `indirect`. With `ReportErrorsWithLegacySemantics` every error of
`makeStructFields` is ignored (`errInit`), so the walk's result is what decides.

The core reproduces `makeStructFields` itself (in Python over the dump), not v1's `typeFields`:

- An embedded field without a JSON name (no tag, or a tag whose name part is empty) whose type is a struct
  or a pointer to a struct (not a named pointer: `indirectType`) is flattened: its type is queued with the
  index path; a type already seen is queued again but its own embedded fields are not followed
  (`visitChildren = !seen[tf]`). An embedded field with a JSON name is an ordinary field.
- An embedded field of a non-struct type is an ordinary field named by its Go name if exported; ignored if
  not (`handleField`'s "not exported" error, ignored).
- Dominance, exactly: fields sorted by (name, depth, untagged-after-tagged), the first of each name kept iff
  it is alone, or shallower than the second, or tagged where the second is not; all of that name dropped
  otherwise (silently, as Go). Output order: depth-first by index path; the case-insensitive fallback's
  precedence: breadth-first order (`byFoldedName`, sorted by id), then `strings.EqualFold` (v1's
  `MatchCaseSensitiveDelimiter`). This also replaces two refusals of today: two fields of one struct with
  the same JSON name (Go drops both, or keeps the tagged one) and names equal ignoring case (Go's
  breadth-first precedence) are now reproduced instead of refused.
- Encoding: a field reached through a nil embedded pointer is skipped; embedded fields add no nesting.
  Decoding: an exported nil embedded pointer on a member's path is allocated (`new(E)`) before the value is
  decoded, also when the value then fails.
- The emitted code names a promoted field by its path: `v.E.X` through exported embedded fields; through an
  unexported embedded struct (`struct{ inner }`, whose exported fields Go promotes, `fields.go`
  parseFieldOptions' comment on go.dev/issue/21357) it relies on Go's selector promotion (`v.X`): the core
  checks, from the dump, that `X` is unique at the shallowest depth it occurs in the embedding tree and is no
  method of the type, so the selector denotes that field (else refused).

Refused: an unexported embedded *pointer* on the path of a field the codec would use (its nil-ness cannot be
tested, nor the pointer allocated, from another package; Go records `errNilField`); an embedded field whose
type has any of encoding/json's methods (`handleEmbed`'s "must not implement marshal or unmarshal methods";
the outer type also gets them by promotion, below); tag options on an embedded field without a name
(`handleEmbed` drops them with an ignored error; refused as almost certainly a mistake); an embedded map or
`json.RawMessage` reached as an embedded fallback (only with the `inline`/`embed` option: refused as today).

## 2. Pointer fields and elements

Go: `arshal_default.go` `makePointerArshaler`; `isLegacyEmpty` (omitempty: nil); `marshalEncode` (root).

Accepted: `*T` as a field, slice element, or pointer reached from a root, for every accepted non-pointer,
non-interface `T` (basic, named basic, struct, slice, `json.RawMessage`, a type with methods). Encoding: nil
is `null`, else `T`'s encoding, the pointee addressable (matters for pointer-receiver `MarshalJSON`, §3).
Decoding: `null` sets the pointer to nil (also under v1's merge semantics: `va.SetZero()`); any other value
allocates if nil (`reflect.New`, before decoding, so a failed value leaves a new zero pointee) and decodes
into the pointee (merging into an existing one). `omitempty`: omitted iff nil.

Refused: pointers to pointers, named pointer types, pointers to interfaces; the `string` option on a pointer
field (forwarded to the pointee, with the `"null"` special case of `makePointerArshaler`: not reproduced);
a pointer type as a root (as today: name `T`, the codec covers `T` and `*T`; `**T` in `Unmarshal` is now
covered when `*T` is in the closure).

## 3. A type's own `MarshalJSON`/`UnmarshalJSON`

Go: `v2/arshal_methods.go` `makeMethodArshaler`, `implements`; `CallMethodsWithLegacySemantics`
(v2_options.go); addressability: `arshal.go` `marshalEncode` (a non-pointer root is copied: `forcedAddr`),
`addressableValue` (a struct's field inherits it, a dereferenced pointer and a slice element are addressable:
`arshal_default.go` pointer and slice arshalers; an `any`'s dynamic value is copied: `makeInterfaceArshaler`,
`marshalValueAny`); `jsontext` `Encoder.WriteValue` (the method's output: validated, nesting checked,
reformatted as a RawMessage is today), `Decoder.ReadValue` (the value's bytes, no surrounding whitespace,
`buf[pos-n:pos:pos]`, aliasing the input); `isFatalError` (legacy: a method's error is recorded and decoding
goes on).

The dump (jsondesc) records per type and receiver (value or pointer) whether it *implements*
`json.Marshaler`, `json.Unmarshaler`, `encoding.TextMarshaler`, `encoding.TextAppender`,
`encoding.TextUnmarshaler` (reflection's `Implements`, the real signatures), and the names of
`MarshalJSONTo`/`UnmarshalJSONFrom`. The methods stay the program's code: the codec calls them; a program's
proof proves them (the vr kit: `log.Logs`).

- Marshal, `MarshalJSON` with a value receiver: always called (`v.MarshalJSON()`). With a pointer receiver
  only: called where the value is addressable (`p.MarshalJSON()` on the real location: through a pointer, a
  slice element, a field of an addressable struct); elsewhere (a non-pointer root, a field of one, an `any`'s
  value) the default encoding (`needAddr && va.forcedAddr`). The emitted code: `jenc_<T>(b, v, d)` (a copy:
  the unaddressable context) and, only for types whose encoding depends on it, `jencA_<T>(b, p, d)` (the
  addressable one). A nil pointer is `null`, never a call with a nil receiver (`makeMethodArshaler`'s
  comment). The method's error: Marshal fails (the error value is the method's, not `*MarshalerError`: the
  documented error-value deviation). Its output: as a RawMessage today: invalid JSON (also nil or empty) is an
  error, nesting beyond 10000 with the containers around it an error, else compacted (`AppendCompact`, which
  panics NotModelled where real encoding/json would escape `<>&`, an escape or non-ASCII).
- Unmarshal, `UnmarshalJSON` (either receiver): always called (decoding targets are addressable), with the
  value's bytes (`null` included: v1's convention; but a `*T` field's `null` is the pointer's, never passed
  to the method), a slice of the input with capacity cut at its end (`b[j:k:k]`). Its error is recorded
  (the first error is returned) and decoding goes on.
- `omitempty` on such a type: by its kind, not the method (`isLegacyEmpty`).
- A type's default structure is checked (and must be in the subset) only where it is used: for encoding
  unless it has a value-receiver `MarshalJSON`, for decoding unless it has `UnmarshalJSON`. A type with
  both (and a value receiver for Marshal) may have any structure (a map, floats, ...).
- Text methods: `MarshalText`/`AppendText` are accepted only when shadowed (a value-receiver `MarshalJSON`:
  never falls back), `UnmarshalText` only with an `UnmarshalJSON`; otherwise refused (their string quoting
  is not reproduced). Map keys, where the text methods matter most, stay refused (maps are). So
  `metav1.Time`-like types (own JSON methods, promoted `time.Time` text methods) are accepted.

Refused: `MarshalJSONTo`, `UnmarshalJSONFrom` (they take precedence; v2-only API over jsontext); a method
of a hook's name whose signature does not implement the interface (Go ignores it; refused as a likely bug);
the `string` option on a type with methods; text methods not shadowed as above.

## Unchanged

Still refused: floats, maps, arrays, `json.Number`, interfaces with methods, `[]byte` (base64), decoding into
`any`, non-plain strings (escapes, `<>&`, non-ASCII: NotModelled panics), types the codec cannot name
(unexported, generic, package main). **This keeps k8s's `storage.continueToken` (and `etcdHealth`,
`controller`'s `objectForAddOwnerRefPatch`/`objectMetaForPatch`) out**: they are unexported types of k8s
packages, and the codec, a package of the program, cannot name them (a case of a type switch must). That is
a limit of a per-program codec in another package, not of the rules; noted for #24.

## The generated codec's interface (for jsonlean, kept stable)

Per program, in its codec package (`json_gen.go`, Goose-translated; unnamed root structs in
`json_extra_gen.go`):

    func RegisterJSON()                                    // json_model_gen.go: SetCodec(&json.Codec{jsonMarshal, jsonUnmarshal, jsoncodec.Scan})
    func jsonMarshal(v any) ([]byte, error)
    func jsonUnmarshal(data []byte, v any) error
    func jencAny(b []byte, v any, d uint64) ([]byte, error)
    func jenc_<T>(b []byte, v <T>, d uint64) ([]byte, error)          // every closure type but any; unaddressable context
    func jencA_<T>(b []byte, p *<T>, d uint64) ([]byte, error)        // NEW, only for address-sensitive types (§3)
    func jdec_<T>(b []byte, i uint64, p *<T>, e *error) uint64
    func jdecMember_<T>(b []byte, i uint64, key string, p *<T>, e *error) uint64   // structs
    func jencValue(b []byte, x []byte, d uint64) ([]byte, error)      // NEW: a MarshalJSON output (validate, nesting, compact)
    func jencRaw(b []byte, v json.RawMessage, d uint64) ([]byte, error)   // nil -> null, else jencValue
    func jdecRaw(b []byte, i uint64, p *json.RawMessage) uint64
    func jsonSetErr(e *error); func jsonUserErr(e *error, err error)   // NEW: a method's error recorded
    func jsonDepthErr() error
    func jenc<Basic>Ptr(b []byte, x *<basic>) []byte
    func jencAnyExtra(...), jsonUnmarshalExtra(...)                    // json_extra*_gen.go

`<T>`'s identifier: as today (`alias_Name`, `S_<elem>` for an unnamed slice); NEW `P_<elem>` for a pointer
type (`jenc_P_bool(b, v *bool, d)`, `jdec_P_membership_Member(b, i, p **membership.Member, e)`). A type with
`MarshalJSON` has `jenc_<T>` calling it (value receiver) or `jencA_<T>` calling it (pointer receiver); with
`UnmarshalJSON`, `jdec_<T>` is `j := SkipSpace(b,i); k := ValueEnd(b,j); if err := p.UnmarshalJSON(b[j:k:k]);
err != nil { jsonUserErr(e, err) }; return k`.

## Evidence plan

- `models/internal/jsongenrand`: the random types gain embedded fields (exported and unexported values,
  exported pointers, nested, repeated types, name clashes across depths with and without tags, names equal
  ignoring case), pointer fields and elements of every accepted kind, and types with `MarshalJSON`/
  `UnmarshalJSON` (value and pointer receivers; outputs with whitespace, invalid, empty, nested, errors; an
  `UnmarshalJSON` recording the bytes it gets, failing on some), reached in every context (root value, root
  pointer, field of each, slice element, `any`). The generated test (`jsongen_testgen.py`) fills such values
  by reflection (exported fields through unexported embedded structs included) and compares against the real
  encoding/json as today. `TestRefusals` gets one input per new refusal, and the newly accepted constructs
  are checked not refused.
- Regression codecs: `examples/models/jsonetcd` (new): `membership.Member`, `RaftAttributes`, `Attributes`,
  `ConfigChangeContext`, `version.DowngradeInfo`, `version.Versions`, `raftpb.ConfState`,
  `[]*membership.Member` and what else etcd's translated packages marshal; `models/internal/jsonvsr`: the
  log copy updated to go-vsr's current `log.go` (with `Logs`' methods) and roots `log.Logs`, `[]log.Log`, as
  the dsv-vr kit's `json.toml`. `--check` of every input in `etc/gates.sh`.
- An independent reviewer pass on the core (as pbgen's) before asking Upamanyu to land.
