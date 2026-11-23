"""jsongen's trusted core: an encoding/json codec (plain Go code, per type) from a dump of the Go types.

This module is the trusted part of models/json/jsongen.py (`notes/decisions.md`, "Trusted generated
code: the generator is the trusted artifact"). The encoding/json model (`models/encoding/json`)
replaces reflection by the codec a program registers; nothing in Lean fixes how a Go value is
encoded (a program's proof proves its codec meets the `JsonCodec` it uses, and its final statement
does not mention it). What is trusted is that running the program with encoding/json's reflection
replaced by the code this module emits behaves as with the real encoding/json of Go 1.27.3, for
every set of types this module accepts. Everything else of jsongen (the command line, reading the
toml, running the dump, the tests: `jsongen.py`, `jsongen_testgen.py`) is untrusted: a bug there
makes a test weaker or a run fail, never wrong code accepted. `models/jsondesc` (the Go program that
produces the dump this module reads) is trusted with it: a wrong fact there would be wrong code
accepted. So are the helpers the emitted code calls, `models.lab/jsoncodec` (each documented and
tested against real encoding/json, `models/jsoncodec/jsoncodec_test.go`; translated by Goose).

THE REAL LIBRARY. Go 1.27.3's encoding/json, as a program builds it by default: GOEXPERIMENT
jsonv2 is on, so the package is the v1 API over encoding/json/v2 (`src/encoding/json/v2_*.go`):
Marshal and Unmarshal are `jsonv2.Marshal(v, DefaultOptionsV1())` and `jsonv2.Unmarshal(data, v,
DefaultOptionsV1())` (v2_encode.go:185, v2_decode.go:110), the options that restore v1's semantics
(v2_options.go:200-235). Citations below are to `$GOROOT/src/encoding/json/`: the v1 contract as
v2_encode.go:31-184 (Marshal) and v2_decode.go:24-109 (Unmarshal) state it, and where the contract
leaves a choice, the implementation (`v2/arshal_default.go`, `v2/fields.go`, `jsontext/`). (The
build with GOEXPERIMENT=nojsonv2, the v1 implementation in decode.go/encode.go, differs in places,
e.g. it has no nesting limit when encoding; it is not what this core claims.)

THE INPUT is a dump (`models.lab/jsondesc`): per type reached from the roots (the types the
program passes to Marshal, Unmarshal, Encoder.Encode, Decoder.Decode, or holds in an `any` it
marshals), reflection's facts: kind, name, package, element type, struct fields with their `json`
tags (reflect.StructTag.Lookup), the methods named like encoding/json's hooks, which of the hook
interfaces (json.Marshaler, json.Unmarshaler, encoding.TextMarshaler, TextAppender, TextUnmarshaler)
the type or only a pointer to it implements (reflect's Implements: `v2/arshal_methods.go`:421-430,
`implements`), the exported method names of a pointer to it, and whether it is encoding/json's
RawMessage or Number. No field list is written by hand. The dump is made in the Go
module the codec is generated into (jsongen.py runs it there), so it reads the very types the
program links. `Schema` checks the dump and refuses (JsonRefused, every reason, naming the type and
the field) everything outside the subset; on a refusal no code is emitted.

THE SUBSET (accepted):
  - bool, string, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64 (int and uint
    are 64 bits: the models are for 64-bit targets), named or not;
  - slices of accepted types whose element kind is not uint8 (a []byte, or a slice of any named
    uint8 type, encodes as base64: v2_encode.go:69-71, `v2/arshal_default.go`:330-341);
  - named struct types whose fields (encoding/json's flattened fields, EMBEDDED FIELDS below) are
    accepted; an unnamed struct type only as a root (its code is built outside Goose, which cannot
    translate a struct type with tags: below);
  - pointers `*T` (a field, an element, a pointee) to an accepted T that is not itself a pointer
    or an interface (POINTERS below);
  - a type with its own MarshalJSON and/or UnmarshalJSON method (OWN METHODS below);
  - `any` (the empty interface) as a field or element type: encoded by its dynamic type
    (v2_encode.go:175-176), which must be one of the codec's types, a pointer to one, or a basic
    type above; decoding into it is not modelled (a panic);
  - encoding/json.RawMessage (a field, element or root).
  Struct fields: unexported fields are ignored (as encoding/json ignores them, `v2/fields.go`:427-433);
  an exported field's `json` tag is `-` (the field ignored, v2_encode.go:89), or a name followed by
  options: the name empty (the Go field name) or made only of ASCII letters, digits and
  `!#$%()*+-./:;=?@[]^_{|}~` and space (the characters both v1 and v2 accept unquoted and write
  without escaping: v2_encode.go:134-136, `v2/fields.go`:438-445, and none of `<>&`, which are
  HTML-escaped when written: v2_encode.go:62-65); options among `omitempty` and `string` (the
  latter on integer kinds without methods only), each at most once.

EMBEDDED FIELDS (`Schema.flatten`: `v2/fields.go`:80-355 makeStructFields, whose errors v1's
ReportErrorsWithLegacySemantics ignores, `v2/arshal_default.go`:1132-1137, 1310-1312). The fields of a
struct are found breadth-first: an embedded field without a JSON name (no tag name) whose type is a
struct or an unnamed pointer to one (`fields.go`:360-365 indirectType) is not a field: its type is
queued with its index path (`fields.go`:126-131, 156-163), its own embedded fields followed only the
first time the type is seen (`queueEntry{tf, f.index, !seen[tf]}`, line 160); an embedded field with
a JSON name, or of another type, is an ordinary field (an unexported one ignored: `fields.go`:197-208).
Then per JSON name (`fields.go`:286-307): the fields sorted by (name, depth, tagged first), the first
kept iff it is alone, or shallower than the next, or tagged where the next is not; otherwise every
field of that name is dropped (silently). The kept fields are encoded in depth-first index order
(line 323); an object key matches a field by exact name, else by strings.EqualFold, the first in
breadth-first order (`fields.go`:340-349; `arshal_default.go`:1328-1338 with
MatchCaseSensitiveDelimiter). A field behind a nil embedded pointer is skipped when encoding
(`arshal_default.go`:1148-1152); when decoding a member, the nil exported embedded pointers on its
path are allocated first (`arshal_default.go`:1390-1393, 1424-1446 fieldByIndex/indirect). The
emitted code names a promoted field by its path (`v.E.X`); through an unexported embedded struct
(whose exported fields Go promotes: `fields.go`:418-426 and go.dev/issue/21357) by Go's selector
promotion (`v.X`), after checking (`Schema.selector_ok`) that the selector denotes that field.

POINTERS (`v2/arshal_default.go`:1718-1795 makePointerArshaler). Encoding: nil is null, else the
pointee's encoding, the pointee addressable (line 1752). Decoding: null sets the pointer to nil
(1757-1763, also under v1's merge semantics); any other value allocates a pointee if the pointer is
nil (1775-1777, before decoding: a value that fails leaves the new pointee) and decodes into it
(merging into an existing one). omitempty: omitted iff nil (isLegacyEmpty, 1449-1466).

OWN METHODS (`v2/arshal_methods.go`:168-430 makeMethodArshaler, never for a pointer or interface
type, lines 171-175; CallMethodsWithLegacySemantics, `v2_options.go`:237-255):
  - Marshal: a value-receiver MarshalJSON is always called; a pointer-receiver one only on an
    addressable value (`needAddr && va.forcedAddr` falls back to the default encoding, line 234):
    through a pointer or a slice element (`arshal_default.go`:1530, 1752), or a field of an
    addressable struct (1147); not a non-pointer argument of Marshal (`arshal.go`:232-240, copied:
    forcedAddr), nor a field of one, nor an `any`'s value (`arshal_any.go`:51,
    `arshal_default.go`:1846). The emitted code: `jenc_T(b, v, d)` for a copy, and for the types
    whose encoding depends on it (`Schema.sensitive`) `jencA_T(b, p, d)`, the method called on the
    real location. A nil pointer is null, never a call (the pointer arshaler, above). The
    method's error fails Marshal (line 238-246); its output is written as encoding/json's
    Encoder.WriteValue writes it (line 248; `jsontext/encode.go`:527-552): an error if it is not one
    valid JSON value (nil and empty among them) or nests beyond 10000 with the containers around it,
    else without its whitespace (jencValue; jsoncodec.AppendCompact, NotModelled where real
    encoding/json would escape).
  - Unmarshal: UnmarshalJSON (either receiver; decoding targets are always addressable) is called
    with the value's bytes (`arshal_methods.go`:342-345; `jsontext/decode.go`:777
    `d.buf[pos-n:pos:pos]`: no whitespace around it, capacity cut at its end, in the input's
    storage, `jsontext/pools.go`:132-135), null included (but a `*T`'s null is the pointer's,
    above); its error is recorded, the first error returned, and decoding goes on (line 350;
    `v2/errors.go`:62-65 isFatalError).
  - omitempty on such a type goes by its kind (isLegacyEmpty), never by the method.
  - A type's default structure is used, so checked, only for encoding without a value-receiver
    MarshalJSON and for decoding without an UnmarshalJSON: a type with both may be of any kind.
  - The text methods (MarshalText, AppendText, UnmarshalText) are accepted only where shadowed:
    MarshalText/AppendText with a value-receiver MarshalJSON (wrapped by it, lines 230-254, never
    falling back), UnmarshalText with an UnmarshalJSON (lines 337-341).

REFUSED, by `Schema` (exit status 2, every reason printed, naming the type and field):
float32, float64 (their formatting and parsing are not reproduced); complex, chan, func (an
UnsupportedTypeError, v2_encode.go:178-180), uintptr, unsafe.Pointer; arrays; maps; pointers
to pointers, named pointer types, pointers to interfaces, a pointer type as a root (name T: the
codec covers T and *T); the `string` option on a pointer (`makePointerArshaler`'s "null" special
case) or on a type with methods; interfaces with methods; slices of a uint8 kind (base64); an
unexported embedded pointer on the path of a field the codec uses (its nil-ness cannot be tested,
nor the pointer allocated, from another package: Go's errNilField, `arshal_default.go`:1394); an
embedded struct with encoding/json methods (`fields.go`:150-154), tag options on an embedded field
without a JSON name (`fields.go`:139-147, dropped with an ignored error), an unexported embedded
struct with a JSON name (the codec cannot name the field), a field promoted through an unexported
embedded struct whose selector would denote another field or a method; an unexported field with a
`json` tag other than `-` (v2 reports it, `v2/fields.go`:427-433); a field name with other
characters, non-ASCII, or quoted (`'...'`, v2_encode.go:90-93); tag options other than
`omitempty` and `string`, empty or repeated ones, `string` on a non-integer field;
encoding/json.Number; a type that has, or whose pointer has, a method named MarshalJSONTo or
UnmarshalJSONFrom (encoding/json/v2's, which take precedence), a method of a hook's name that does
not implement its interface, or text methods not shadowed (OWN METHODS);
types the codec cannot name (unexported, generic, of package main, of a package with no alias in
the input); Go package aliases or generated names that collide.

THE EMITTED CODE. Marshal (jsonMarshal; jencAny on the argument, by its dynamic type) writes:
  - a nil interface or a nil pointer: `null` (v2_encode.go:172-176); a pointer: its element;
  - bool: `true`/`false`; integers: decimal, `-` for negatives (v2_encode.go:55-57;
    `v2/arshal_default.go`:467-489, strconv.AppendInt/AppendUint); with the `string` option, the
    same in quotes (v2_encode.go:127-132);
  - string: the bytes in quotes (jsoncodec.AppendString), for strings of bytes 0x20..0x7e other
    than `"`, `\\`, `<`, `>`, `&`: real encoding/json writes exactly those bytes for them; any
    other string panics (NotModelled: escaping, UTF-8 coercion and HTML escaping, v2_encode.go:60-67,
    are not reproduced);
  - a slice: `null` if nil, else `[`, the elements separated by `,`, `]` (v2_encode.go:69-71);
  - a struct: `{`, then per flattened field in index order (EMBEDDED FIELDS) that is not behind a
    nil embedded pointer and not omitted, `"name":` and the value, separated by `,`, then `}`
    (v2_encode.go:73-82);
  - a pointer, a type with MarshalJSON: POINTERS, OWN METHODS;
    `omitempty` omits false, 0, a nil interface, a slice or string of length 0, never a struct
    (v2_encode.go:84-87; isLegacyEmpty, `v2/arshal_default.go`:1449-1466);
  - RawMessage: `null` if nil (its MarshalJSON, `jsontext/value.go`:234-240), else an error if it is
    not one valid JSON value, else the value without its whitespace outside strings
    (jsoncodec.AppendCompact, which panics, NotModelled, on a string with `<`, `>`, `&`, an escape or
    a non-ASCII byte: real encoding/json escapes or rewrites those);
  - no whitespace anywhere; nesting: an array or object inside 10000 others, or a RawMessage whose
    nesting (jsoncodec.Nesting) with the containers around it exceeds 10000, is an error, as the
    encoder's nesting limit (`jsontext` maxNestingDepth; measured: jsoncodec_test.go, TestNesting).
  Any value of another type panics (NotModelled; real encoding/json would encode it by
  reflection or return an UnsupportedTypeError).

Unmarshal (the model's Unmarshal first checks that the input is one valid JSON value with only
whitespace around it, jsoncodec.Scan, and returns a syntax error with nothing decoded otherwise, as
the real one, v2_decode.go:91; then jsonUnmarshal) decodes into `*p`, p a non-nil pointer to one of
the codec's types (a nil pointer, or a non-pointer value of one of the codec's types, or nil: an
error, the real InvalidUnmarshalError, v2_decode.go:24-26; anything else panics, NotModelled):
  - null into a slice sets it to nil; null into anything else (bool, string, integer, struct)
    leaves it (v2_decode.go:100-105; `MergeWithLegacySemantics`, `v2/arshal_default.go`:504-509);
  - a value of the wrong kind, or a number out of range or with a fraction or exponent for an
    integer: an error recorded, the target left as it was, decoding goes on and the first error is
    returned (v2_decode.go:93-99; `ReportErrorsWithLegacySemantics`);
  - integers: a JSON number, `-` for signed kinds only, no fraction or exponent, in range
    (`v2/arshal_default.go`:531-554, 632-647); with the `string` option a JSON string holding
    strconv.ParseInt/ParseUint(s, 10, bits) syntax (a `+` or `-` sign for signed kinds, leading
    zeros allowed) or the string "null" (the field left), and nothing else
    (`v2/arshal_default.go`:510-528, 609-627); a string with an escape sequence panics
    (NotModelled: the real one unescapes first);
  - strings: a JSON string without escape sequences or non-ASCII bytes (else a panic, NotModelled:
    unescaping and invalid UTF-8 replacement are not reproduced);
  - slices: a JSON array; `[]` gives a new empty slice (v2_decode.go:75-76); a non-empty array into
    a nil slice gives a new slice of the decoded elements (an element of the wrong kind is
    appended as its zero value); a non-empty array into a non-nil slice panics (NotModelled: the
    real one decodes into the existing elements in place, v2_decode.go:71-74);
  - structs: a JSON object; each member's key matched to the field of that JSON name, else to the
    one equal to it ignoring ASCII case (v2_decode.go:55-59; `v2/fields.go`:367-386 with
    `MatchCaseSensitiveDelimiter`: strings.EqualFold, which for the ASCII keys the codec accepts is
    ASCII case folding; among several, the first breadth-first: EMBEDDED FIELDS); its value decoded
    into that field (merging: the other fields stay; a repeated
    key decodes again, so the last wins); members matching no field skipped; a key with an escape
    or a non-ASCII byte panics (NotModelled);
  - RawMessage: a copy of the value's bytes (without the whitespace around it), also for null
    (its UnmarshalJSON, `jsontext/value.go`:242-251, reusing the target's storage);
  - `any`: panics (NotModelled);
  - a pointer, a type with UnmarshalJSON: POINTERS, OWN METHODS.

WHERE THE CLAIM STOPS (documented deviations, outside "behaves as encoding/json"):
  - error values: only error-or-not is the real one's (*jsoncodec.Error, or a method's own error
    unwrapped, not *SyntaxError, *UnmarshalTypeError, *InvalidUnmarshalError, *MarshalerError, ...). A program that inspects an error's type or
    message observes a difference.
  - what comes with an error: after an Unmarshal error the target's contents are what the codec
    left (the real one says the fields after the problematic one are not guaranteed to be
    decoded, v2_decode.go:97-99); the differential tests compare them too, but the claim does not
    rely on it.
  - slice capacities and aliasing: decoded slices are built by append; the real one sizes them
    otherwise; lengths and contents agree. (The bytes an UnmarshalJSON method gets are a slice of
    the input with capacity cut at the value's end, as the real one's for Unmarshal; for a Decoder,
    of the model's buffer, which the method must not retain, as encoding/json documents.)
  - only the API the encoding/json model covers (`models/encoding/json`, its doc): Marshal,
    Unmarshal, Valid, Encoder.Encode, Decoder.Decode and their companions; MarshalIndent, Indent,
    Compact, HTMLEscape, Token-level decoding and DisallowUnknownFields panic there.

The evidence (untrusted, jsongen.py --help): the generator's differential test over random Go
types of the subset (`models/internal/jsongenrand`), the regression test generated beside each
codec (json_gen_test.go), and the stream tests of the model (`models/internal/jsonstreamtest`).
"""

import re


class JsonRefused(Exception):
    def __init__(self, reasons):
        reasons = list(dict.fromkeys(reasons))     # each reason once, in order
        super().__init__("; ".join(reasons))
        self.reasons = reasons


# integer kinds: (signed, max): the codec's range checks (int and uint: 64 bits)
INTS = {
    "int8": (True, (1 << 7) - 1), "int16": (True, (1 << 15) - 1), "int32": (True, (1 << 31) - 1),
    "int64": (True, (1 << 63) - 1), "int": (True, (1 << 63) - 1),
    "uint8": (False, (1 << 8) - 1), "uint16": (False, (1 << 16) - 1), "uint32": (False, (1 << 32) - 1),
    "uint64": (False, (1 << 64) - 1), "uint": (False, (1 << 64) - 1),
}
BASIC = set(INTS) | {"bool", "string"}
# the characters of an accepted JSON name besides ASCII letters and digits
NAME_PUNCT = set("!#$%()*+-./:;=?@[]^_{|}~ ")
HOOKS = ["MarshalJSON", "UnmarshalJSON", "MarshalText", "UnmarshalText", "AppendText",
         "MarshalJSONTo", "UnmarshalJSONFrom"]
MAX_DEPTH = 10000
# identifiers the generated files use (imports, locals): a package alias that is one of them (or
# starts with "j") is renamed p_<alias> in the generated code
RESERVED = {"json", "jsoncodec", "errors", "bytes", "rand", "reflect", "testing", "fmt", "math",
            "os", "strconv", "strings", "t", "r", "i", "j", "k", "k1", "k2", "v", "x", "b", "b2", "p",
            "e", "err", "st", "s", "c", "key", "more", "empty", "first", "d", "ok", "data", "n",
            "seed", "depth", "a", "w", "got", "want", "real", "model", "m", "q", "u", "f", "y", "z"}


def go_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def is_ascii_ident(s):
    return re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s) is not None


class Step:
    """One step of a struct field's path from the struct the codec encodes (an index of
    reflect.Type.FieldByIndex): the Go field `name` at index `fi` of its struct, of kind
      "field"  the field encoded (the last step);
      "embed"  an exported embedded struct (written `.name`);
      "eptr"   an exported embedded pointer to a struct (written `.name`; nil-checked when encoding,
               allocated when decoding);
      "hidden" an unexported embedded struct (not written: the next step is reached by Go's
               selector promotion, checked unique by `Schema.selector_ok`);
      "hptr"   an unexported embedded pointer to a struct (refused on a field the codec uses);
    `typ`: the field's type, for embedded fields the struct type (a pointer's element)."""

    def __init__(self, fi, name, kind, typ):
        self.fi, self.name, self.kind, self.typ = fi, name, kind, typ


class Field:
    """An encoded struct field (one of encoding/json's flattened fields): its path, JSON name,
    type id, options, and its breadth-first position (the case-insensitive match's precedence)."""

    def __init__(self, steps, json_name, typ, omitempty, quoted, bfs):
        self.steps, self.json, self.typ, self.omitempty, self.quoted = steps, json_name, typ, omitempty, quoted
        self.bfs = bfs

    @property
    def go(self):
        return self.steps[-1].name


# encoding/json's hook interfaces as jsondesc names them, and the method each consists of
IFACE_METHOD = {"Marshaler": "MarshalJSON", "Unmarshaler": "UnmarshalJSON", "TextMarshaler": "MarshalText",
                "TextAppender": "AppendText", "TextUnmarshaler": "UnmarshalText"}


class Schema:
    """The accepted types (by dump id) and roots."""

    def __init__(self, dump, aliases):
        self.t = {e["id"]: e for e in dump["table"]}
        self.reasons = []
        self.alias = {"encoding/json": "json"}   # import path -> alias in the generated code
        for a, p in aliases.items():
            if p == "encoding/json":
                self.reasons.append(f"imports: {a} = \"encoding/json\": name encoding/json's types as json.X")
                continue
            if a in RESERVED or a.startswith("j"):
                a = "p_" + a
            self.alias[p] = a
        if len(set(self.alias.values())) != len(self.alias):
            self.reasons.append("imports: two package aliases are the same after renaming")
        self.ok = {}          # id -> True (checked, accepted)
        self.fields = {}      # struct id (encoded by default) -> [Field], in encoding order
        self.menc = {}        # id -> "value" | "ptr": encoded by its MarshalJSON (receiver kind)
        self.mdec = set()     # ids decoded by their UnmarshalJSON
        self.opaque = set()   # ids whose default structure is never used (both methods)
        self.roots = []       # [(expr, id)]
        self.unnamed = {}     # id of an unnamed struct root -> its expression (aliases renamed)
        self.alias_in = dict(aliases)
        for r in dump["roots"]:
            self.root(r["expr"], r["type"])
        self.closure = []     # every accepted type reached, in a fixed order
        seen = set()
        for _, i in self.roots:
            self.collect(i, seen)
        self.idents = {}
        for i in self.closure:
            n = self.ident(i)
            if n in self.idents.values():
                self.reasons.append(f"type {self.t[i]['string']}: its generated name {n} collides")
            self.idents[i] = n
        self._sens = {}
        if self.reasons:
            raise JsonRefused(self.reasons)

    # -- the subset ------------------------------------------------------------------------

    def refuse(self, where, why):
        self.reasons.append(f"{where}: {why}")
        return False

    def nameable(self, e, where):
        """A named type of a package: the codec can name it (alias.Name)."""
        if "[" in e["name"]:
            return self.refuse(where, f"{e['string']} is a generic type (not nameable)")
        if not e["name"][0].isupper():
            return self.refuse(where, f"{e['string']} is unexported (the codec cannot name it)")
        if e["pkg_name"] == "main":
            return self.refuse(where, f"{e['string']} is in package main (not importable)")
        if e["pkg_path"] not in self.alias:
            return self.refuse(where, f"{e['string']}: its package {e['pkg_path']} has no alias in "
                                      "[json].imports")
        return True

    def hooks(self, i, where):
        """(menc, mdec) of type i: how encoding/json calls its own methods (`v2/arshal_methods.go`
        makeMethodArshaler; never for a pointer or interface type), or None (refused)."""
        e = self.t[i]
        if e["kind"] in ("ptr", "interface"):
            return None, False
        names = set(e["methods"]) | set(e["ptr_methods"])
        impl = e.get("implements") or {}
        bad = False
        for m in ("MarshalJSONTo", "UnmarshalJSONFrom"):
            if m in names:
                bad = not self.refuse(where, f"{e['string']} has method {m} (encoding/json/v2's "
                                             "MarshalerTo/UnmarshalerFrom: outside the subset)")
        for iface, m in IFACE_METHOD.items():
            if m in names and not impl.get(iface):
                bad = not self.refuse(where, f"{e['string']} has a method {m} that does not implement "
                                             f"{iface} (encoding/json ignores it; refused)")
        menc = impl.get("Marshaler") or None
        mdec = bool(impl.get("Unmarshaler"))
        for iface in ("TextMarshaler", "TextAppender"):
            if impl.get(iface) and menc != "value":
                bad = not self.refuse(where, f"{e['string']} implements {iface} and no value-receiver "
                                             "MarshalJSON shadows it (text marshaling is outside the subset)")
        if impl.get("TextUnmarshaler") and not mdec:
            bad = not self.refuse(where, f"{e['string']} implements TextUnmarshaler and no UnmarshalJSON "
                                         "shadows it (text unmarshaling is outside the subset)")
        if bad:
            return None
        return menc, mdec

    def check(self, i, where, ctx, stack=()):
        """Whether type i is accepted in context ctx ("root", "field", "elem")."""
        e = self.t[i]
        if i in self.ok:
            return True
        k = e["kind"]
        if e["raw_message"]:
            self.ok[i] = True
            return True
        if e["number"]:
            return self.refuse(where, "encoding/json.Number is outside the subset")
        h = self.hooks(i, where)
        if h is None:
            return False
        menc, mdec = h
        if e["name"] and e["pkg_path"] and not self.nameable(e, where):
            return False
        if menc:
            self.menc[i] = menc
        if mdec:
            self.mdec.add(i)
        if menc == "value" and mdec:
            # both directions call the methods: the default structure is never used
            self.opaque.add(i)
            self.ok[i] = True
            return True
        if k in BASIC:
            self.ok[i] = True
            return True
        if k == "interface":
            if e["num_method"] != 0:
                return self.refuse(where, f"interface {e['string']} has methods (only any is accepted)")
            if ctx == "root":
                return self.refuse(where, "any as a root (name the types it holds)")
            self.ok[i] = True
            return True
        if k == "slice":
            el = self.t[e["elem"]]
            if el["kind"] == "uint8" and not el["raw_message"]:
                return self.refuse(where, f"{e['string']}: a slice of a uint8 kind (encoded as base64; "
                                          "outside the subset)")
            if i in stack:
                self.ok[i] = True
                return True
            good = self.check(e["elem"], f"{where} element", "elem", stack + (i,))
            if good:
                self.ok[i] = True
            return good
        if k == "struct":
            if not e["name"] and ctx != "root":
                return self.refuse(where, "an unnamed struct type other than a root")
            if i in stack:
                return True
            self.ok[i] = True     # recursion through slices and pointers reaches it again
            good = self.struct_fields(i, stack)
            if not good:
                del self.ok[i]
            return good
        if k == "ptr":
            if ctx == "root":
                return self.refuse(where, f"{e['string']}: a pointer type at the root (name the type: "
                                          "the codec covers T and *T)")
            if e["name"]:
                return self.refuse(where, f"{e['string']}: a named pointer type (outside the subset)")
            el = self.t[e["elem"]]
            if el["kind"] in ("ptr", "interface"):
                return self.refuse(where, f"{e['string']}: a pointer to a {el['kind']} (outside the subset)")
            if i in stack:
                self.ok[i] = True
                return True
            good = self.check(e["elem"], f"{where} pointee", "elem", stack + (i,))
            if good:
                self.ok[i] = True
            return good
        return self.refuse(where, f"kind {k} ({e['string']}) is outside the subset")

    def parse_tag(self, f, where):
        """(ignored, json name, has a name, omitempty, quoted) of a field Go does not ignore, or
        None (refused). `v2/fields.go` parseFieldOptions."""
        tag = f["tag"]
        if tag == "-":
            return True, None, False, False, False
        name, _, opts = tag.partition(",")
        has_name = name != ""
        if name == "":
            name = f["name"]
            if not is_ascii_ident(name):
                self.refuse(where, f"Go name {name!r} is not ASCII (the codec writes names raw)")
                return None
        elif any(not (c.isascii() and (c.isalnum() or c in NAME_PUNCT)) for c in name):
            self.refuse(where, f"JSON name {name!r}: a character outside ASCII letters, digits and "
                               f"{''.join(sorted(NAME_PUNCT))!r}")
            return None
        omitempty = quoted = False
        if "," in tag:
            seen = set()
            for o in opts.split(","):
                if o not in ("omitempty", "string"):
                    self.refuse(where, f"tag option {o!r} (only omitempty and string are reproduced)")
                    return None
                if o in seen:
                    self.refuse(where, f"tag option {o!r} repeated")
                    return None
                seen.add(o)
            omitempty, quoted = "omitempty" in seen, "string" in seen
        return False, name, has_name, omitempty, quoted

    def indirect(self, tid):
        """`v2/fields.go` indirectType: an unnamed pointer's element, else the type."""
        e = self.t[tid]
        if e["kind"] == "ptr" and not e["name"]:
            return e["elem"], True
        return tid, False

    def flatten(self, i):
        """encoding/json's fields of struct i (`v2/fields.go` makeStructFields, whose errors v1's
        options ignore): ([Field] in encoding order, [(where, why)] refusals, [all walked fields]).
        Breadth-first over embedded structs (a type seen before is queued again without its own
        embedded fields: visitChildren = !seen[tf]); then per JSON name the dominant field
        (alone, or the shallowest, or the only tagged one at that depth), else none of them;
        ordered depth-first by index."""
        reasons = []
        queue = [(i, [], True)]
        seen = {i}
        cand = []           # (json name, depth, has name, index, Field)
        qi = 0
        while qi < len(queue):
            ti, steps, visit = queue[qi]
            qi += 1
            te = self.t[ti]
            for fi, f in enumerate(te["fields"]):
                fw = f"{te['string']}.{f['name']}"
                if not f["exported"] and not f["embedded"]:
                    # ignored (`fields.go` parseFieldOptions); a tag on it is v2's error: refused
                    if f["has_tag"] and f["tag"] != "-":
                        reasons.append((fw, f"an unexported field with tag json:{f['tag']!r}"))
                    continue
                if f["tag"] == "-":
                    continue
                p = self.parse_tag(f, fw)
                if p is None:
                    reasons.append(None)
                    continue
                _, name, has_name, omitempty, quoted = p
                tid, isptr = self.indirect(f["type"])
                if f["embedded"] and not has_name and self.t[tid]["kind"] == "struct":
                    # handleEmbed: the embedded struct's fields are promoted
                    if omitempty or quoted:
                        reasons.append((fw, "tag options on an embedded field without a JSON name (Go "
                                            "drops them with an error it ignores; refused)"))
                        continue
                    te2 = self.t[tid]
                    if (any((te2.get("implements") or {}).values()) or
                            {"MarshalJSONTo", "UnmarshalJSONFrom"} & (set(te2["methods"]) | set(te2["ptr_methods"]))):
                        reasons.append((fw, f"an embedded {te2['string']} with encoding/json methods "
                                            "(v2: must not implement marshal or unmarshal methods)"))
                        continue
                    kind = ("eptr" if isptr else "embed") if f["exported"] else ("hptr" if isptr else "hidden")
                    st = Step(fi, f["name"], kind, tid)
                    if visit:
                        queue.append((tid, steps + [st], tid not in seen))
                    seen.add(tid)
                    continue
                # handleField: an ordinary field
                if not f["exported"]:
                    if f["embedded"] and self.t[tid]["kind"] == "struct":
                        reasons.append((fw, "an unexported embedded struct with a JSON name (the codec "
                                            "cannot name the field)"))
                    continue          # an unexported embedded non-struct: ignored (Go's ignored error)
                st = Step(fi, f["name"], "field", f["type"])
                path = steps + [st]
                fld = Field(path, name, f["type"], omitempty, quoted, len(cand))
                cand.append((name, len(path), has_name, [s.fi for s in path], fld, fw))
        # dominance: sort by (name, depth, tagged first), keep the first of a name if it dominates
        order = sorted(cand, key=lambda c: (c[0].encode(), c[1], not c[2]))   # stable; Go compares bytes
        kept = []
        k = 0
        while k < len(order):
            n = 1
            while k + n < len(order) and order[k + n][0] == order[k][0]:
                n += 1
            if n == 1 or order[k][1] != order[k + 1][1] or order[k][2] != order[k + 1][2]:
                kept.append(order[k])
            k += n
        kept.sort(key=lambda c: c[3])
        return [c[4] for c in kept], [c[5] for c in kept], reasons

    def selector_ok(self, s, path):
        """Whether Go's selector `x.N` on a value x of struct type s denotes the field at index path
        (N its Go name): N is no method of s or *s, and among the fields of s's embedding tree
        (embedded structs and pointers to structs followed) the shallowest named N is unique and
        is this one (the Go spec's selector rule)."""
        target = path
        n = None
        cur = s
        for fi in path:
            f = self.t[cur]["fields"][fi]
            n = f["name"]
            if f["type"] >= 0:
                cur = self.indirect(f["type"])[0]
        if n in self.t[s].get("method_names", []):
            return False
        level = [([], s)]
        for _ in range(len(path)):
            matches, nxt = [], []
            for pre, st in level:
                for fi, f in enumerate(self.t[st]["fields"]):
                    if f["name"] == n:
                        matches.append(pre + [fi])
                    if f["embedded"] and f["type"] >= 0:
                        tid, _ = self.indirect(f["type"])
                        if self.t[tid]["kind"] == "struct":
                            nxt.append((pre + [fi], tid))
            if matches:
                return matches == [target]
            level = nxt
        return False

    def struct_fields(self, i, stack):
        e = self.t[i]
        good = True
        fields, wheres, reasons = self.flatten(i)
        for r in reasons:
            if r is not None:
                self.refuse(*r)
            good = False
        out = []
        for f, fw in zip(fields, wheres):
            ft = self.t[f.typ]
            ok = True
            # the path: no unexported embedded pointer; promoted selectors unique; embedded
            # pointers' types nameable (decoding allocates them)
            base, pending = i, []
            for s in f.steps:
                if s.kind == "hptr":
                    ok = self.refuse(fw, "reached through an unexported embedded pointer (its nil-ness "
                                         "cannot be tested nor the pointer allocated from the codec)")
                    break
                if s.kind == "hidden":
                    pending.append(s.fi)
                    base_next = s.typ
                    continue
                if pending and not self.selector_ok(base, pending + [s.fi]):
                    ok = self.refuse(fw, f"promoted through an unexported embedded struct, but the "
                                         f"selector .{s.name} on {self.t[base]['string']} does not denote "
                                         "it (another field or a method of that name)")
                    break
                pending = []
                if s.kind == "eptr" and not self.nameable(self.t[s.typ], fw):
                    ok = False
                    break
                if s.kind in ("embed", "eptr"):
                    base = s.typ
            if not ok:
                good = False
                continue
            if f.quoted and (ft["kind"] not in INTS or ft["raw_message"] or
                             (self.hooks(f.typ, fw) or (None, False)) != (None, False)):
                good = self.refuse(fw, f"the string option on a {ft['kind']} field (reproduced for "
                                       "integers without encoding/json methods only)")
                continue
            if not self.check(f.typ, f"{fw} ({ft['string']})", "field", stack + (i,)):
                good = False
                continue
            out.append(f)
        self.fields[i] = out
        return good

    def root(self, expr, i):
        e = self.t[i]
        where = f"root {expr}"
        if e["kind"] == "ptr":
            return self.refuse(where, "a pointer type (name the type: the codec covers T and *T)")
        if e["kind"] == "struct" and not e["name"]:
            self.unnamed[i] = re.sub(r"\b(\w+)\.", lambda m: self.alias.get(self.alias_in.get(m.group(1), ""),
                                                                            m.group(1)) + ".", expr)
        if self.check(i, where, "root") and all(i != j for _, j in self.roots):
            self.roots.append((expr, i))

    def collect(self, i, seen):
        if i in seen:
            return
        seen.add(i)
        e = self.t[i]
        if i not in self.opaque:
            if e["kind"] in ("slice", "ptr") and not e["raw_message"]:
                self.collect(e["elem"], seen)
            if e["kind"] == "struct":
                for f in self.fields[i]:
                    self.collect(f.typ, seen)
        self.closure.append(i)

    def sensitive(self, i):
        """Whether type i encodes differently addressable (`jencA_`) and not (`jenc_`): it has a
        pointer-receiver MarshalJSON (called only on an addressable value, `arshal_methods.go`
        `needAddr && va.forcedAddr`), or it is a struct encoded by default with such a field
        reached without an embedded pointer (a struct's fields inherit its addressability;
        pointees and slice elements are always addressable)."""
        if i in self._sens:
            return self._sens[i]
        self._sens[i] = False
        r = False
        if self.menc.get(i) == "ptr":
            r = True
        elif i not in self.menc and self.t[i]["kind"] == "struct":
            r = any(self.sensitive(f.typ) for f in self.fields[i] if not any(s.kind == "eptr" for s in f.steps))
        self._sens[i] = r
        return r

    # -- names -----------------------------------------------------------------------------

    def go(self, i):
        """The Go spelling of type i."""
        e = self.t[i]
        if i in self.unnamed:
            return self.unnamed[i]
        if e["raw_message"]:
            return "json.RawMessage"
        if e["kind"] == "interface":
            return "any"
        if e["name"] and e["pkg_path"]:
            return f"{self.alias[e['pkg_path']]}.{e['name']}"
        if e["name"]:
            return e["name"]          # a predeclared basic type
        if e["kind"] == "slice":
            return "[]" + self.go(e["elem"])
        if e["kind"] == "ptr":
            return "*" + self.go(e["elem"])
        raise AssertionError(f"no spelling for {e['string']}")

    def ident(self, i):
        e = self.t[i]
        if i in self.unnamed:
            return f"root{sorted(self.unnamed).index(i)}"
        if e["raw_message"]:
            return "RawMessage"
        if e["kind"] == "slice" and not e["name"]:
            return "S_" + self.ident(e["elem"])
        if e["kind"] == "ptr" and not e["name"]:
            return "P_" + self.ident(e["elem"])
        return re.sub(r"[^A-Za-z0-9]", "_", self.go(i))

    def kind(self, i):
        e = self.t[i]
        if e["raw_message"]:
            return "raw"
        if e["kind"] in INTS:
            return "int"
        return e["kind"]          # bool string slice struct interface ptr (or another, if opaque)

    def goose(self, i):
        """Whether type i's code is in json_gen.go (Goose's), not the !goose file."""
        return i not in self.unnamed

    def uses_json(self):
        return any(self.t[i]["raw_message"] for i in self.closure)

    def uses_value(self):
        return self.uses_json() or any(i in self.menc for i in self.closure)


# ---------------------------------------------------------------------------------------------
# The emitter

def nm(msg):
    return f"panic(jsoncodec.NotModelled({go_str('json model: ' + msg)}))"


def int_append(S, i, expr, quoted):
    signed, _ = INTS[S.t[i]["kind"]]
    fn = ("AppendQuotedInt" if quoted else "AppendInt") if signed else \
         ("AppendQuotedUint" if quoted else "AppendUint")
    conv = "int64" if signed else "uint64"
    return f"b = jsoncodec.{fn}(b, {conv}({expr}))"


def inline_scalar(S, i):
    """Whether type i's encoding and decoding are written inline (a basic kind, no methods)."""
    return S.kind(i) in ("int", "string", "bool") and i not in S.menc and i not in S.mdec


def scalar_enc(S, i, expr, quoted):
    k = S.kind(i)
    if k == "int":
        return [int_append(S, i, expr, quoted)]
    if k == "string":
        return [f"b = jsoncodec.AppendString(b, string({expr}))"]
    return [f"b = jsoncodec.AppendBool(b, bool({expr}))"]


def enc_value(S, i, expr, quoted, d, ptr=None):
    """Go statements appending the encoding of expr (of type i) to b at depth d (an expression);
    ptr: expr's address where the value is addressable (else None: a copy). They may return an
    error."""
    k = S.kind(i)
    if i not in S.menc and k in ("int", "string", "bool"):
        return scalar_enc(S, i, expr, quoted)
    if ptr is not None and S.sensitive(i):
        call = f"jencA_{S.idents[i]}(b, {ptr}, {d})"
    elif k == "raw":
        call = f"jencRaw(b, {expr}, {d})"
    elif k == "interface":
        call = f"jencAny(b, {expr}, {d})"
    else:
        call = f"jenc_{S.idents[i]}(b, {expr}, {d})"
    return [f"b, err = {call}", "if err != nil {", "\treturn b, err", "}"]


def empty_test(S, i, expr):
    """A Go condition: expr (of type i) is not empty for omitempty (None: never empty). By kind,
    whatever its methods (`v2/arshal_default.go` isLegacyEmpty)."""
    k = S.t[i]["kind"]
    if S.t[i]["raw_message"] or k in ("string", "slice", "map", "array"):
        return f"len({expr}) != 0"
    if k in INTS or k in ("float32", "float64", "uintptr"):
        return f"{expr} != 0"
    if k == "bool":
        return f"bool({expr})"
    if k in ("interface", "ptr"):
        return f"{expr} != nil"
    return None


def field_expr(base, steps):
    """The Go selector of a field's path (unexported embedded structs left to promotion)."""
    return base + "".join("." + s.name for s in steps if s.kind != "hidden")


def nil_conds(base, steps):
    return [f"{field_expr(base, steps[:n + 1])} != nil" for n, s in enumerate(steps) if s.kind == "eptr"]


def struct_enc_body(S, i, base, addressable):
    """The statements encoding the struct `base` (a value, or a pointer if addressable): its
    flattened fields in order (`v2/arshal_default.go` makeStructArshaler: a field behind a nil
    embedded pointer skipped, then omitempty)."""
    fields = S.fields[i]
    dyn = any(f.omitempty or nil_conds(base, f.steps) for f in fields)
    body = ["if d >= jsoncodec.MaxDepth {", "\treturn b, jsonDepthErr()", "}",
            "var err error", "_ = err", "b = append(b, '{')"]
    if dyn:
        body += ["first := true", "_ = first"]
    for n, f in enumerate(fields):
        expr = field_expr(base, f.steps)
        conds = nil_conds(base, f.steps)
        faddr = addressable or bool(conds)
        key = go_str('"' + f.json + '":')
        val = enc_value(S, f.typ, expr, f.quoted, "d+1", ptr=f"&{expr}" if faddr else None)
        if dyn:
            stmts = ["if !first {", "\tb = append(b, ',')", "}", "first = false",
                     f"b = jsoncodec.AppendRaw(b, {key})"] + val
            if f.omitempty:
                c = empty_test(S, f.typ, expr)
                if c is not None:
                    conds = conds + [c]
            if not conds:
                body += stmts
            else:
                body += [f"if {' && '.join(conds)} {{"] + ["\t" + l for l in stmts] + ["}"]
        else:
            sep = go_str(("," if n > 0 else "") + '"' + f.json + '":')
            body += [f"b = jsoncodec.AppendRaw(b, {sep})"] + val
    body += ["return append(b, '}'), nil"]
    return body


def method_enc_body(recv):
    return [f"x, err := {recv}.MarshalJSON()", "if err != nil {", "\treturn b, err", "}",
            "return jencValue(b, x, d)"]


def default_enc_body(S, i):
    """The statements of jenc_<i> (v of type i, unaddressable) by its kind."""
    k = S.kind(i)
    if k in ("int", "string", "bool"):
        return scalar_enc(S, i, "v", False) + ["return b, nil"]
    if k == "raw":
        return ["return jencRaw(b, v, d)"]
    if k == "slice":
        et = S.t[i]["elem"]
        body = ["if v == nil {", "\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "}",
                "if d >= jsoncodec.MaxDepth {", "\treturn b, jsonDepthErr()", "}",
                "var err error", "_ = err", "b = append(b, '[')"]
        if S.sensitive(et):
            # a slice element is addressable (`v2/arshal_default.go` makeSliceArshaler)
            body += ["for i := range v {", "\tif i > 0 {", "\t\tb = append(b, ',')", "\t}"]
            body += ["\t" + l for l in enc_value(S, et, "v[i]", False, "d+1", ptr="&v[i]")]
        else:
            body += ["for i, x := range v {", "\tif i > 0 {", "\t\tb = append(b, ',')", "\t}"]
            body += ["\t" + l for l in enc_value(S, et, "x", False, "d+1")]
        body += ["}", "return append(b, ']'), nil"]
        return body
    if k == "ptr":
        et = S.t[i]["elem"]
        # nil: null; else the pointee, addressable (`v2/arshal_default.go` makePointerArshaler)
        body = ["if v == nil {", "\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "}",
                "var err error", "_ = err"]
        body += enc_value(S, et, "*v", False, "d", ptr="v")
        return body + ["return b, nil"]
    return struct_enc_body(S, i, "v", False)


def gen_encoder(S, i):
    g, I, k = S.go(i), S.idents[i], S.kind(i)
    out = []
    if S.menc.get(i) == "value":
        body = method_enc_body("v")
        what = "by its MarshalJSON method (value receiver: always called)"
    else:
        body = default_enc_body(S, i)
        what = "inside d arrays and objects, unaddressable"
    out += [f"// jenc_{I} appends the encoding of a {g} {what}.",
            f"func jenc_{I}(b []byte, v {g}, d uint64) ([]byte, error) {{"]
    out += ["\t" + l for l in body] + ["}", ""]
    if S.sensitive(i):
        if S.menc.get(i) == "ptr":
            body = method_enc_body("p")
            what = "by its MarshalJSON method (pointer receiver: called on an addressable value)"
        else:
            body = struct_enc_body(S, i, "p", True)
            what = "at *p (addressable: its fields' pointer-receiver MarshalJSON methods are called)"
        out += [f"// jencA_{I} appends the encoding of the {g} {what}.",
                f"func jencA_{I}(b []byte, p *{g}, d uint64) ([]byte, error) {{"]
        out += ["\t" + l for l in body] + ["}", ""]
    return out


def scalar_dec(S, i, quoted, target):
    """Go statements decoding the value at b[i:] into target (an addressable expression of type i,
    a bool, string or integer kind), setting k (the index after the value)."""
    k = S.kind(i)
    g = S.go(i)
    if k == "int":
        signed, mx = INTS[S.t[i]["kind"]]
        fn = ("QuotedInt" if quoted else "Int") if signed else ("QuotedUint" if quoted else "Uint")
        call = f"jsoncodec.{fn}(b, i, {mx})"
    elif k == "string":
        call = "jsoncodec.String(b, i)"
    else:
        call = "jsoncodec.Bool(b, i)"
    return [f"y, st, k1 := {call}", "k = k1", "if st == jsoncodec.Set {", f"\t{target} = {g}(y)",
            "} else if st == jsoncodec.TypeErr {", "\tjsonSetErr(e)", "}"]


def dec_value(S, i, quoted, target, ptr=None):
    """Go statements decoding the value at b[i:] into target (of type i; ptr: its address, else
    &target), setting k."""
    k = S.kind(i)
    addr = ptr if ptr is not None else f"&{target}"
    if inline_scalar(S, i):
        return scalar_dec(S, i, quoted, target)
    if k == "interface":
        return [nm("decoding into an interface (any)")]
    if k == "raw":
        return [f"k = jdecRaw(b, i, {addr})"]
    return [f"k = jdec_{S.idents[i]}(b, i, {addr}, e)"]


def gen_decoder(S, i):
    g, I, k = S.go(i), S.idents[i], S.kind(i)
    out = [f"// jdec_{I} decodes the value at b[i:] (valid JSON, after whitespace) into *p as real",
           "// encoding/json does; the first error is kept in *e. It returns the index after the value.",
           f"func jdec_{I}(b []byte, i uint64, p *{g}, e *error) uint64 {{"]
    if i in S.mdec:
        # its UnmarshalJSON, given the value's bytes (`jsontext` ReadValue: no whitespace, capacity
        # cut at the end); its error recorded, decoding goes on (`arshal_methods.go`, isFatalError)
        body = ["j := jsoncodec.SkipSpace(b, i)", "k := jsoncodec.ValueEnd(b, j)",
                "err := p.UnmarshalJSON(b[j:k:k])", "if err != nil {", "\tjsonUserErr(e, err)", "}",
                "return k"]
    elif k in ("int", "string", "bool"):
        body = ["var k uint64"] + scalar_dec(S, i, False, "*p") + ["return k"]
    elif k == "raw":
        body = ["return jdecRaw(b, i, p)"]
    elif k == "ptr":
        et = S.t[i]["elem"]
        # null: nil; else allocate if nil, then decode into the pointee (makePointerArshaler)
        body = ["j, c := jsoncodec.At(b, i)", "if c == 'n' {", "\t*p = nil", "\treturn j + 4", "}",
                "if *p == nil {", f"\t*p = new({S.go(et)})", "}", "q := *p", "var k uint64"]
        body += dec_value(S, et, False, "*q", ptr="q") + ["return k"]
    elif k == "slice":
        et = S.t[i]["elem"]
        body = ["j, c := jsoncodec.At(b, i)", "if c == 'n' {", "\t*p = nil", "\treturn j + 4", "}",
                "if c != '[' {", "\tjsonSetErr(e)", "\treturn jsoncodec.ValueEnd(b, j)", "}",
                "empty, k := jsoncodec.Empty(b, j)", "if empty {", f"\t*p = make({g}, 0)", "\treturn k", "}",
                "if *p != nil {", "\t" + nm("decoding a non-empty array into a non-nil slice"), "}"]
        if S.kind(et) == "interface":
            body += [nm("decoding into an interface (any)")]
        else:
            body += [f"s := make({g}, 0)", "for {", f"\tvar x {S.go(et)}", "\ti := k"]
            body += ["\t" + l for l in dec_value(S, et, False, "x")]
            body += ["\ts = append(s, x)", "\tmore, k2 := jsoncodec.Next(b, k)", "\tk = k2",
                     "\tif !more {", "\t\t*p = s", "\t\treturn k", "\t}", "}"]
    else:
        body = ["j, c := jsoncodec.At(b, i)", "if c == 'n' {", "\treturn j + 4", "}",
                "if c != '{' {", "\tjsonSetErr(e)", "\treturn jsoncodec.ValueEnd(b, j)", "}",
                "empty, k := jsoncodec.Empty(b, j)", "if empty {", "\treturn k", "}", "for {",
                "\tkey, v := jsoncodec.Member(b, k)", f"\tk = jdecMember_{I}(b, v, key, p, e)",
                "\tmore, k2 := jsoncodec.Next(b, k)", "\tk = k2", "\tif !more {", "\t\treturn k", "\t}", "}"]
    out += ["\t" + l for l in body] + ["}", ""]
    if k == "struct" and i not in S.mdec:
        out += [f"// jdecMember_{I} decodes the value of member key at b[i:] into its field of *p (the",
                "// field of that JSON name, else the first, breadth-first, whose name equals it ignoring",
                "// case; else the value is skipped), as real encoding/json does, allocating the nil",
                "// embedded pointers on the field's path first; it returns the index after the value.",
                f"func jdecMember_{I}(b []byte, i uint64, key string, p *{g}, e *error) uint64 {{"]
        by_bfs = sorted(S.fields[i], key=lambda f: f.bfs)
        for mode, fs in (("exact", S.fields[i]), ("fold", by_bfs)):
            for f in fs:
                cond = (f"key == {go_str(f.json)}" if mode == "exact"
                        else f"jsoncodec.FoldEq(key, {go_str(f.json)})")
                if S.kind(f.typ) == "interface":
                    out += [f"\tif {cond} {{", "\t\t" + nm("decoding into an interface (any)"), "\t}"]
                    continue
                out += [f"\tif {cond} {{"]
                for n, s in enumerate(f.steps):
                    if s.kind == "eptr":
                        x = field_expr("p", f.steps[:n + 1])
                        out += [f"\t\tif {x} == nil {{", f"\t\t\t{x} = new({S.go(s.typ)})", "\t\t}"]
                out += ["\t\tvar k uint64"]
                out += ["\t\t" + l for l in dec_value(S, f.typ, f.quoted, field_expr("p", f.steps))]
                out += ["\t\treturn k", "\t}"]
        out += ["\treturn jsoncodec.ValueEnd(b, jsoncodec.SkipSpace(b, i))", "}", ""]
    return out


# the dynamic types jencAny knows besides the codec's own: the basic types of the subset
ANY_BASICS = ["bool", "string", "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16",
              "uint32", "uint64"]


def any_cases(S, ids, basics):
    out = []
    for g in basics:
        if g in INTS:
            enc = f"jsoncodec.{'AppendInt' if INTS[g][0] else 'AppendUint'}(b, {'int64' if INTS[g][0] else 'uint64'}(x))"
        elif g == "string":
            enc = "jsoncodec.AppendString(b, x)"
        else:
            enc = "jsoncodec.AppendBool(b, x)"
        out += [f"case {g}:", f"\treturn {enc}, nil", f"case *{g}:", "\tif x == nil {",
                "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "\t}", f"\treturn jenc{g.capitalize()}Ptr(b, x), nil"]
    for i in ids:
        g, I = S.go(i), S.idents[i]
        if g in ANY_BASICS or S.kind(i) == "interface":
            continue
        if S.kind(i) == "ptr":
            # a value of type *T is T's pointer case; **T here
            out += [f"case *{g}:", "\tif x == nil {", "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "\t}",
                    f"\treturn jenc_{I}(b, *x, d)"]
            continue
        # an any's value is copied (unaddressable); a pointer's pointee is addressable
        # (`v2/arshal_any.go` marshalValueAny, `v2/arshal.go` marshalEncode)
        deref = f"jencA_{I}(b, x, d)" if S.sensitive(i) else f"jenc_{I}(b, *x, d)"
        out += [f"case {g}:", f"\treturn jenc_{I}(b, x, d)", f"case *{g}:", "\tif x == nil {",
                "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "\t}", f"\treturn {deref}"]
    return out


def unmarshal_cases(S, ids):
    out = []
    for i in ids:
        g, I = S.go(i), S.idents[i]
        if S.kind(i) == "interface":
            continue
        out += [f"case *{g}:", "\tif p == nil {",
                f"\t\treturn &jsoncodec.Error{{Msg: {go_str('Unmarshal(nil *' + g + ')')}}}", "\t}",
                f"\tjdec_{I}(data, 0, p, &err)", "\treturn err"]
        if S.kind(i) != "ptr":
            out += [f"case {g}:", f"\treturn &jsoncodec.Error{{Msg: {go_str('Unmarshal(non-pointer ' + g + ')')}}}"]
    return out


def imports(S, text, extra=()):
    text = "\n".join(l for l in text.split("\n") if not l.lstrip().startswith("//"))
    imps = list(extra)
    if re.search(r"\bjson\.", text):
        imps.insert(0, '\tjson "encoding/json"')
    imps.append('\t"models.lab/jsoncodec"')
    for p, a in sorted(S.alias.items(), key=lambda x: x[1]):
        if p != "encoding/json" and re.search(r"\b" + re.escape(a) + r"\.", text):
            imps.append(f'\t{a} "{p}"')
    return ["import ("] + imps + [")", ""]


def codec_go(S, header, pkg):
    """json_gen.go: the codec of the named types (Goose's)."""
    ids = [i for i in S.closure if S.goose(i)]
    body = [
        "// jsonMarshal is the codec's Marshal: v's encoding as real encoding/json's Marshal writes it,",
        "// for v nil, a value of one of the codec's types or a basic type, or a pointer to one; any",
        "// other v panics (NotModelled).",
        "func jsonMarshal(v any) ([]byte, error) {",
        "\tb, err := jencAny(make([]byte, 0), v, 0)",
        "\tif err != nil {",
        "\t\treturn nil, err",
        "\t}",
        "\treturn b, nil",
        "}",
        "",
        "// jsonUnmarshal is the codec's Unmarshal: decodes data (one valid JSON value, whitespace",
        "// around it) into *v as real encoding/json's Unmarshal does, v a non-nil pointer to one of the",
        "// codec's types; real encoding/json's error for a nil pointer, a non-pointer of one of its",
        "// types, or nil; any other v panics (NotModelled).",
        "func jsonUnmarshal(data []byte, v any) error {"]
    uc = unmarshal_cases(S, ids)
    if uc:
        body += ["\tvar err error", "\tswitch p := v.(type) {"] + ["\t" + l for l in uc] + ["\t}"]
    body += ["\tif v == nil {", "\t\treturn &jsoncodec.Error{Msg: \"Unmarshal(nil)\"}", "\t}",
             "\treturn jsonUnmarshalExtra(data, v)", "}", "",
             "// jencAny appends the encoding of v by its dynamic type (nil: null) inside d arrays and",
             "// objects; a type the codec does not know panics (NotModelled).",
             "func jencAny(b []byte, v any, d uint64) ([]byte, error) {",
             "\tif v == nil {", "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "\t}",
             "\tswitch x := v.(type) {"]
    body += ["\t" + l for l in any_cases(S, ids, ANY_BASICS)]
    body += ["\t}", "\treturn jencAnyExtra(b, v, d)", "}", ""]
    for g in ANY_BASICS:
        if g in INTS:
            enc = f"jsoncodec.{'AppendInt' if INTS[g][0] else 'AppendUint'}(b, {'int64' if INTS[g][0] else 'uint64'}(*x))"
        elif g == "string":
            enc = "jsoncodec.AppendString(b, *x)"
        else:
            enc = "jsoncodec.AppendBool(b, *x)"
        body += [f"func jenc{g.capitalize()}Ptr(b []byte, x *{g}) []byte {{", f"\treturn {enc}", "}", ""]
    body += [
        "// jsonSetErr records a decoding error (real encoding/json keeps decoding and returns the",
        "// first error).",
        "func jsonSetErr(e *error) {",
        "\tif *e == nil {",
        "\t\t*e = &jsoncodec.Error{Msg: \"a value of the wrong kind or out of range\"}",
        "\t}",
        "}",
        "",
        "// jsonDepthErr is the error of a value nested deeper than encoding/json's encoder allows.",
        "func jsonDepthErr() error {",
        "\treturn &jsoncodec.Error{Msg: \"exceeded the maximum nesting depth\"}",
        "}",
        ""]
    if S.mdec & set(ids):
        body += [
            "// jsonUserErr records an UnmarshalJSON method's error (real encoding/json keeps decoding",
            "// and returns the first error).",
            "func jsonUserErr(e *error, err error) {",
            "\tif *e == nil {",
            "\t\t*e = err",
            "\t}",
            "}",
            ""]
    if S.uses_value():
        body += [
            "// jencValue appends a MarshalJSON method's output x as real encoding/json does: an error if",
            "// it is not one valid JSON value (nil and empty among them) or nests too deep inside d arrays",
            "// and objects, else the value compacted (jsoncodec.AppendCompact).",
            "func jencValue(b []byte, x []byte, d uint64) ([]byte, error) {",
            "\tif !jsoncodec.Valid(x) {",
            "\t\treturn b, &jsoncodec.Error{Msg: \"a MarshalJSON output that is not one valid JSON value\"}",
            "\t}",
            "\tif d+jsoncodec.Nesting(x) > jsoncodec.MaxDepth {",
            "\t\treturn b, jsonDepthErr()",
            "\t}",
            "\tb2, _ := jsoncodec.AppendCompact(b, x)",
            "\treturn b2, nil",
            "}",
            ""]
    if S.uses_json():
        body += [
            "// jencRaw appends a RawMessage as real encoding/json does (its MarshalJSON: null if nil,",
            "// else the value, through jencValue).",
            "func jencRaw(b []byte, v json.RawMessage, d uint64) ([]byte, error) {",
            "\tif v == nil {",
            "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil",
            "\t}",
            "\treturn jencValue(b, v, d)",
            "}",
            "",
            "// jdecRaw decodes the value at b[i:] into a RawMessage: a copy of its bytes, without the",
            "// whitespace around it, in *p's storage (its UnmarshalJSON); also for null.",
            "func jdecRaw(b []byte, i uint64, p *json.RawMessage) uint64 {",
            "\tj := jsoncodec.SkipSpace(b, i)",
            "\tk := jsoncodec.ValueEnd(b, j)",
            "\t*p = append((*p)[0:0], b[j:k]...)",
            "\treturn k",
            "}",
            ""]
    for i in ids:
        if S.kind(i) != "interface":
            body += gen_encoder(S, i) + gen_decoder(S, i)
    text = "\n".join(body)
    return "\n".join([header.rstrip("\n"), "", f"package {pkg}", ""] + imports(S, text)) + "\n" + text


def extra_go(S, header, pkg):
    """{file: contents}: the unnamed root types' code (json_extra_gen.go, !goose) and the stub Goose
    sees (json_extra_goose_gen.go); without unnamed roots, json_extra_gen.go is the stub."""
    stub = [
        "// jencAnyExtra: under Goose the codec has no unnamed type; encoding a value of a type it does",
        "// not know panics (NotModelled).",
        "func jencAnyExtra(b []byte, v any, d uint64) ([]byte, error) {",
        "\t" + nm("encoding a value of a type the codec does not know"),
        "}",
        "",
        "// jsonUnmarshalExtra: decoding into a type the codec does not know panics (NotModelled).",
        "func jsonUnmarshalExtra(data []byte, v any) error {",
        "\t" + nm("decoding into a type the codec does not know"),
        "}"]
    stub_text = "\n".join(stub) + "\n"

    def file(tag, text):
        h = header.rstrip("\n") + "\n\n" + (f"//go:build {tag}\n\n" if tag else "")
        return h + f"package {pkg}\n\n" + "\n".join(imports(S, text)) + "\n" + text

    if not S.unnamed:
        return {"json_extra_gen.go": file(None, stub_text)}
    ids = [i for i in S.closure if not S.goose(i)]
    body = ["// jencAnyExtra appends the encoding of a value of an unnamed root type (outside Goose).",
            "func jencAnyExtra(b []byte, v any, d uint64) ([]byte, error) {", "\tswitch x := v.(type) {"]
    body += ["\t" + l for l in any_cases(S, ids, [])]
    body += ["\t}", "\t" + nm("encoding a value of a type the codec does not know"), "}", "",
             "// jsonUnmarshalExtra decodes into an unnamed root type (outside Goose).",
             "func jsonUnmarshalExtra(data []byte, v any) error {"]
    uc = unmarshal_cases(S, ids)
    if uc:
        body += ["\tvar err error", "\tswitch p := v.(type) {"] + ["\t" + l for l in uc] + ["\t}"]
    body += ["\t" + nm("decoding into a type the codec does not know"), "}", ""]
    for i in ids:
        body += gen_encoder(S, i) + gen_decoder(S, i)
    return {"json_extra_gen.go": file("!goose", "\n".join(body)),
            "json_extra_goose_gen.go": file("goose", stub_text)}


def model_go(header, pkg):
    """json_model_gen.go: the registration with the encoding/json model (a model build)."""
    return (header.rstrip("\n") + "\n\n//go:build netmodel || goose\n\n" + f"package {pkg}\n\n"
            "import (\n\tjson \"encoding/json\"\n\n\t\"models.lab/jsoncodec\"\n)\n\n"
            "// RegisterJSON registers this program's codec with the encoding/json model (in a model\n"
            "// build: tag netmodel, or goose; json_real_gen.go's RegisterJSON does nothing).\n"
            "func RegisterJSON() {\n"
            "\tjson.SetCodec(&json.Codec{Marshal: jsonMarshal, Unmarshal: jsonUnmarshal, Scan: jsoncodec.Scan})\n"
            "}\n")


def real_go(header, pkg):
    """json_real_gen.go: nothing to register with the real encoding/json."""
    return (header.rstrip("\n") + "\n\n//go:build !netmodel && !goose\n\n" + f"package {pkg}\n\n"
            "// RegisterJSON: the real encoding/json needs no codec.\n"
            "func RegisterJSON() {}\n")
