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
tags (reflect.StructTag.Lookup), the methods named like encoding/json's hooks, and whether it is
encoding/json's RawMessage or Number. No field list is written by hand. The dump is made in the Go
module the codec is generated into (jsongen.py runs it there), so it reads the very types the
program links. `Schema` checks the dump and refuses (JsonRefused, every reason, naming the type and
the field) everything outside the subset; on a refusal no code is emitted.

THE SUBSET (accepted):
  - bool, string, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64 (int and uint
    are 64 bits: the models are for 64-bit targets), named or not;
  - slices of accepted types whose element kind is not uint8 (a []byte, or a slice of any named
    uint8 type, encodes as base64: v2_encode.go:69-71, `v2/arshal_default.go`:330-341);
  - named struct types whose fields are accepted; an unnamed struct type only as a root (its code
    is built outside Goose, which cannot translate a struct type with tags: below);
  - `any` (the empty interface) as a field or element type: encoded by its dynamic type
    (v2_encode.go:175-176), which must be one of the codec's types, a pointer to one, or a basic
    type above; decoding into it is not modelled (it blocks forever);
  - encoding/json.RawMessage (a field, element or root).
  Struct fields: unexported fields are ignored (as encoding/json ignores them, `v2/fields.go`:410-431);
  an exported field's `json` tag is `-` (the field ignored, v2_encode.go:89), or a name followed by
  options: the name empty (the Go field name) or made only of ASCII letters, digits and
  `!#$%()*+-./:;=?@[]^_{|}~` and space (the characters both v1 and v2 accept unquoted and write
  without escaping: v2_encode.go:134-136, `v2/fields.go`:438-445, and none of `<>&`, which are
  HTML-escaped when written: v2_encode.go:62-65); options among `omitempty` and `string` (the
  latter on integer kinds only), each at most once.

REFUSED, by `Schema` (exit status 2, every reason printed, naming the type and field):
float32, float64 (their formatting and parsing are not reproduced); complex, chan, func (an
UnsupportedTypeError, v2_encode.go:178-180), uintptr, unsafe.Pointer; arrays; maps; pointers
other than at the root (a field or element of pointer type: nil handling and allocation on decode
are not reproduced); interfaces with methods; slices of a uint8 kind (base64); embedded fields
(encoding/json's promotion and conflict rules, v2_encode.go:138-162); an unexported field with a
`json` tag other than `-` (v2 reports it, `v2/fields.go`:423-427); a field name with other
characters, non-ASCII, or quoted (`'...'`, v2_encode.go:90-93); tag options other than
`omitempty` and `string`, empty or repeated ones, `string` on a non-integer field; two fields of
a struct with the same JSON name, or names equal ignoring ASCII case (the rules choosing among
them, v2_encode.go:146-157, and case-insensitive matching between them, are not reproduced);
encoding/json.Number; a type that has, or whose pointer has, a method named MarshalJSON,
UnmarshalJSON, MarshalText, UnmarshalText, AppendText, MarshalJSONTo or UnmarshalJSONFrom
(encoding/json calls those: v2_encode.go:37-51, v2_decode.go:40-51) other than RawMessage;
types the codec cannot name (unexported, generic, of package main, of a package with no alias in
the input); Go package aliases or generated names that collide.

THE EMITTED CODE. Marshal (jsonMarshal; jencAny on the argument, by its dynamic type) writes:
  - a nil interface or a nil pointer: `null` (v2_encode.go:172-176); a pointer: its element;
  - bool: `true`/`false`; integers: decimal, `-` for negatives (v2_encode.go:55-57;
    `v2/arshal_default.go`:467-489, strconv.AppendInt/AppendUint); with the `string` option, the
    same in quotes (v2_encode.go:127-132);
  - string: the bytes in quotes (jsoncodec.AppendString), for strings of bytes 0x20..0x7e other
    than `"`, `\\`, `<`, `>`, `&`: real encoding/json writes exactly those bytes for them; any
    other string blocks forever (not modelled: escaping, UTF-8 coercion and HTML escaping, v2_encode.go:60-67,
    are not reproduced);
  - a slice: `null` if nil, else `[`, the elements separated by `,`, `]` (v2_encode.go:69-71);
  - a struct: `{`, then per field in declaration order (`v2/fields.go`:80, index order) that is not
    ignored and not omitted, `"name":` and the value, separated by `,`, then `}` (v2_encode.go:73-82);
    `omitempty` omits false, 0, a nil interface, a slice or string of length 0, never a struct
    (v2_encode.go:84-87; isLegacyEmpty, `v2/arshal_default.go`:1449-1466);
  - RawMessage: `null` if nil (its MarshalJSON, `jsontext/value.go`:234-240), else an error if it is
    not one valid JSON value, else the value without its whitespace outside strings
    (jsoncodec.AppendCompact, which blocks forever, not modelled, on a string with `<`, `>`, `&`, an escape or
    a non-ASCII byte: real encoding/json escapes or rewrites those);
  - no whitespace anywhere; nesting: an array or object inside 10000 others, or a RawMessage whose
    nesting (jsoncodec.Nesting) with the containers around it exceeds 10000, is an error, as the
    encoder's nesting limit (`jsontext` maxNestingDepth; measured: jsoncodec_test.go, TestNesting).
  Any value of another type blocks forever (not modelled; real encoding/json would encode it by
  reflection or return an UnsupportedTypeError).

Unmarshal (the model's Unmarshal first checks that the input is one valid JSON value with only
whitespace around it, jsoncodec.Scan, and returns a syntax error with nothing decoded otherwise, as
the real one, v2_decode.go:91; then jsonUnmarshal) decodes into `*p`, p a non-nil pointer to one of
the codec's types (a nil pointer, or a non-pointer value of one of the codec's types, or nil: an
error, the real InvalidUnmarshalError, v2_decode.go:24-26; anything else blocks forever, not
modelled):
  - null into a slice sets it to nil; null into anything else (bool, string, integer, struct)
    leaves it (v2_decode.go:100-105; `MergeWithLegacySemantics`, `v2/arshal_default.go`:504-509);
  - a value of the wrong kind, or a number out of range or with a fraction or exponent for an
    integer: an error recorded, the target left as it was, decoding goes on and the first error is
    returned (v2_decode.go:93-99; `ReportErrorsWithLegacySemantics`);
  - integers: a JSON number, `-` for signed kinds only, no fraction or exponent, in range
    (`v2/arshal_default.go`:531-554, 632-647); with the `string` option a JSON string holding
    strconv.ParseInt/ParseUint(s, 10, bits) syntax (a `+` or `-` sign for signed kinds, leading
    zeros allowed) or the string "null" (the field left), and nothing else
    (`v2/arshal_default.go`:510-528, 609-627); a string with an escape sequence blocks
    forever (not modelled: the real one unescapes first);
  - strings: a JSON string without escape sequences or non-ASCII bytes (else it blocks forever, not modelled:
    unescaping and invalid UTF-8 replacement are not reproduced);
  - slices: a JSON array; `[]` gives a new empty slice (v2_decode.go:75-76); a non-empty array into
    a nil slice gives a new slice of the decoded elements (an element of the wrong kind is
    appended as its zero value); a non-empty array into a non-nil slice blocks forever (not modelled: the
    real one decodes into the existing elements in place, v2_decode.go:71-74);
  - structs: a JSON object; each member's key matched to the field of that JSON name, else to the
    one equal to it ignoring ASCII case (v2_decode.go:55-59; `v2/fields.go`:367-386 with
    `MatchCaseSensitiveDelimiter`: strings.EqualFold, which for the ASCII keys the codec accepts is
    ASCII case folding); its value decoded into that field (merging: the other fields stay; a repeated
    key decodes again, so the last wins); members matching no field skipped; a key with an escape
    or a non-ASCII byte blocks forever (not modelled);
  - RawMessage: a copy of the value's bytes (without the whitespace around it), also for null
    (its UnmarshalJSON, `jsontext/value.go`:242-251, reusing the target's storage);
  - `any`: blocks forever (not modelled).

WHERE THE CLAIM STOPS (documented deviations, outside "behaves as encoding/json"):
  - error values: only error-or-not is the real one's (*jsoncodec.Error, not *SyntaxError,
    *UnmarshalTypeError, *InvalidUnmarshalError, ...). A program that inspects an error's type or
    message observes a difference.
  - what comes with an error: after an Unmarshal error the target's contents are what the codec
    left (the real one says the fields after the problematic one are not guaranteed to be
    decoded, v2_decode.go:97-99); the differential tests compare them too, but the claim does not
    rely on it.
  - slice capacities and aliasing: decoded slices are built by append; the real one sizes them
    otherwise; lengths and contents agree.
  - only the API the encoding/json model covers (`models/encoding/json`, its doc): Marshal,
    Unmarshal, Valid, Encoder.Encode, Decoder.Decode and their companions; MarshalIndent, Indent,
    Compact, Token-level decoding and DisallowUnknownFields block forever there.

The evidence (untrusted, jsongen.py --help): the generator's differential test over random Go
types of the subset (`models/internal/jsongenrand`), the regression test generated beside each
codec (json_gen_test.go), and the stream tests of the model (`models/internal/jsonstreamtest`).
"""

import re


class JsonRefused(Exception):
    def __init__(self, reasons):
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


class Field:
    """An encoded struct field: Go name, JSON name, type id, options."""

    def __init__(self, go, json_name, typ, omitempty, quoted):
        self.go, self.json, self.typ, self.omitempty, self.quoted = go, json_name, typ, omitempty, quoted


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
        self.fields = {}      # struct id -> [Field]
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
        hooks = [m for m in HOOKS if m in e["methods"] or m in e["ptr_methods"]]
        if hooks:
            return self.refuse(where, f"{e['string']} has method {hooks[0]} (encoding/json calls it; "
                                      "outside the subset)")
        if e["name"] and e["pkg_path"] and not self.nameable(e, where):
            return False
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
            self.ok[i] = True     # recursion through slices reaches it again
            good = self.struct_fields(i, stack)
            if not good:
                del self.ok[i]
            return good
        if k == "ptr":
            return self.refuse(where, f"{e['string']}: a pointer (outside the subset but at the root)")
        return self.refuse(where, f"kind {k} ({e['string']}) is outside the subset")

    def parse_tag(self, f, where):
        """(ignored, json name, omitempty, quoted) of an exported field, or None (refused)."""
        tag = f["tag"]
        if tag == "-":
            return True, None, False, False
        name, _, opts = tag.partition(",")
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
        return False, name, omitempty, quoted

    def struct_fields(self, i, stack):
        e = self.t[i]
        good = True
        fields = []
        for f in e["fields"]:
            fw = f"{e['string']}.{f['name']}"
            if f["embedded"]:
                good = self.refuse(fw, "an embedded field (encoding/json's promotion rules are not "
                                       "reproduced)")
                continue
            if not f["exported"]:
                if f["has_tag"] and f["tag"] != "-":
                    good = self.refuse(fw, f"an unexported field with tag json:{f['tag']!r}")
                continue
            p = self.parse_tag(f, fw)
            if p is None:
                good = False
                continue
            ignored, name, omitempty, quoted = p
            if ignored:
                continue
            ft = self.t[f["type"]]
            if quoted and (ft["kind"] not in INTS or ft["raw_message"]):
                good = self.refuse(fw, f"the string option on a {ft['kind']} field (reproduced for "
                                       "integers only)")
                continue
            if not self.check(f["type"], f"{fw} ({ft['string']})", "field", stack + (i,)):
                good = False
                continue
            fields.append(Field(f["name"], name, f["type"], omitempty, quoted))
        names = [f.json for f in fields]
        if len(set(names)) != len(names):
            good = self.refuse(e["string"], "two fields with the same JSON name")
        elif len({n.lower() for n in names}) != len(names):
            good = self.refuse(e["string"], "two fields' JSON names are equal ignoring case")
        self.fields[i] = fields
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
        if e["kind"] == "slice" and not e["raw_message"]:
            self.collect(e["elem"], seen)
        if e["kind"] == "struct":
            for f in self.fields[i]:
                self.collect(f.typ, seen)
        self.closure.append(i)

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
        raise AssertionError(f"no spelling for {e['string']}")

    def ident(self, i):
        e = self.t[i]
        if i in self.unnamed:
            return f"root{sorted(self.unnamed).index(i)}"
        if e["raw_message"]:
            return "RawMessage"
        if e["kind"] == "slice" and not e["name"]:
            return "S_" + self.ident(e["elem"])
        return re.sub(r"[^A-Za-z0-9]", "_", self.go(i))

    def kind(self, i):
        e = self.t[i]
        if e["raw_message"]:
            return "raw"
        if e["kind"] in INTS:
            return "int"
        return e["kind"]          # bool string slice struct interface

    def goose(self, i):
        """Whether type i's code is in json_gen.go (Goose's), not the !goose file."""
        return i not in self.unnamed

    def uses_json(self):
        return any(self.t[i]["raw_message"] for i in self.closure)


# ---------------------------------------------------------------------------------------------
# The emitter

def nm(msg):
    """The statement where the codec does not model encoding/json: it blocks forever (an empty
    select, never a panic: a program can recover a panic, which would add behaviors encoding/json
    does not have; blocking only removes behaviors, models/README.md)."""
    return "select {} // MODEL: not modelled (stuck): json model: " + msg


def int_append(S, i, expr, quoted):
    signed, _ = INTS[S.t[i]["kind"]]
    fn = ("AppendQuotedInt" if quoted else "AppendInt") if signed else \
         ("AppendQuotedUint" if quoted else "AppendUint")
    conv = "int64" if signed else "uint64"
    return f"b = jsoncodec.{fn}(b, {conv}({expr}))"


def enc_value(S, i, expr, quoted, d):
    """Go statements appending the encoding of expr (of type i) to b at depth d (an expression);
    they may return an error."""
    k = S.kind(i)
    if k == "int":
        return [int_append(S, i, expr, quoted)]
    if k == "string":
        return [f"b = jsoncodec.AppendString(b, string({expr}))"]
    if k == "bool":
        return [f"b = jsoncodec.AppendBool(b, bool({expr}))"]
    fn = {"raw": "jencRaw", "interface": "jencAny"}.get(k, f"jenc_{S.idents[i]}")
    return [f"b, err = {fn}(b, {expr}, {d})", "if err != nil {", "\treturn b, err", "}"]


def empty_test(S, i, expr):
    """A Go condition: expr (of type i) is not empty for omitempty (None: never empty)."""
    k = S.kind(i)
    if k == "int":
        return f"{expr} != 0"
    if k == "bool":
        return f"bool({expr})"
    if k in ("string", "slice", "raw"):
        return f"len({expr}) != 0"
    if k == "interface":
        return f"{expr} != nil"
    return None


def gen_encoder(S, i):
    g, I, k = S.go(i), S.idents[i], S.kind(i)
    out = [f"// jenc_{I} appends the encoding of a {g} inside d arrays and objects.",
           f"func jenc_{I}(b []byte, v {g}, d uint64) ([]byte, error) {{"]
    if k in ("int", "string", "bool"):
        body = enc_value(S, i, "v", False, "d") + ["return b, nil"]
    elif k == "raw":
        body = ["return jencRaw(b, v, d)"]
    elif k == "slice":
        body = ["if v == nil {", "\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "}",
                "if d >= jsoncodec.MaxDepth {", "\treturn b, jsonDepthErr()", "}",
                "var err error", "_ = err", "b = append(b, '[')", "for i, x := range v {",
                "\tif i > 0 {", "\t\tb = append(b, ',')", "\t}"]
        body += ["\t" + l for l in enc_value(S, S.t[i]["elem"], "x", False, "d+1")]
        body += ["}", "return append(b, ']'), nil"]
    else:
        fields = S.fields[i]
        dyn = any(f.omitempty for f in fields)
        body = ["if d >= jsoncodec.MaxDepth {", "\treturn b, jsonDepthErr()", "}",
                "var err error", "_ = err", "b = append(b, '{')"]
        if dyn:
            body += ["first := true", "_ = first"]
        for n, f in enumerate(fields):
            key = go_str('"' + f.json + '":')
            val = enc_value(S, f.typ, f"v.{f.go}", f.quoted, "d+1")
            if dyn:
                stmts = ["if !first {", "\tb = append(b, ',')", "}", "first = false",
                         f"b = jsoncodec.AppendRaw(b, {key})"] + val
                cond = empty_test(S, f.typ, f"v.{f.go}") if f.omitempty else None
                if cond is None:
                    body += stmts
                else:
                    body += [f"if {cond} {{"] + ["\t" + l for l in stmts] + ["}"]
            else:
                sep = go_str(("," if n > 0 else "") + '"' + f.json + '":')
                body += [f"b = jsoncodec.AppendRaw(b, {sep})"] + val
        body += ["return append(b, '}'), nil"]
    return out + ["\t" + l for l in body] + ["}", ""]


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


def dec_value(S, i, quoted, target):
    """Go statements decoding the value at b[i:] into target (of type i), setting k."""
    k = S.kind(i)
    if k in ("int", "string", "bool"):
        return scalar_dec(S, i, quoted, target)
    if k == "interface":
        return [nm("decoding into an interface (any)")]
    if k == "raw":
        return [f"k = jdecRaw(b, i, &{target})"]
    return [f"k = jdec_{S.idents[i]}(b, i, &{target}, e)"]


def gen_decoder(S, i):
    g, I, k = S.go(i), S.idents[i], S.kind(i)
    out = [f"// jdec_{I} decodes the value at b[i:] (valid JSON, after whitespace) into *p as real",
           "// encoding/json does; the first error is kept in *e. It returns the index after the value.",
           f"func jdec_{I}(b []byte, i uint64, p *{g}, e *error) uint64 {{"]
    if k in ("int", "string", "bool"):
        body = ["var k uint64"] + scalar_dec(S, i, False, "*p") + ["return k"]
    elif k == "raw":
        body = ["return jdecRaw(b, i, p)"]
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
    if k == "struct":
        out += [f"// jdecMember_{I} decodes the value of member key at b[i:] into its field of *p (the",
                "// field of that JSON name, else the one whose name equals it ignoring ASCII case; else",
                "// the value is skipped), as real encoding/json does; it returns the index after the value.",
                f"func jdecMember_{I}(b []byte, i uint64, key string, p *{g}, e *error) uint64 {{"]
        for mode in ("exact", "fold"):
            for f in S.fields[i]:
                cond = (f"key == {go_str(f.json)}" if mode == "exact"
                        else f"jsoncodec.FoldEq(key, {go_str(f.json)})")
                if S.kind(f.typ) == "interface":
                    out += [f"\tif {cond} {{", "\t\t" + nm("decoding into an interface (any)"), "\t}"]
                    continue
                out += [f"\tif {cond} {{", "\t\tvar k uint64"]
                out += ["\t\t" + l for l in dec_value(S, f.typ, f.quoted, f"p.{f.go}")]
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
        out += [f"case {g}:", f"\treturn jenc_{I}(b, x, d)", f"case *{g}:", "\tif x == nil {",
                "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "\t}", f"\treturn jenc_{I}(b, *x, d)"]
    return out


def unmarshal_cases(S, ids):
    out = []
    for i in ids:
        g, I = S.go(i), S.idents[i]
        if S.kind(i) == "interface":
            continue
        out += [f"case *{g}:", "\tif p == nil {",
                f"\t\treturn &jsoncodec.Error{{Msg: {go_str('Unmarshal(nil *' + g + ')')}}}", "\t}",
                f"\tjdec_{I}(data, 0, p, &err)", "\treturn err",
                f"case {g}:", f"\treturn &jsoncodec.Error{{Msg: {go_str('Unmarshal(non-pointer ' + g + ')')}}}"]
    return out


def imports(S, text, extra=()):
    text = "\n".join(l for l in text.split("\n") if not l.lstrip().startswith("//"))
    imps = list(extra)
    if re.search(r"\bjson\.", text):
        imps.insert(0, '\tjson "encoding/json"')
    if re.search(r"\bjsoncodec\.", text):
        imps.append('\t"models.lab/jsoncodec"')
    for p, a in sorted(S.alias.items(), key=lambda x: x[1]):
        if p != "encoding/json" and re.search(r"\b" + re.escape(a) + r"\.", text):
            imps.append(f'\t{a} "{p}"')
    if not [l for l in imps if l]:
        return []
    return ["import ("] + imps + [")", ""]


def codec_go(S, header, pkg):
    """json_gen.go: the codec of the named types (Goose's)."""
    ids = [i for i in S.closure if S.goose(i)]
    body = [
        "// jsonMarshal is the codec's Marshal: v's encoding as real encoding/json's Marshal writes it,",
        "// for v nil, a value of one of the codec's types or a basic type, or a pointer to one; any",
        "// other v blocks forever (not modelled).",
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
        "// types, or nil; any other v blocks forever (not modelled).",
        "func jsonUnmarshal(data []byte, v any) error {"]
    uc = unmarshal_cases(S, ids)
    if uc:
        body += ["\tvar err error", "\tswitch p := v.(type) {"] + ["\t" + l for l in uc] + ["\t}"]
    body += ["\tif v == nil {", "\t\treturn &jsoncodec.Error{Msg: \"Unmarshal(nil)\"}", "\t}",
             "\treturn jsonUnmarshalExtra(data, v)", "}", "",
             "// jencAny appends the encoding of v by its dynamic type (nil: null) inside d arrays and",
             "// objects; a type the codec does not know blocks forever (not modelled).",
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
    if S.uses_json():
        body += [
            "// jencRaw appends a RawMessage as real encoding/json does: null if nil (its MarshalJSON),",
            "// else an error if it is not one valid JSON value or nests too deep inside d arrays and",
            "// objects, else the value compacted (jsoncodec.AppendCompact).",
            "func jencRaw(b []byte, v json.RawMessage, d uint64) ([]byte, error) {",
            "\tif v == nil {",
            "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil",
            "\t}",
            "\tif !jsoncodec.Valid(v) {",
            "\t\treturn b, &jsoncodec.Error{Msg: \"a RawMessage that is not one valid JSON value\"}",
            "\t}",
            "\tif d+jsoncodec.Nesting(v) > jsoncodec.MaxDepth {",
            "\t\treturn b, jsonDepthErr()",
            "\t}",
            "\tb2, _ := jsoncodec.AppendCompact(b, v)",
            "\treturn b2, nil",
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
        "// not know blocks forever (not modelled).",
        "func jencAnyExtra(b []byte, v any, d uint64) ([]byte, error) {",
        "\t" + nm("encoding a value of a type the codec does not know"),
        "}",
        "",
        "// jsonUnmarshalExtra: decoding into a type the codec does not know blocks forever (not modelled).",
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
