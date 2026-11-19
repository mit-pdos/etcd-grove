#!/usr/bin/env python3
"""jsongen: an encoding/json codec, plain Go code per type, from a [json] table.

A model of encoding/json replaces reflection by a codec the program registers: an encoder and a
decoder for exactly the listed Go types, and the JSON scanner (`netmodels.lab/jsoncodec.Scan`,
`netmodels/`, translated into the part `Net/`). This script generates the codec, and the Go tests
that check the trusted claims against real encoding/json: the listed structure of each type is the
Go type's (reflection: field names, types, tags), the codec's encoding of random values is real
encoding/json's byte for byte, its decoding of the encodings of every listed type into every
decodable listed type (fresh and pre-filled targets), and of mutations of them (keys in other
cases, unknown and repeated keys, values of other kinds, null, whitespace, numbers out of range,
truncations), gives real encoding/json's value and error-or-not, and the scanner agrees with
real encoding/json on what is valid and where a streamed value ends. Ported from dsverify-lab's
`harness/kitgen/jsongen.py` (`348a866`), which kitgen called as a module: the command line below is
new, what it generates unchanged but jsoncodec's import path, the messages, and the registration
files made optional (`--register`).

Use:

    etc/jsongen.py SECTION.toml OUTDIR --pkg NAME [--register] [--check]

writes into the Go package directory OUTDIR (package NAME, which must import the listed types'
packages) `json_gen.go` (the codec: `jsonMarshal`, `jsonUnmarshal`), `json_extra_gen.go` (and
`json_extra_goose_gen.go` when some type is unnamed: `goose = false`) and `json_gen_test.go` (its
tests against real encoding/json); with `--register` also `json_model_gen.go`/`json_real_gen.go`
(`registerJSON()`: the codec registered with the model of encoding/json, `json.SetCodec`, in a
model build (tag `rpcmodel` or `goose`); nothing in a real build). `--check` writes nothing and
exits 1 if a file differs. Example: `netmodels/internal/jsondifftest/`.

The [json] table (in any toml file):

    [json]
    imports = { events = "github.com/x/y/events", ... }   # Go package aliases used below
    [json.types]
    "events.EventType" = { basic = "uint8" }               # a named basic type
    "events.Request" = { struct = [["ID", "uint64", "id,string"], ["Op", "string", "op"]] }
    "log.Logs" = { slice = "log.Log", marshal = "value", unmarshal = "pointer" }
    "[]log.Log" = { slice = "log.Log" }
    "events.Event" = { struct = [["Type", "events.EventType", "@type"], ["Data", "any", "data"]],
                       decode = false }
    "frame" = { go_type = "struct { ... }", struct = [...], goose = false }   # an unnamed type

A field's type is `uint64`, `uint32`, `uint8`, `string`, `bool`, `any` (encoded by its dynamic
type, which must be a listed type or a pointer to one, or nil; not decodable), `json.RawMessage`
(Go's: a Marshaler and Unmarshaler) or a listed type. A field's tag is its JSON name, with
`,string` for an unsigned integer field. `marshal = "value"`: the type has a MarshalJSON method on
its value, which the codec calls (as encoding/json does) and whose output it compacts;
`unmarshal = "pointer"`: an UnmarshalJSON method on its pointer, which the codec calls with the
value's bytes. `encode = false` / `decode = false`: the codec panics on encoding / decoding the
type. `goose = false` (with `go_type`, the type's Go spelling): an unnamed type Goose cannot
translate (a struct type with tags); its code is built only outside Goose (build tag !goose), so
in the theorem the codec panics on it.

What the codec covers, and where it panics instead (stricter than Go, never more permissive):
strings must be plain (jsoncodec's package doc); decoding into a non-nil slice panics (Go reuses
its elements); decoding into a type not listed, or into `any`, panics.
"""

import re

UINTS = {"uint64": "18446744073709551615", "uint32": "4294967295", "uint8": "255"}
BASIC = set(UINTS) | {"string", "bool"}


class JsonError(Exception):
    pass


def ident(name):
    """A Go identifier for a type name: events.Request -> events_Request; []log.Log -> S_log_Log."""
    return re.sub(r"[^A-Za-z0-9]", "_", name.replace("[]", "S_").replace("*", "P_"))


class Types:
    def __init__(self, js):
        self.imports = dict(js.get("imports", {}))
        self.decl = js.get("types", {})
        if not self.decl:
            raise JsonError("[json.types] is empty")
        self.t = {}
        for n, d in self.decl.items():
            self.t[n] = self.parse_decl(n, d)
        for n, d in self.t.items():
            for f in d.get("fields", []):
                self.check_field_type(n, f)
            if d["kind"] == "slice":
                self.check_type(n, d["elem"])
        self.names = list(self.t)

    def go(self, n):
        """The Go spelling of a listed type."""
        return self.t[n].get("go_type", n)

    def parse_decl(self, n, d):
        if not isinstance(d, dict):
            raise JsonError(f"type {n}: a table")
        allowed = {"basic", "struct", "slice", "marshal", "unmarshal", "encode", "decode", "goose", "go_type"}
        if set(d) - allowed:
            raise JsonError(f"type {n}: unknown keys {sorted(set(d) - allowed)}")
        kinds = [k for k in ("basic", "struct", "slice") if k in d]
        if len(kinds) != 1:
            raise JsonError(f"type {n}: one of basic, struct, slice")
        goose = d.get("goose", True)
        if not goose and "go_type" not in d:
            raise JsonError(f"type {n}: goose = false needs go_type")
        if goose and not (re.fullmatch(r"\w+\.\w+", n) or re.fullmatch(r"\[\]\w+\.\w+", n)):
            raise JsonError(f"type {n}: pkg.T or []pkg.T")
        m = re.fullmatch(r"(?:\[\])?(\w+)\.\w+", n)
        if goose and m.group(1) not in self.imports:
            raise JsonError(f"type {n}: package {m.group(1)} not in [json].imports")
        if not goose and not re.fullmatch(r"\w+", n):
            raise JsonError(f"type {n}: an unnamed type's key is an identifier")
        r = {"kind": kinds[0], "encode": d.get("encode", True), "decode": d.get("decode", True),
             "goose": goose, "marshal": d.get("marshal"), "unmarshal": d.get("unmarshal")}
        if "go_type" in d:
            r["go_type"] = d["go_type"]
        if r["marshal"] not in (None, "value"):
            raise JsonError(f"type {n}: marshal = \"value\" (a MarshalJSON on the value)")
        if r["unmarshal"] not in (None, "pointer"):
            raise JsonError(f"type {n}: unmarshal = \"pointer\" (an UnmarshalJSON on the pointer)")
        if kinds[0] == "basic":
            if d["basic"] not in UINTS:
                raise JsonError(f"type {n}: basic = one of {sorted(UINTS)}")
            r["basic"] = d["basic"]
        elif kinds[0] == "slice":
            if n.startswith("[]") and n[2:] != d["slice"]:
                raise JsonError(f"type {n}: slice = {n[2:]!r}")
            r["elem"] = d["slice"]
        else:
            fields = []
            for f in d["struct"]:
                if len(f) != 3 or not re.fullmatch(r"[A-Z]\w*", f[0]):
                    raise JsonError(f"type {n}: field {f!r}: [Name, type, tag]")
                tag = f[2]
                parts = tag.split(",")
                if len(parts) > 2 or (len(parts) == 2 and parts[1] != "string") or not parts[0]:
                    raise JsonError(f"type {n}.{f[0]}: tag {tag!r}: a name, optionally ,string")
                if not re.fullmatch(r"[A-Za-z0-9_@\-]+", parts[0]):
                    raise JsonError(f"type {n}.{f[0]}: name {parts[0]!r}: plain characters only")
                quoted = len(parts) == 2
                fields.append({"name": f[0], "type": f[1], "json": parts[0], "quoted": quoted})
            lows = [f["json"].lower() for f in fields]
            if len(set(lows)) != len(lows):
                raise JsonError(f"type {n}: two fields' JSON names fold to the same name")
            r["fields"] = fields
        return r

    def check_type(self, where, t):
        if t in BASIC or t in ("any", "json.RawMessage"):
            return
        if t not in self.t:
            raise JsonError(f"{where}: type {t!r} is not listed")
        if not self.t[t]["goose"]:
            raise JsonError(f"{where}: an unnamed type cannot be a field's or an element's")

    def check_field_type(self, n, f):
        self.check_type(f"{n}.{f['name']}", f["type"])
        if f["quoted"] and self.base(f["type"]) not in UINTS:
            raise JsonError(f"{n}.{f['name']}: ,string on a non-unsigned field")

    def base(self, t):
        """A field type's basic kind (for named basics), else the type itself."""
        if t in self.t and self.t[t]["kind"] == "basic":
            return self.t[t]["basic"]
        return t

    def enc_types(self):
        return [n for n in self.names if self.t[n]["encode"]]

    def dec_types(self):
        return [n for n in self.names if self.t[n]["decode"]]


# ---------------------------------------------------------------------------------------------
# The codec


def go_imports(T, extra=()):
    lines = [f'\t{a} "{p}"' for a, p in sorted(T.imports.items())]
    return lines


def needs_json_pkg(T):
    """Whether the codec's Go code names package encoding/json (json.RawMessage)."""
    for d in T.t.values():
        for f in d.get("fields", []):
            if f["type"] == "json.RawMessage":
                return True
    return False


def enc_value(T, t, expr, b="b"):
    """Go statements appending the encoding of expr (of field type t) to b; may return an error."""
    bt = T.base(t)
    if t in T.t and T.t[t]["kind"] != "basic":
        return [f"{b}, err = jenc_{ident(t)}({b}, {expr})", "if err != nil {", "\treturn b, err", "}"]
    if t == "json.RawMessage":
        return [f"{b}, err = jencMarshaler({b}, {expr})", "if err != nil {", "\treturn b, err", "}"]
    if t == "any":
        return [f"{b}, err = jencAny({b}, {expr})", "if err != nil {", "\treturn b, err", "}"]
    if bt in UINTS:
        return [f"{b} = jsoncodec.AppendUint({b}, uint64({expr}))"]
    if bt == "string":
        return [f"{b} = jsoncodec.AppendString({b}, {expr})"]
    if bt == "bool":
        return [f"{b} = jsoncodec.AppendBool({b}, {expr})"]
    raise JsonError(f"no encoder for {t}")


def gen_encoder(T, n):
    d = T.t[n]
    g = T.go(n)
    out = [f"// jenc_{ident(n)} appends the encoding of a {n} (real encoding/json's).",
           f"func jenc_{ident(n)}(b []byte, v {g}) ([]byte, error) {{"]
    body = []
    if d["marshal"] == "value":
        body += ["raw, err := v.MarshalJSON()", "if err != nil {",
                 "\treturn b, &jsoncodec.Error{Msg: \"a MarshalJSON method's error\"}", "}",
                 "b2, ok := jsoncodec.AppendCompact(b, raw)", "if !ok {",
                 "\treturn b, &jsoncodec.Error{Msg: \"a MarshalJSON method's invalid output\"}", "}",
                 "return b2, nil"]
    elif d["kind"] == "basic":
        body += ["return jsoncodec.AppendUint(b, uint64(v)), nil"]
    elif d["kind"] == "slice":
        body += ["if v == nil {", "\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "}",
                 "var err error", "b = append(b, '[')", "for i, x := range v {",
                 "\tif i > 0 {", "\t\tb = append(b, ',')", "\t}"]
        body += ["\t" + l for l in enc_value(T, d["elem"], "x")]
        body += ["}", "return append(b, ']'), nil"]
    else:
        body += ["var err error", "_ = err", "b = append(b, '{')"]
        for i, f in enumerate(d["fields"]):
            body.append(f"b = jsoncodec.AppendRaw(b, {go_str(('' if i == 0 else ',') + chr(34) + f['json'] + chr(34) + ':')})")
            if f["quoted"]:
                body.append(f"b = jsoncodec.AppendQuotedUint(b, uint64(v.{f['name']}))")
            else:
                body += enc_value(T, f["type"], f"v.{f['name']}")
        body += ["return append(b, '}'), nil"]
    out += ["\t" + l for l in body] + ["}", ""]
    return out


def go_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def dec_field_value(T, t, quoted, target, conv):
    """Go statements decoding the value at b[i:] into the field `target` (an addressable
    expression of type t): set k (the index after the value)."""
    bt = T.base(t)
    if quoted:
        return [f"x, st, k1 := jsoncodec.QuotedUint(b, i, {UINTS[bt]})", "k = k1",
                "if st == jsoncodec.Set {", f"\t{target} = {conv}(x)", "} else if st == jsoncodec.TypeErr {",
                "\tjsonSetErr(e)", "}"]
    if t in T.t and T.t[t]["kind"] != "basic":
        d = T.t[t]
        if d["unmarshal"] == "pointer":
            return [f"k = jdecUnmarshaler(b, i, &{target}, e)"]
        if not d["decode"]:
            return [f"panic({go_str('json model: decoding into ' + t + ' (not decodable)')})"]
        return [f"k = jdec_{ident(t)}(b, i, &{target}, e)"]
    if t == "json.RawMessage":
        return [f"k = jdecUnmarshaler(b, i, &{target}, e)"]
    if t == "any":
        return ["panic(\"json model: decoding into an interface field\")"]
    if bt in UINTS:
        return [f"x, st, k1 := jsoncodec.Uint(b, i, {UINTS[bt]})", "k = k1",
                "if st == jsoncodec.Set {", f"\t{target} = {conv}(x)", "} else if st == jsoncodec.TypeErr {",
                "\tjsonSetErr(e)", "}"]
    if bt == "string":
        return ["x, st, k1 := jsoncodec.String(b, i)", "k = k1",
                "if st == jsoncodec.Set {", f"\t{target} = {conv}(x)", "} else if st == jsoncodec.TypeErr {",
                "\tjsonSetErr(e)", "}"]
    if bt == "bool":
        return ["x, st, k1 := jsoncodec.Bool(b, i)", "k = k1",
                "if st == jsoncodec.Set {", f"\t{target} = {conv}(x)", "} else if st == jsoncodec.TypeErr {",
                "\tjsonSetErr(e)", "}"]
    raise JsonError(f"no decoder for {t}")


def conv_of(T, t):
    return T.go(t) if (t in T.t and T.t[t]["kind"] == "basic") else (t if t in BASIC else "")


def gen_decoder(T, n):
    d = T.t[n]
    g = T.go(n)
    I = ident(n)
    out = [f"// jdec_{I} decodes the value at b[i:] (valid JSON, after whitespace) into *p as real",
           f"// encoding/json does; the first error is kept in *e. It returns the index after the value.",
           f"func jdec_{I}(b []byte, i uint64, p *{g}, e *error) uint64 {{"]
    body = []
    if d["unmarshal"] == "pointer":
        body += ["return jdecUnmarshaler(b, i, p, e)"]
    elif d["kind"] == "basic":
        body += [f"x, st, k := jsoncodec.Uint(b, i, {UINTS[d['basic']]})", "if st == jsoncodec.Set {",
                 f"\t*p = {g}(x)", "} else if st == jsoncodec.TypeErr {", "\tjsonSetErr(e)", "}", "return k"]
    elif d["kind"] == "slice":
        et = d["elem"]
        body += ["j, c := jsoncodec.At(b, i)", "if c == 'n' {", "\t*p = nil", "\treturn j + 4", "}",
                 "if c != '[' {", "\tjsonSetErr(e)", "\treturn jsoncodec.ValueEnd(b, j)", "}",
                 "if *p != nil {", "\tpanic(\"json model: decoding into a non-nil slice\")", "}",
                 f"s := make({g}, 0)", "empty, k := jsoncodec.Empty(b, j)", "if empty {", "\t*p = s",
                 "\treturn k", "}", "for {", f"\tvar x {T.go(et)}", "\tk1 := k"]
        body += ["\t" + l for l in dec_field_value(T, et, False, "x", conv_of(T, et))]
        body += ["\ts = append(s, x)", "\tmore, k2 := jsoncodec.Next(b, k)", "\tk = k2", "\t_ = k1",
                 "\tif !more {", "\t\t*p = s", "\t\treturn k", "\t}", "}"]
        body = [l.replace("\tk1 := k", "\ti := k") if l == "\tk1 := k" else l for l in body]
        body = [l for l in body if l != "\t_ = k1"]
    else:
        body += ["j, c := jsoncodec.At(b, i)", "if c == 'n' {", "\treturn j + 4", "}",
                 "if c != '{' {", "\tjsonSetErr(e)", "\treturn jsoncodec.ValueEnd(b, j)", "}",
                 "empty, k := jsoncodec.Empty(b, j)", "if empty {", "\treturn k", "}", "for {",
                 "\tkey, v := jsoncodec.Member(b, k)",
                 f"\tk = jdecMember_{I}(b, v, key, p, e)",
                 "\tmore, k2 := jsoncodec.Next(b, k)", "\tk = k2", "\tif !more {", "\t\treturn k", "\t}", "}"]
    out += ["\t" + l for l in body] + ["}", ""]
    if d["kind"] == "struct" and d["unmarshal"] is None:
        out += [f"// jdecMember_{I} decodes the value of member key at b[i:] into its field of *p (the",
                "// field named key exactly, else the one whose name equals it ignoring case; else the",
                "// value is skipped), as real encoding/json does; it returns the index after the value.",
                f"func jdecMember_{I}(b []byte, i uint64, key string, p *{g}, e *error) uint64 {{"]
        fields = d["fields"]
        for mode in ("exact", "fold"):
            for f in fields:
                cond = (f"key == {go_str(f['json'])}" if mode == "exact"
                        else f"jsoncodec.FoldEq(key, {go_str(f['json'])})")
                out += [f"\tif {cond} {{", "\t\tvar k uint64"]
                out += ["\t\t" + l for l in dec_field_value(T, f["type"], f["quoted"], f"p.{f['name']}",
                                                         conv_of(T, f["type"]))]
                out += ["\t\treturn k", "\t}"]
        out += ["\treturn jsoncodec.ValueEnd(b, jsoncodec.SkipSpace(b, i))", "}", ""]
    return out


def gen_codec_go(T, header, go_name, goose):
    """The codec (json_gen.go when goose, json_extra_gen.go for the unnamed types otherwise)."""
    names = [n for n in T.names if T.t[n]["goose"] == goose]
    o = [header, f"package {go_name}", ""]
    imps = []
    body_text = []
    if goose:
        body_text += [
            "// jsonSetErr records a decoding error (real encoding/json keeps decoding and returns the",
            "// first error).",
            "func jsonSetErr(e *error) {",
            "\tif *e == nil {",
            "\t\t*e = &jsoncodec.Error{Msg: \"a value of the wrong kind or out of range\"}",
            "\t}",
            "}",
            "",
            "// jsonUnmarshalerOf is the interface of an UnmarshalJSON method.",
            "type jsonUnmarshalerOf interface {",
            "\tUnmarshalJSON([]byte) error",
            "}",
            "",
            "// jsonMarshalerOf is the interface of a MarshalJSON method.",
            "type jsonMarshalerOf interface {",
            "\tMarshalJSON() ([]byte, error)",
            "}",
            "",
            "// jdecUnmarshaler passes the value at b[i:] (its bytes, without the whitespace around it) to",
            "// u's UnmarshalJSON, as real encoding/json does (also for null); its error is kept in *e.",
            "func jdecUnmarshaler(b []byte, i uint64, u jsonUnmarshalerOf, e *error) uint64 {",
            "\tj := jsoncodec.SkipSpace(b, i)",
            "\tk := jsoncodec.ValueEnd(b, j)",
            "\tif err := u.UnmarshalJSON(b[j:k]); err != nil {",
            "\t\tif *e == nil {",
            "\t\t\t*e = err",
            "\t\t}",
            "\t}",
            "\treturn k",
            "}",
            "",
            "// jencMarshaler appends m's MarshalJSON output, compacted (real encoding/json's), or an error.",
            "func jencMarshaler(b []byte, m jsonMarshalerOf) ([]byte, error) {",
            "\traw, err := m.MarshalJSON()",
            "\tif err != nil {",
            "\t\treturn b, &jsoncodec.Error{Msg: \"a MarshalJSON method's error\"}",
            "\t}",
            "\tb2, ok := jsoncodec.AppendCompact(b, raw)",
            "\tif !ok {",
            "\t\treturn b, &jsoncodec.Error{Msg: \"a MarshalJSON method's invalid output\"}",
            "\t}",
            "\treturn b2, nil",
            "}",
            "",
        ]
        # jencAny: the dynamic types an `any` field may hold
        body_text += ["// jencAny appends the encoding of v by its dynamic type: nil, a listed type or a pointer to",
                      "// one (real encoding/json's); it panics for any other.",
                      "func jencAny(b []byte, v interface{}) ([]byte, error) {",
                      "\tif v == nil {", "\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil", "\t}",
                      "\tswitch x := v.(type) {"]
        for n in T.enc_types():
            if not T.t[n]["goose"]:
                continue
            g = T.go(n)
            body_text += [f"\tcase {g}:", f"\t\treturn jenc_{ident(n)}(b, x)",
                          f"\tcase *{g}:", "\t\tif x == nil {", "\t\t\treturn jsoncodec.AppendRaw(b, \"null\"), nil",
                          "\t\t}", f"\t\treturn jenc_{ident(n)}(b, *x)"]
        body_text += ["\t}", "\tpanic(\"json model: encoding a type not listed in the [json] table\")", "}", ""]
        # top level
        body_text += ["// jsonMarshal is the codec's Marshal: v's encoding, for v of a listed type or a pointer",
                      "// to one (or nil); it panics for any other.",
                      "func jsonMarshal(v interface{}) ([]byte, error) {",
                      "\tb, err := jencAny(make([]byte, 0), v)", "\tif err != nil {", "\t\treturn nil, err", "\t}",
                      "\treturn b, nil", "}", ""]
        body_text += ["// jsonUnmarshal is the codec's Unmarshal: decodes data (one valid JSON value) into v, a",
                      "// non-nil pointer to a decodable listed type; real encoding/json's error for a nil",
                      "// pointer or a non-pointer of a listed type; it panics for any other v.",
                      "func jsonUnmarshal(data []byte, v interface{}) error {",
                      "\tvar err error",
                      "\tswitch p := v.(type) {"]
        for n in T.names:
            if not T.t[n]["goose"]:
                continue
            g = T.go(n)
            if T.t[n]["decode"]:
                body_text += [f"\tcase *{g}:", "\t\tif p == nil {",
                              "\t\t\treturn &jsoncodec.Error{Msg: \"Unmarshal(nil pointer)\"}", "\t\t}",
                              f"\t\tjdec_{ident(n)}(data, 0, p, &err)", "\t\treturn err"]
            body_text += [f"\tcase {g}:", "\t\treturn &jsoncodec.Error{Msg: \"Unmarshal(non-pointer)\"}"]
        body_text += ["\t}", "\treturn jsonUnmarshalExtra(data, v)", "}", ""]
    for n in names:
        if T.t[n]["encode"]:
            body_text += gen_encoder(T, n)
        if T.t[n]["decode"]:
            body_text += gen_decoder(T, n)
    if not goose:
        body_text += ["// jsonUnmarshalExtra decodes into the unnamed listed types (outside Goose only).",
                      "func jsonUnmarshalExtra(data []byte, v interface{}) error {",
                      "\tvar err error", "\tswitch p := v.(type) {"]
        for n in names:
            if T.t[n]["decode"]:
                g = T.go(n)
                body_text += [f"\tcase *{g}:", "\t\tif p == nil {",
                              "\t\t\treturn &jsoncodec.Error{Msg: \"Unmarshal(nil pointer)\"}", "\t\t}",
                              f"\t\tjdec_{ident(n)}(data, 0, p, &err)", "\t\treturn err"]
        body_text += ["\t}", "\tpanic(\"json model: decoding into a type not listed in the [json] table\")", "}", ""]
    text = "\n".join(body_text)
    imps = ['\t"netmodels.lab/jsoncodec"']
    if "json." in text:
        imps.insert(0, '\t"encoding/json"')
    for a, p in sorted(T.imports.items()):
        if re.search(r"\b" + re.escape(a) + r"\.", text):
            imps.append(f'\t{a} "{p}"')
    o += ["import ("] + imps + [")", ""]
    return "\n".join(o) + "\n" + text


def gen_extra_files(T, header, go_name):
    """The codec's part for the unnamed types (goose = false): {file name: contents}. With such
    types, json_extra_gen.go (build tag !goose) has their encoders and decoders, and
    json_extra_goose_gen.go (tag goose) the stub; without, json_extra_gen.go is the stub."""
    if all(T.t[n]["goose"] for n in T.names):
        return {"json_extra_gen.go": gen_extra_goose(T, header, go_name)}
    return {"json_extra_gen.go": gen_codec_go(T, header + "//go:build !goose\n", go_name, False),
            "json_extra_goose_gen.go": gen_extra_goose(T, header + "//go:build goose\n\n", go_name)}


def gen_extra_goose(T, header, go_name):
    """Under Goose: no unnamed types; decoding into any other type panics."""
    return (header + f"package {go_name}\n\n"
            "// jsonUnmarshalExtra: Goose translates no unnamed type of the [json] table; decoding\n"
            "// into one, or into a type not listed, panics.\n"
            "func jsonUnmarshalExtra(data []byte, v interface{}) error {\n"
            "\tpanic(\"json model: decoding into a type not listed in the [json] table\")\n"
            "}\n")


def gen_register_model(header, go_name):
    return (header + "//go:build rpcmodel || goose\n\n" + f"package {go_name}\n\n"
            "import (\n\t\"encoding/json\"\n\n\t\"netmodels.lab/jsoncodec\"\n)\n\n"
            "// registerJSON registers the codec with the encoding/json model (the first\n"
            "// registration stays).\n"
            "func registerJSON() {\n"
            "\tjson.SetCodec(&json.Codec{Marshal: jsonMarshal, Unmarshal: jsonUnmarshal, Scan: jsoncodec.Scan})\n"
            "}\n")


def gen_register_real(header, go_name):
    return (header + "//go:build !rpcmodel && !goose\n\n" + f"package {go_name}\n\n"
            "// registerJSON: real encoding/json needs no codec.\n"
            "func registerJSON() {}\n")


def audit_lines(T):
    return (f"{len(T.names)} types ({', '.join(T.names)})")


# ---------------------------------------------------------------------------------------------
# The test of the trusted claims against real encoding/json (json_gen_test.go)


def gen_test_go(T, header, go_name):
    rnd = []
    # random value generators for every listed type (struct fields recursively)
    for n in T.names:
        d = T.t[n]
        g = T.go(n)
        I = ident(n)
        rnd.append(f"func jrnd_{I}(r *rand.Rand, depth int) {g} {{")
        if d["kind"] == "basic":
            rnd.append(f"\treturn {g}(jrndUint(r, {UINTS[d['basic']]}))")
        elif d["kind"] == "slice":
            rnd += ["\tif r.Intn(4) == 0 || depth > 2 {", "\t\treturn nil", "\t}",
                    f"\tv := make({g}, r.Intn(4))", "\tfor i := range v {",
                    f"\t\tv[i] = {rnd_expr(T, d['elem'])}", "\t}", "\treturn v"]
        else:
            rnd.append(f"\tvar v {g}")
            for f in d["fields"]:
                rnd.append(f"\tv.{f['name']} = {rnd_expr(T, f['type'])}")
            rnd.append("\treturn v")
        rnd += ["}", ""]
    encs = [n for n in T.enc_types() if all(T.t[x]["encode"] for x in [n])]
    decs = T.dec_types()
    lines = [header + "//go:build !rpcmodel && !goose\n", f"package {go_name}", "",
             "import (", '\t"encoding/json"', '\t"math/rand"', '\t"reflect"', '\t"strings"',
             '\t"testing"', "", '\t"netmodels.lab/jsoncodec"']
    used = "\n".join(rnd) + " ".join(T.go(n) for n in T.names)
    for a, p in sorted(T.imports.items()):
        if re.search(r"\b" + re.escape(a) + r"\.", used):
            lines.append(f'\t{a} "{p}"')
    lines += [")", ""]
    lines += [
        "func jrndUint(r *rand.Rand, max uint64) uint64 {",
        "\tswitch r.Intn(4) {",
        "\tcase 0:",
        "\t\treturn 0",
        "\tcase 1:",
        "\t\treturn max",
        "\tcase 2:",
        "\t\tif x := uint64(r.Intn(20)); x <= max {",
        "\t\t\treturn x",
        "\t\t}",
        "\t\treturn max",
        "\t}",
        "\treturn r.Uint64() % (max/2 + 1)",
        "}",
        "",
        "// jrndString: a plain string (jsoncodec's subset), possibly empty, with spaces.",
        "func jrndString(r *rand.Rand) string {",
        "\tconst alphabet = \"abcXYZ019 _-.:/@{}[],\"",
        "\tn := r.Intn(8)",
        "\tvar sb strings.Builder",
        "\tfor i := 0; i < n; i++ {",
        "\t\tsb.WriteByte(alphabet[r.Intn(len(alphabet))])",
        "\t}",
        "\treturn sb.String()",
        "}",
        "",
        "func jrndAny(r *rand.Rand, depth int) interface{} {",
        f"\tswitch r.Intn({len(encs) + 1}) {{",
    ]
    for i, n in enumerate(encs):
        if T.t[n]["goose"]:
            lines += [f"\tcase {i}:", f"\t\treturn jrnd_{ident(n)}(r, depth+1)"]
    lines += ["\t}", "\treturn nil", "}", "",
              "func jrndRaw(r *rand.Rand) json.RawMessage {",
              "\tswitch r.Intn(4) {", "\tcase 0:", "\t\treturn nil", "\tcase 1:",
              "\t\treturn json.RawMessage(`{\"a\": [1, \"x\"] , \"b\":null}`)", "\tcase 2:",
              "\t\treturn json.RawMessage(\" 17 \")", "\t}", "\treturn json.RawMessage(`\"s\"`)", "}", ""]
    lines += rnd
    # the shape test: the listed structure is the Go type's
    lines += ["// TestJSONShapes: each listed struct's fields (names, Go types, tags) are the Go type's.",
              "func TestJSONShapes(t *testing.T) {"]
    for n in T.names:
        d = T.t[n]
        g = T.go(n)
        if d["kind"] == "struct":
            lines.append(f"\tjsonCheckFields(t, {go_str(n)}, reflect.TypeOf({g}{{}}), []string{{" +
                         ", ".join(go_str(f"{f['name']} {f['type']} {f['json'] + (',string' if f['quoted'] else '')}") for f in d["fields"]) + "})")
        elif d["kind"] == "basic":
            lines.append(f"\tif k := reflect.TypeOf({g}(0)).Kind().String(); k != {go_str(d['basic'])} {{")
            lines.append(f"\t\tt.Errorf(\"%s: kind %s, the [json] table says {d['basic']}\", {go_str(n)}, k)")
            lines.append("\t}")
        else:
            lines.append(f"\tif e := reflect.TypeOf({g}(nil)).Elem(); e != reflect.TypeOf({rnd_zero(T, d['elem'])}) {{")
            lines.append(f"\t\tt.Errorf(\"%s: element type %v\", {go_str(n)}, e)")
            lines.append("\t}")
        mv = "reflect.TypeOf(" + rnd_zero_of(T, n) + ")"
        hasM = d["marshal"] == "value"
        hasU = d["unmarshal"] == "pointer"
        lines.append(f"\tjsonCheckMethods(t, {go_str(n)}, {mv}, {str(hasM).lower()}, {str(hasU).lower()})")
    lines += ["}", "",
              "var jsonMarshalerT = reflect.TypeOf((*json.Marshaler)(nil)).Elem()",
              "var jsonUnmarshalerT = reflect.TypeOf((*json.Unmarshaler)(nil)).Elem()", "",
              "func jsonCheckMethods(t *testing.T, n string, ty reflect.Type, m, u bool) {",
              "\tif ty.Implements(jsonMarshalerT) != m {",
              "\t\tt.Errorf(\"%s: implements json.Marshaler: %v, the [json] table says %v\", n, ty.Implements(jsonMarshalerT), m)",
              "\t}",
              "\tif reflect.PointerTo(ty).Implements(jsonMarshalerT) && !ty.Implements(jsonMarshalerT) {",
              "\t\tt.Errorf(\"%s: a MarshalJSON on the pointer (outside the codec)\", n)",
              "\t}",
              "\tif reflect.PointerTo(ty).Implements(jsonUnmarshalerT) != u {",
              "\t\tt.Errorf(\"%s: *T implements json.Unmarshaler: %v, the [json] table says %v\", n, reflect.PointerTo(ty).Implements(jsonUnmarshalerT), u)",
              "\t}",
              "\tfor _, other := range []string{\"MarshalText\", \"UnmarshalText\"} {",
              "\t\tif _, ok := reflect.PointerTo(ty).MethodByName(other); ok {",
              "\t\t\tt.Errorf(\"%s: has %s (outside the codec)\", n, other)",
              "\t\t}",
              "\t}",
              "}", "",
              "func jsonCheckFields(t *testing.T, n string, ty reflect.Type, want []string) {",
              "\tgot := []string{}",
              "\tfor i := 0; i < ty.NumField(); i++ {",
              "\t\tf := ty.Field(i)",
              "\t\tif !f.IsExported() {",
              "\t\t\tcontinue",
              "\t\t}",
              "\t\tgot = append(got, f.Name+\" \"+jsonTypeName(f.Type)+\" \"+f.Tag.Get(\"json\"))",
              "\t}",
              "\tif !reflect.DeepEqual(got, want) {",
              "\t\tt.Errorf(\"%s: fields\\n got  %q\\n want %q (the [json] table)\", n, got, want)",
              "\t}",
              "}", "",
              "func jsonTypeName(ty reflect.Type) string {",
              "\tif ty == reflect.TypeOf(json.RawMessage(nil)) {",
              "\t\treturn \"json.RawMessage\"",
              "\t}",
              "\tif ty.Kind() == reflect.Interface && ty.NumMethod() == 0 {",
              "\t\treturn \"any\"",
              "\t}",
              "\tif ty.Kind() == reflect.Slice && ty.Name() == \"\" {",
              "\t\treturn \"[]\" + jsonTypeName(ty.Elem())",
              "\t}",
              "\tif ty.PkgPath() == \"\" {",
              "\t\treturn ty.String()",
              "\t}",
              "\treturn ty.String()",
              "}", ""]
    # encoders agree byte for byte
    lines += ["// TestJSONEncode: the codec's encoding of random values is real encoding/json's, byte for byte",
              "// (also through a pointer, and in an any).",
              "func TestJSONEncode(t *testing.T) {",
              "\tr := rand.New(rand.NewSource(1))",
              "\tfor it := 0; it < 3000; it++ {"]
    for n in encs:
        if not T.t[n]["goose"]:
            continue
        I = ident(n)
        lines += [f"\t\t{{", f"\t\t\tv := jrnd_{I}(r, 0)", "\t\t\tjsonCheckEncode(t, v)", "\t\t\tjsonCheckEncode(t, &v)", f"\t\t}}"]
    lines += ["\t\tjsonCheckEncode(t, nil)", "\t}", "}", "",
              "func jsonCheckEncode(t *testing.T, v interface{}) {",
              "\tt.Helper()",
              "\twant, werr := json.Marshal(v)",
              "\tgot, gerr := jsonMarshal(v)",
              "\tif (werr != nil) != (gerr != nil) || string(got) != string(want) {",
              "\t\tt.Fatalf(\"Marshal(%#v):\\n real  %s %v\\n codec %s %v\", v, want, werr, got, gerr)",
              "\t}",
              "}", ""]
    # decoding: canonical encodings of every encodable type into every decodable type, + mutations
    lines += ["// jsonSamples: encodings (by real encoding/json) of random values of every listed type.",
              "func jsonSamples(r *rand.Rand, n int) [][]byte {",
              "\tvar out [][]byte",
              "\tfor len(out) < n {",
              "\t\tvar v interface{}",
              f"\t\tswitch r.Intn({len(T.names) + 1}) {{"]
    for i, n in enumerate(T.names):
        lines += [f"\t\tcase {i}:", f"\t\t\tv = jrnd_{ident(n)}(r, 0)"]
    lines += ["\t\tdefault:", "\t\t\tv = jrndAny(r, 0)", "\t\t}",
              "\t\tb, err := json.Marshal(v)", "\t\tif err == nil {", "\t\t\tout = append(out, b)", "\t\t}",
              "\t}", "\treturn out", "}", ""]
    lines += ["// jsonDecoders: for each decodable listed type, a fresh target and a pre-filled one, decoded",
              "// by real encoding/json and by the codec.",
              "type jsonTarget struct {",
              "\tname string",
              "\tnew  func(r *rand.Rand, fill bool) (interface{}, interface{})",
              "}", "",
              "func jsonTargets() []jsonTarget {",
              "\treturn []jsonTarget{"]
    for n in decs:
        g = T.go(n)
        I = ident(n)
        d = T.t[n]
        fill = "fill && " + ("false" if d["kind"] == "slice" else "true")
        lines += [f"\t\t{{{go_str(n)}, func(r *rand.Rand, fill bool) (interface{{}}, interface{{}}) {{",
                  f"\t\t\tvar a, b {g}",
                  f"\t\t\tif {fill} {{",
                  f"\t\t\t\ts := r.Int63()",
                  f"\t\t\t\ta = jrnd_{I}(rand.New(rand.NewSource(s)), 0)",
                  f"\t\t\t\tb = jrnd_{I}(rand.New(rand.NewSource(s)), 0)",
                  "\t\t\t}",
                  "\t\t\treturn &a, &b",
                  "\t\t}},"]
    lines += ["\t}", "}", "",
              "// jsonCheckDecode decodes data into a pair of equal targets, by real encoding/json and by the",
              "// model's Unmarshal (validation, then the codec): equal values and error-or-not. ok is false if",
              "// the codec panicked decoding into a non-nil slice (the model's panic: Go merges into the",
              "// slice's elements); any other panic fails the test.",
              "func jsonCheckDecode(t *testing.T, name string, data []byte, a, b interface{}) (ok bool) {",
              "\tt.Helper()",
              "\twerr := json.Unmarshal(data, a)",
              "\tvar gerr error",
              "\tpanicked := func() (p bool) {",
              "\t\tdefer func() {",
              "\t\t\tif x := recover(); x != nil {",
              "\t\t\t\tif x != \"json model: decoding into a non-nil slice\" {",
              "\t\t\t\t\tpanic(x)",
              "\t\t\t\t}",
              "\t\t\t\tp = true",
              "\t\t\t}",
              "\t\t}()",
              "\t\tif !jsoncodec.Valid(data) {",
              "\t\t\tgerr = &jsoncodec.Error{Msg: \"syntax\"}",
              "\t\t\treturn false",
              "\t\t}",
              "\t\tgerr = jsonUnmarshal(data, b)",
              "\t\treturn false",
              "\t}()",
              "\tif panicked {",
              "\t\treturn false",
              "\t}",
              "\tif (werr != nil) != (gerr != nil) || !reflect.DeepEqual(a, b) {",
              "\t\tt.Fatalf(\"Unmarshal(%q) into %s:\\n real  %#v %v\\n codec %#v %v\", data, name, a, werr, b, gerr)",
              "\t}",
              "\treturn true",
              "}", "",
              "// jsonMutate: a mutation of a JSON text (within the plain alphabet).",
              "func jsonMutate(r *rand.Rand, b []byte, samples [][]byte) []byte {",
              "\ts := string(b)",
              "\tswitch r.Intn(10) {",
              "\tcase 0: // a key or word in another case",
              "\t\treturn []byte(strings.ToUpper(s[:len(s)/2]) + s[len(s)/2:])",
              "\tcase 1: // whitespace around tokens",
              "\t\ts = strings.ReplaceAll(s, \":\", \" :\\n \")",
              "\t\treturn []byte(strings.ReplaceAll(s, \",\", \"\\t, \"))",
              "\tcase 2: // a value replaced by another sample",
              "\t\ti := strings.Index(s, \":\")",
              "\t\tif i < 0 {",
              "\t\t\treturn b",
              "\t\t}",
              "\t\tj := strings.IndexAny(s[i:], \",}\")",
              "\t\tif j < 0 {",
              "\t\t\treturn b",
              "\t\t}",
              "\t\treturn []byte(s[:i+1] + string(samples[r.Intn(len(samples))]) + s[i+j:])",
              "\tcase 3: // a value replaced by a literal or a number",
              "\t\tlits := []string{\"null\", \"true\", \"false\", \"0\", \"-1\", \"1.5\", \"1e2\", \"256\", \"4294967296\",",
              "\t\t\t\"18446744073709551616\", \"\\\"\\\"\", \"\\\"12\\\"\", \"\\\"012\\\"\", \"\\\"null\\\"\", \"\\\" 1\\\"\", \"[]\", \"{}\"}",
              "\t\ti := strings.Index(s, \":\")",
              "\t\tif i < 0 {",
              "\t\t\treturn []byte(lits[r.Intn(len(lits))])",
              "\t\t}",
              "\t\tj := strings.IndexAny(s[i:], \",}\")",
              "\t\tif j < 0 {",
              "\t\t\treturn b",
              "\t\t}",
              "\t\treturn []byte(s[:i+1] + lits[r.Intn(len(lits))] + s[i+j:])",
              "\tcase 4: // a member repeated",
              "\t\tif len(s) > 2 && s[0] == '{' && s[1] != '}' {",
              "\t\t\tj := strings.Index(s, \",\")",
              "\t\t\tif j > 0 {",
              "\t\t\t\treturn []byte(s[:len(s)-1] + \",\" + s[1:j] + \"}\")",
              "\t\t\t}",
              "\t\t}",
              "\t\treturn b",
              "\tcase 5: // cut short",
              "\t\treturn b[:r.Intn(len(b)+1)]",
              "\tcase 6: // a suffix",
              "\t\treturn b[r.Intn(len(b)+1):]",
              "\tcase 7: // an unknown member",
              "\t\tif len(s) > 1 && s[0] == '{' {",
              "\t\t\treturn []byte(\"{\\\"zz\\\":\" + string(samples[r.Intn(len(samples))]) + map[bool]string{true: \"\", false: \",\"}[s[1] == '}'] + s[1:])",
              "\t\t}",
              "\t\treturn b",
              "\tcase 8: // one byte replaced",
              "\t\tif len(b) == 0 {",
              "\t\t\treturn b",
              "\t\t}",
              "\t\tc := []byte(s)",
              "\t\tc[r.Intn(len(c))] = \"{}[],:\\\" 0a-.etn\"[r.Intn(15)]",
              "\t\treturn c",
              "\t}",
              "\treturn []byte(s + \" \")",
              "}", "",
              "// TestJSONDecode: the codec decodes the encodings of every listed type, and mutations of them,",
              "// into every decodable type (fresh and pre-filled targets) as real encoding/json does; it panics",
              "// only into a non-nil slice (pre-filled slice targets are left out; a struct's slice field may",
              "// be non-nil).",
              "func TestJSONDecode(t *testing.T) {",
              "\tr := rand.New(rand.NewSource(2))",
              "\tsamples := jsonSamples(r, 200)",
              "\ttargets := jsonTargets()",
              "\tnSlice := 0",
              "\tfor it := 0; it < 20000; it++ {",
              "\t\tdata := samples[r.Intn(len(samples))]",
              "\t\tfor m := r.Intn(3); m > 0; m-- {",
              "\t\t\tdata = jsonMutate(r, data, samples)",
              "\t\t}",
              "\t\ttg := targets[r.Intn(len(targets))]",
              "\t\ta, b := tg.new(r, r.Intn(2) == 0)",
              "\t\tif !jsonCheckDecode(t, tg.name, data, a, b) {",
              "\t\t\tnSlice++",
              "\t\t}",
              "\t}",
              "\tif nSlice > 10000 {",
              "\t\tt.Fatalf(\"%d of 20000 decodings into a non-nil slice (the model panics): too few checked\", nSlice)",
              "\t}",
              "}", "",
              "// TestJSONScan: the scanner agrees with real encoding/json on what is one valid value (random",
              "// texts over JSON's structural characters and a plain alphabet), and a stream of encodings",
              "// separated by newlines (Encoder's) splits as real encoding/json's Decoder splits it, at every",
              "// cut (More before a value's last byte).",
              "func TestJSONScan(t *testing.T) {",
              "\tr := rand.New(rand.NewSource(3))",
              "\tconst alpha = \"{}[],:\\\" \\n\\t0123-.eE+tfrulnasx\"",
              "\tfor it := 0; it < 200000; it++ {",
              "\t\tn := r.Intn(12)",
              "\t\tb := make([]byte, n)",
              "\t\tfor i := range b {",
              "\t\t\tb[i] = alpha[r.Intn(len(alpha))]",
              "\t\t}",
              "\t\tif got, want := jsoncodec.Valid(b), json.Valid(b); got != want {",
              "\t\t\tt.Fatalf(\"Valid(%q): scanner %v, real %v\", b, got, want)",
              "\t\t}",
              "\t}",
              "\tsamples := jsonSamples(r, 300)",
              "\tfor _, s := range samples {",
              "\t\tif !jsoncodec.Valid(s) {",
              "\t\t\tt.Fatalf(\"Valid(%q) false\", s)",
              "\t\t}",
              "\t\tstream := append(append([]byte{}, s...), '\\n')",
              "\t\tfor cut := 0; cut <= len(stream); cut++ {",
              "\t\t\tst, end := jsoncodec.Scan(stream[:cut], false)",
              "\t\t\tif cut < len(s) && st != jsoncodec.More {",
              "\t\t\t\tif !(st == jsoncodec.Done && s[0] != '{' && s[0] != '[' && s[0] != '\"' && uint64(cut) >= end) {",
              "\t\t\t\t\tt.Fatalf(\"Scan(%q, false) = %d, %d, want More\", stream[:cut], st, end)",
              "\t\t\t\t}",
              "\t\t\t}",
              "\t\t\tif cut > len(s) && (st != jsoncodec.Done || end != uint64(len(s))) {",
              "\t\t\t\tt.Fatalf(\"Scan(%q, false) = %d, %d, want Done, %d\", stream[:cut], st, end, len(s))",
              "\t\t\t}",
              "\t\t}",
              "\t\t// a suffix of a stream of two values: real Decoder's first value or error, and the",
              "\t\t// scanner's",
              "\t\tt2 := samples[r.Intn(len(samples))]",
              "\t\tboth := append(append(append(append([]byte{}, s...), '\\n'), t2...), '\\n')",
              "\t\tfor k := 0; k <= len(both); k++ {",
              "\t\t\tjsonCheckStream(t, both[k:])",
              "\t\t}",
              "\t}",
              "}", "",
              "// jsonCheckStream: real Decoder's first Decode on b (all of it available, then EOF) succeeds",
              "// or fails with a syntax error, io.EOF or io.ErrUnexpectedEOF exactly when the scanner says,",
              "// and the value it decodes is the scanner's.",
              "func jsonCheckStream(t *testing.T, b []byte) {",
              "\tt.Helper()",
              "\tvar raw json.RawMessage",
              "\terr := json.NewDecoder(strings.NewReader(string(b))).Decode(&raw)",
              "\tst, end := jsoncodec.Scan(b, true)",
              "\tswitch {",
              "\tcase err == nil:",
              "\t\tif st != jsoncodec.Done || strings.TrimSpace(string(b[:end])) != string(raw) {",
              "\t\t\tt.Fatalf(\"stream %q: real decodes %q, scanner %d, %d\", b, raw, st, end)",
              "\t\t}",
              "\tcase err.Error() == \"EOF\" || err.Error() == \"unexpected EOF\":",
              "\t\tif st != jsoncodec.More {",
              "\t\t\tt.Fatalf(\"stream %q: real %v, scanner %d, %d\", b, err, st, end)",
              "\t\t}",
              "\t\tif (err.Error() == \"EOF\") != (strings.TrimSpace(string(b)) == \"\") {",
              "\t\t\tt.Fatalf(\"stream %q: real %v\", b, err)",
              "\t\t}",
              "\tdefault:",
              "\t\tif st != jsoncodec.Bad {",
              "\t\t\tt.Fatalf(\"stream %q: real %v, scanner %d, %d\", b, err, st, end)",
              "\t\t}",
              "\t}",
              "}", ""]
    return "\n".join(lines) + "\n"


def rnd_expr(T, t):
    bt = T.base(t)
    if t in T.t and T.t[t]["kind"] != "basic":
        return f"jrnd_{ident(t)}(r, depth+1)"
    if t in T.t:
        return f"jrnd_{ident(t)}(r, depth+1)"
    if t == "any":
        return "jrndAny(r, depth)"
    if t == "json.RawMessage":
        return "jrndRaw(r)"
    if bt in UINTS:
        return f"{bt}(jrndUint(r, {UINTS[bt]}))"
    if bt == "string":
        return "jrndString(r)"
    if bt == "bool":
        return "r.Intn(2) == 0"
    raise JsonError(f"no generator for {t}")


def rnd_zero(T, t):
    """A Go expression of type t (for reflect.TypeOf)."""
    if t in T.t:
        return rnd_zero_of(T, t)
    return {"uint64": "uint64(0)", "uint32": "uint32(0)", "uint8": "uint8(0)", "string": "\"\"",
            "bool": "false"}[t]


def rnd_zero_of(T, n):
    d = T.t[n]
    g = T.go(n)
    if d["kind"] == "struct":
        return f"{g}{{}}"
    if d["kind"] == "slice":
        return f"{g}(nil)"
    return f"{g}(0)"


def files(T, header, go_name, register=False):
    """The generated files: {file name: contents} (the registration files only with `register`)."""
    out = {"json_gen.go": gen_codec_go(T, header, go_name, True)}
    out.update(gen_extra_files(T, header, go_name))
    if register:
        out["json_model_gen.go"] = gen_register_model(header, go_name)
        out["json_real_gen.go"] = gen_register_real(header, go_name)
    out["json_gen_test.go"] = gen_test_go(T, header, go_name)
    return out


def main():
    import argparse
    import os
    import sys
    import tomllib
    ap = argparse.ArgumentParser(description="An encoding/json codec for a [json] table.")
    ap.add_argument("toml", help="a toml file holding a [json] table")
    ap.add_argument("outdir", help="the Go package directory to write the files into")
    ap.add_argument("--pkg", required=True, help="the Go package name")
    ap.add_argument("--register", action="store_true",
                    help="also write registerJSON (json_model_gen.go, json_real_gen.go)")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if a file differs")
    a = ap.parse_args()
    try:
        with open(a.toml, "rb") as fh:
            doc = tomllib.load(fh)
        if "json" not in doc:
            raise JsonError(f"{a.toml}: no [json] table")
        T = Types(doc["json"])
    except JsonError as e:
        print(f"jsongen: {e}", file=sys.stderr)
        return 1
    header = f"// Code generated by jsongen.py from {os.path.basename(a.toml)}. DO NOT EDIT.\n\n"
    ok = True
    for f, c in files(T, header, a.pkg, a.register).items():
        p = os.path.join(a.outdir, f)
        cur = open(p).read() if os.path.exists(p) else None
        if cur == c:
            continue
        if a.check:
            print(f"not current: {p}", file=sys.stderr)
            ok = False
        else:
            os.makedirs(a.outdir, exist_ok=True)
            with open(p, "w") as fh:
                fh.write(c)
            print(f"wrote {p}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
