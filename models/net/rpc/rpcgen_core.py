"""rpcgen's trusted core: the Go code that stands in for encoding/gob and reflection in the net/rpc
model (models/net/rpc), for the types and receivers of one program.

THE CLAIM (trusted). For every input this core accepts (a dump of reflection's facts about the
program's receivers and types, `models/rpcdesc`), the emitted code behaves, as the program
observes it, as Go 1.27.3's encoding/gob and reflection do in net/rpc:

  * `rpcEncode(v)` and `rpcDecode(data, p)`: decoding `rpcEncode(v)` into `*p` (p a non-nil
    pointer to a value of v's type, or of the type v points to) leaves `*p` as gob's
    `Decoder.Decode(p)` of gob's `Encoder.Encode(v)` leaves it, for every value of `*p` before the
    decode (gob merges into it: below); the encoding of a value of a listed type never fails.
  * `rpcReceiver(rcvr)`, for a receiver of a listed receiver type: `Name` is
    `reflect.Indirect(reflect.ValueOf(rcvr)).Type().Name()` (`NilPtr` says whether that panics),
    `Type` is `reflect.TypeOf(rcvr).String()`, `Methods` holds exactly the methods net/rpc's
    `suitableMethods` registers for the type, and `PtrHasMethods` whether it registers any for a
    pointer to it; per method, `NewArg`/`NewReply`/`Call` are net/rpc's `readRequest` values
    (`reflect.New`, with `reflect.MakeMap`/`MakeSlice` for a map or slice reply) and
    `reflect.Value.Call` of the method.

The facts are not decided here: the dump states them, read off reflect (`models/rpcdesc`,
`suitableMethods` copied from net/rpc). What is decided here is the encoding and the decoding,
whose every choice is gob's (Go 1.27.3, `src/encoding/gob/`), cited below.

THE SUBSET. Accepted types: bool; int, int8, int16, int32, int64, uint, uint8, uint16, uint32,
uint64; string; slices of accepted non-pointer types (`[]byte` among them); maps of accepted
non-pointer key and element types; named struct types whose exported fields are of accepted
types or pointers to accepted non-pointer types (unexported fields are ignored, as gob ignores
them: type.go, `isSent`); and named types of these. A receiver type is a named type or a pointer
to one; every method suitableMethods registers for it must take an accepted type or a pointer to
one, and a pointer to an accepted type as its reply.

THE REFUSALS (exit status 2, every reason printed, naming the type, field or method): floats and
complex numbers; arrays; interfaces (and so `any` fields); channels and functions (gob skips such
fields, `isSent`: refused rather than modelled); uintptr and unsafe.Pointer; a pointer to a
pointer; a pointer element of a slice or map (gob's "encodeArray: nil element" error is not
modelled); embedded fields; a struct with fields none of which is exported (gob's "type has no
exported fields" error); a type that implements, or whose pointer implements, gob.GobEncoder,
gob.GobDecoder, encoding.BinaryMarshaler/BinaryUnmarshaler or TextMarshaler/TextUnmarshaler (gob
calls those methods: type.go, `validUserType`); recursive types; unnamed struct types; types the
generated package cannot name (unexported named types, types of package main, generic types).

THE ENCODING (the model's own: gob's bytes differ; both ends run the model). A value is its
type's tag (the type's identity: `importpath.Name` for a named type, the composite's spelling over
tags otherwise) and its body: bool one byte; integers eight bytes little-endian (signed ones as
int64's bits); strings a length and the bytes; slices a count and each element's body; maps a
count and each key's and element's bodies; structs a marker byte and, per exported field in
order, a presence byte and, if present, the field's body (a pointer field: its element's body).

THE DECODING, gob's (decode.go), which merges into the target:
  * A struct field is present exactly when gob sends it (encode.go: `encodeStruct` skips a nil
    pointer field, `encIndirect`/`valid`; the ops skip zero values when `sendZero` is off, as it
    is for struct fields: bool false, integers 0, strings "", slices of length 0, nil maps (an
    empty non-nil map is sent), and a struct is always sent); through a pointer field, what is
    sent is the element (`encIndirect`), under the element's rule. A field not present leaves the
    target's field as it was (`decodeStruct`); a present pointer field is allocated if nil and its
    element decoded into (`decAlloc`).
  * Slices (`decodeSlice`, `decUint8Slice`): of count n, the target is a new slice of n zero
    elements if its capacity is below n, else resliced to n (keeping its backing array and the
    elements there); then each element is decoded into (every element is sent, `sendZero`).
  * Maps (`decodeMap`): a nil target gets a new map; each entry is decoded into a fresh zero key
    and element and stored (the map's other entries stay).
  * Basic values are set. A top-level value is always sent (`encodeSingle`, `sendZero`) and
    decoded into `*p` as a field would be.

THE DOCUMENTED DEVIATIONS (behaviors of gob the model does not reproduce, each stuck: the emitted
`rpcStuck()`, which in a model build is the net/rpc model's `Stuck`, whose Lean model is Perennial's
stuck `Panic "not modelled"`, so a proof of the program shows it never reaches one; never a value
panic, which a program could recover, adding behaviors gob does not have, nor a bare `select {}`,
whose WP proves anything after it: models/README.md, "Not modelled: stuck"): decoding a value of
one type into a value of another (gob matches struct fields by name and converts integers; the
model is stuck); `Encode` of a nil value, a nil pointer or a value of an unlisted type (gob returns
an error; the model is stuck); `Decode` into a nil pointer or an unlisted type (likewise); and, not
observable through net/rpc's API: the capacity of a slice gob allocates (it may allocate less and
grow), the contents of the target after a decode that fails (only on malformed input, which no
model peer sends: gob's errors there are not the model's).
"""

import re


class RpcRefused(Exception):
    def __init__(self, reasons):
        super().__init__("; ".join(reasons))
        self.reasons = reasons


SIGNED = {"int", "int8", "int16", "int32", "int64"}
UNSIGNED = {"uint", "uint8", "uint16", "uint32", "uint64"}
BASIC = SIGNED | UNSIGNED | {"bool", "string"}
GOB_IFACES = ["gob_encoder", "gob_decoder", "binary_marshaler", "binary_unmarshaler",
              "text_marshaler", "text_unmarshaler"]
# identifiers the generated files import or use as local names: a package alias that is one of
# them (or starts with "rpc") is renamed p_<alias> in the generated code
RESERVED = {"errors", "rpcmodel", "bytes", "gob", "rand", "reflect", "testing", "fmt", "math", "os",
            "strconv", "t", "r", "i", "seed", "v", "z", "real", "model", "model2", "r1", "r2",
            "real3", "model3", "before", "err", "d", "b", "x", "y", "p", "n", "ok", "rest", "tag",
            "data", "ptr", "rcvr", "argv", "replyv", "ms", "errT", "exported", "m", "mt", "got",
            "want", "s", "k", "f", "c", "e", "q"}


class Schema:
    """The accepted program: its types (by dump id), roots and receivers."""

    def __init__(self, dump, aliases):
        self.t = {e["id"]: e for e in dump["table"]}
        self.reasons = []
        self.alias = {}       # import path -> alias
        for a, p in aliases.items():
            if a in RESERVED or a.startswith("rpc"):
                a = "p_" + a
            self.alias[p] = a
        self.ok = {}          # id -> True (checked, accepted)
        self.roots = []       # ids of top-level types (method arguments flattened, extra types)
        self.receivers = []   # [(receiver dump, [(method name, arg id, arg is pointer, reply id)])]
        for r in dump["receivers"]:
            self.receiver(r)
        for x in dump["types"]:
            self.root(x["type"], f"type {x['expr']}")
        self.closure = []     # every accepted type reached, in a fixed order
        seen = set()
        for i in self.roots:
            self.collect(i, seen)
        if self.reasons:
            raise RpcRefused(self.reasons)

    # -- the subset -------------------------------------------------------------------------

    def refuse(self, where, why):
        self.reasons.append(f"{where}: {why}")
        return False

    def name_ok(self, e, where):
        if e["name"] and e["pkg_path"]:
            if "[" in e["name"]:
                return self.refuse(where, f"{e['string']} is a generic type (not nameable)")
            if not e["name"][0].isupper():
                return self.refuse(where, f"{e['string']} is unexported (the codec cannot name it)")
            if e["pkg_name"] == "main":
                return self.refuse(where, f"{e['string']} is in package main (not importable)")
        return True

    def check(self, i, where, ctx, stack=()):
        """Whether type i is accepted in context ctx ("top", "field", "elem")."""
        e = self.t[i]
        where = f"{where} ({e['string']})" if not where.endswith(")") else where
        if i in stack:
            return self.refuse(where, f"recursive type {e['string']}")
        k = e["kind"]
        if k == "ptr":
            if ctx != "field":
                return self.refuse(where, "a pointer here (a pointer element of a slice or map, "
                                          "or a pointer to a pointer)")
            return self.check(e["elem"], where, "ptrelem", stack + (i,))
        if i in self.ok:
            return True
        for f in GOB_IFACES:
            if e[f]:
                return self.refuse(where, f"{e['string']} implements gob's {f} interface "
                                          "(gob calls its methods)")
        if not self.name_ok(e, where):
            return False
        good = True
        if k in BASIC:
            pass
        elif k == "slice":
            good = self.check(e["elem"], f"{where} element", "elem", stack + (i,))
        elif k == "map":
            good = (self.check(e["key"], f"{where} key", "elem", stack + (i,)) and
                    self.check(e["elem"], f"{where} element", "elem", stack + (i,)))
        elif k == "struct":
            if not e["name"]:
                return self.refuse(where, "an unnamed struct type")
            exported = [f for f in e["fields"] if f["exported"]]
            if e["fields"] and not exported:
                return self.refuse(where, f"{e['string']} has fields but none exported "
                                          "(gob: no exported fields)")
            for f in e["fields"]:
                fw = f"{e['string']}.{f['name']}"
                if f["embedded"]:
                    good = self.refuse(fw, "an embedded field") and good
                    continue
                if not f["exported"]:
                    continue
                good = self.check(f["type"], fw, "field", stack + (i,)) and good
        else:
            return self.refuse(where, f"kind {k} is outside the subset")
        if good:
            self.ok[i] = True
        return good

    def root(self, i, where):
        e = self.t[i]
        if e["kind"] == "ptr":
            i = e["elem"]
            if self.t[i]["kind"] == "ptr":
                return self.refuse(where, "a pointer to a pointer")
        if self.check(i, where, "top") and i not in self.roots:
            self.roots.append(i)
        return i

    def receiver(self, r):
        rt = self.t[r["type"]]
        base = self.t[rt["elem"]] if rt["kind"] == "ptr" else rt
        where = f"receiver {r['expr']}"
        if not base["name"] or (rt["kind"] == "ptr" and self.t[base["id"]]["kind"] == "ptr"):
            self.refuse(where, "a receiver is a named type or a pointer to one")
            return
        if not self.name_ok(base, where):
            return
        ms = []
        for m in r["methods"]:
            mw = f"{where} method {m['name']}"
            a = self.t[m["arg"]]
            arg_ptr = a["kind"] == "ptr"
            ai = self.root(m["arg"], f"{mw} argument")
            ri = self.root(m["reply"], f"{mw} reply")
            ms.append((m["name"], ai, arg_ptr, ri))
        self.receivers.append((r, ms))

    def collect(self, i, seen):
        e = self.t[i]
        if e["kind"] == "ptr":
            return self.collect(e["elem"], seen)
        if i in seen:
            return
        seen.add(i)
        if e["kind"] in ("slice", "map"):
            if e["kind"] == "map":
                self.collect(e["key"], seen)
            self.collect(e["elem"], seen)
        elif e["kind"] == "struct":
            for f in e["fields"]:
                if f["exported"]:
                    self.collect(f["type"], seen)
        self.closure.append(i)

    # -- names --------------------------------------------------------------------------------

    def pkg_alias(self, path, pkg_name):
        if path not in self.alias:
            base = pkg_name if pkg_name else re.sub(r"\W", "_", path.split("/")[-1])
            if base in RESERVED or base.startswith("rpc"):
                base = "p_" + base
            a, n = base, 2
            while a in self.alias.values():
                a, n = f"{base}{n}", n + 1
            self.alias[path] = a
        return self.alias[path]

    def go(self, i):
        """The Go spelling of type i in the generated package."""
        e = self.t[i]
        if e["name"]:
            if not e["pkg_path"]:
                return e["name"]
            return self.pkg_alias(e["pkg_path"], e["pkg_name"]) + "." + e["name"]
        k = e["kind"]
        if k == "slice":
            return "[]" + self.go(e["elem"])
        if k == "map":
            return f"map[{self.go(e['key'])}]{self.go(e['elem'])}"
        if k == "ptr":
            return "*" + self.go(e["elem"])
        raise AssertionError(e)

    def tag(self, i):
        """Type i's identity on the wire."""
        e = self.t[i]
        if e["name"]:
            return (e["pkg_path"] + "." if e["pkg_path"] else "") + e["name"]
        k = e["kind"]
        if k == "slice":
            return "[]" + self.tag(e["elem"])
        if k == "map":
            return f"map[{self.tag(e['key'])}]{self.tag(e['elem'])}"
        raise AssertionError(e)

    def imports(self, receivers=True):
        """The (alias, path) imports of the closure's types, and with receivers also of the
        receivers' types: rpc_gen.go names only the types (an import of a receiver's package it
        does not use would not compile); the generated test names the receivers too."""
        for i in self.closure:
            self.go(i)
        for r, _ in self.receivers:
            self.go(r["type"])
        return sorted((a, p) for p, a in self.alias.items()
                      if any(self.uses(i, p) for i in self.closure)
                      or (receivers and any(self.uses(r["type"], p) for r, _ in self.receivers)))

    def uses(self, i, path):
        e = self.t[i]
        if e["name"]:
            return e["pkg_path"] == path
        return any(self.uses(e[k], path) for k in ("elem", "key") if e.get(k, -1) >= 0)


# -- emitting -------------------------------------------------------------------------------

def fn(i):
    return f"t{i}"


def enc_body(S, i):
    e, g = S.t[i], S.go(i)
    k = e["kind"]
    if k == "bool":
        return "\tif v {\n\t\treturn append(b, 1)\n\t}\n\treturn append(b, 0)\n"
    if k in SIGNED:
        return "\treturn rpcPutU64(b, uint64(int64(v)))\n"
    if k in UNSIGNED:
        return "\treturn rpcPutU64(b, uint64(v))\n"
    if k == "string":
        return "\tb = rpcPutU64(b, uint64(len(v)))\n\treturn append(b, v...)\n"
    if k == "slice":
        return (f"\tb = rpcPutU64(b, uint64(len(v)))\n\tfor _, x := range v {{\n"
                f"\t\tb = rpcEnc_{fn(e['elem'])}(b, x)\n\t}}\n\treturn b\n")
    if k == "map":
        return (f"\tb = rpcPutU64(b, uint64(len(v)))\n\tfor x, y := range v {{\n"
                f"\t\tb = rpcEnc_{fn(e['key'])}(b, x)\n\t\tb = rpcEnc_{fn(e['elem'])}(b, y)\n"
                f"\t}}\n\treturn b\n")
    if k == "struct":
        o = ["\tb = append(b, 1)\n"]
        for f in e["fields"]:
            if not f["exported"]:
                continue
            ft = S.t[f["type"]]
            if ft["kind"] == "ptr":
                el = ft["elem"]
                o.append(f"\tif v.{f['name']} != nil && rpcSent_{fn(el)}(*v.{f['name']}) {{\n"
                         f"\t\tb = append(b, 1)\n\t\tb = rpcEnc_{fn(el)}(b, *v.{f['name']})\n"
                         f"\t}} else {{\n\t\tb = append(b, 0)\n\t}}\n")
            else:
                o.append(f"\tif rpcSent_{fn(f['type'])}(v.{f['name']}) {{\n"
                         f"\t\tb = append(b, 1)\n\t\tb = rpcEnc_{fn(f['type'])}(b, v.{f['name']})\n"
                         f"\t}} else {{\n\t\tb = append(b, 0)\n\t}}\n")
        o.append("\treturn b\n")
        return "".join(o)
    raise AssertionError(e)


def sent_body(S, i):
    """gob's rule for sending a struct field's value (sendZero off)."""
    k = S.t[i]["kind"]
    if k == "bool":
        return "\treturn bool(v)\n"
    if k in SIGNED or k in UNSIGNED:
        return "\treturn v != 0\n"
    if k == "string":
        return "\treturn v != \"\"\n"
    if k == "slice":
        return "\treturn len(v) != 0\n"
    if k == "map":
        return "\treturn v != nil\n"
    if k == "struct":
        return "\treturn true\n"
    raise AssertionError(k)


def dec_body(S, i):
    e, g = S.t[i], S.go(i)
    k = e["kind"]
    fail = "\t\treturn nil, false\n"
    if k == "bool":
        return (f"\tif len(b) < 1 || b[0] > 1 {{\n{fail}\t}}\n"
                f"\t*p = {g}(b[0] == 1)\n\treturn b[1:], true\n")
    if k in SIGNED:
        return (f"\tx, r, ok := rpcGetU64(b)\n\tif !ok || int64({g}(int64(x))) != int64(x) {{\n{fail}\t}}\n"
                f"\t*p = {g}(int64(x))\n\treturn r, true\n")
    if k in UNSIGNED:
        return (f"\tx, r, ok := rpcGetU64(b)\n\tif !ok || uint64({g}(x)) != x {{\n{fail}\t}}\n"
                f"\t*p = {g}(x)\n\treturn r, true\n")
    if k == "string":
        return (f"\tn, r, ok := rpcGetU64(b)\n\tif !ok || n > uint64(len(r)) {{\n{fail}\t}}\n"
                f"\t*p = {g}(string(r[:n]))\n\treturn r[n:], true\n")
    if k == "slice":
        return (f"\tn, r, ok := rpcGetU64(b)\n\tif !ok || n > uint64(len(r)) {{\n{fail}\t}}\n"
                f"\tif uint64(cap(*p)) < n {{\n\t\t*p = make({g}, n)\n\t}} else {{\n\t\t*p = (*p)[:n]\n\t}}\n"
                f"\tfor i := uint64(0); i < n; i++ {{\n"
                f"\t\tr, ok = rpcDec_{fn(e['elem'])}(r, &(*p)[i])\n\t\tif !ok {{\n\t{fail}\t\t}}\n\t}}\n"
                f"\treturn r, true\n")
    if k == "map":
        return (f"\tn, r, ok := rpcGetU64(b)\n\tif !ok || n > uint64(len(r)) {{\n{fail}\t}}\n"
                f"\tif *p == nil {{\n\t\t*p = make({g})\n\t}}\n"
                f"\tfor i := uint64(0); i < n; i++ {{\n"
                f"\t\tvar x {S.go(e['key'])}\n\t\tr, ok = rpcDec_{fn(e['key'])}(r, &x)\n\t\tif !ok {{\n\t{fail}\t\t}}\n"
                f"\t\tvar y {S.go(e['elem'])}\n\t\tr, ok = rpcDec_{fn(e['elem'])}(r, &y)\n\t\tif !ok {{\n\t{fail}\t\t}}\n"
                f"\t\t(*p)[x] = y\n\t}}\n\treturn r, true\n")
    if k == "struct":
        o = [f"\tif len(b) < 1 || b[0] != 1 {{\n{fail}\t}}\n\tr := b[1:]\n\tok := true\n"]
        for f in e["fields"]:
            if not f["exported"]:
                continue
            ft = S.t[f["type"]]
            o.append(f"\tif len(r) < 1 || r[0] > 1 {{\n{fail}\t}}\n\tif r[0] == 1 {{\n\t\tr = r[1:]\n")
            if ft["kind"] == "ptr":
                el = ft["elem"]
                o.append(f"\t\tif p.{f['name']} == nil {{\n\t\t\tp.{f['name']} = new({S.go(el)})\n\t\t}}\n"
                         f"\t\tr, ok = rpcDec_{fn(el)}(r, p.{f['name']})\n")
            else:
                o.append(f"\t\tr, ok = rpcDec_{fn(f['type'])}(r, &p.{f['name']})\n")
            o.append(f"\t\tif !ok {{\n\t{fail}\t\t}}\n\t}} else {{\n\t\tr = r[1:]\n\t}}\n")
        o.append("\treturn r, ok\n")
        return "".join(o)
    raise AssertionError(e)


def needs_sent(S):
    """The types whose rpcSent_ is used: struct field types, and pointer fields' elements."""
    out = set()
    for i in S.closure:
        e = S.t[i]
        if e["kind"] == "struct":
            for f in e["fields"]:
                if f["exported"]:
                    ft = S.t[f["type"]]
                    out.add(ft["elem"] if ft["kind"] == "ptr" else f["type"])
    return out


HELPERS = """
func rpcErrDecode() error {
	return errors.New("net/rpc model: malformed value")
}

func rpcPutU64(b []byte, x uint64) []byte {
	return append(b, byte(x), byte(x>>8), byte(x>>16), byte(x>>24), byte(x>>32), byte(x>>40),
		byte(x>>48), byte(x>>56))
}

func rpcGetU64(b []byte) (uint64, []byte, bool) {
	if len(b) < 8 {
		return 0, nil, false
	}
	x := uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
	return x, b[8:], true
}

func rpcGetTag(b []byte) (string, []byte, bool) {
	n, r, ok := rpcGetU64(b)
	if !ok || n > uint64(len(r)) {
		return "", nil, false
	}
	return string(r[:n]), r[n:], true
}

func rpcPutTag(tag string) []byte {
	b := rpcPutU64(nil, uint64(len(tag)))
	return append(b, tag...)
}
"""


def codec_go(S, header, pkg):
    imps = S.imports(receivers=False)
    o = [header, f"package {pkg}\n\nimport (\n\t\"errors\"\n"]
    if imps:
        o.append("\n")
    o.extend(f"\t{a} \"{p}\"\n" for a, p in imps)
    o.append(")\n\n// The net/rpc model's codec of this program's types (models/net/rpc/rpcgen.py; "
             "the encoding and\n// gob's decoding it reproduces: rpcgen_core.py's doc).\n")
    o.append(HELPERS)
    sent = needs_sent(S)
    for i in S.closure:
        g = S.go(i)
        o.append(f"\n// {fn(i)}: {S.tag(i)}\n\nfunc rpcEnc_{fn(i)}(b []byte, v {g}) []byte {{\n"
                 f"{enc_body(S, i)}}}\n")
        if i in sent:
            o.append(f"\nfunc rpcSent_{fn(i)}(v {g}) bool {{\n{sent_body(S, i)}}}\n")
        o.append(f"\nfunc rpcDec_{fn(i)}(b []byte, p *{g}) ([]byte, bool) {{\n{dec_body(S, i)}}}\n")
    enc, dec = [], []
    for i in S.roots:
        g, tag = S.go(i), S.tag(i)
        enc.append(f"\tcase {g}:\n\t\treturn rpcEnc_{fn(i)}(rpcPutTag({tag!r}), x)\n"
                   f"\tcase *{g}:\n\t\tif x == nil {{\n"
                   f"\t\t\trpcStuck() // MODEL: not modelled (stuck): net/rpc model: Encode of a nil *{g} (gob: cannot encode nil pointer)\n"
                   f"\t\t}}\n\t\treturn rpcEnc_{fn(i)}(rpcPutTag({tag!r}), *x)\n".replace("'", '"'))
        dec.append(f"\tcase *{g}:\n\t\tif p == nil {{\n"
                   f"\t\t\trpcStuck() // MODEL: not modelled (stuck): net/rpc model: Decode into a nil *{g}\n\t\t}}\n"
                   f"\t\tif tag != {tag!r} {{\n"
                   f"\t\t\trpcStuck() // MODEL: not modelled (stuck): net/rpc model: decoding a value of another type into a {g}\n"
                   f"\t\t}}\n\t\tr, ok2 := rpcDec_{fn(i)}(rest, p)\n"
                   f"\t\tif !ok2 || len(r) != 0 {{\n\t\t\treturn rpcErrDecode()\n\t\t}}\n"
                   f"\t\treturn nil\n".replace("'", '"'))
    o.append("""
// rpcEncode is the codec's Encode: a value of a listed type, or a non-nil pointer to one.
func rpcEncode(v any) []byte {
	switch x := v.(type) {
""" + "".join(enc) + """	}
	rpcStuck() // MODEL: not modelled (stuck): net/rpc model: Encode of a value of a type the codec does not list
	return nil // (not reached: rpcStuck does not return)
}

// rpcDecode is the codec's Decode: into a non-nil pointer to a value of a listed type, of the
// encoded value's type.
func rpcDecode(data []byte, ptr any) error {
	tag, rest, ok := rpcGetTag(data)
	if !ok {
		return rpcErrDecode()
	}
	switch p := ptr.(type) {
""" + "".join(dec) + """	}
	rpcStuck() // MODEL: not modelled (stuck): net/rpc model: Decode into a value of a type the codec does not list
	return nil // (not reached: rpcStuck does not return)
}
""")
    return "".join(o)


def model_go(S, header, pkg):
    """Register (the model build: tag netmodel, or goose, which goose always sets) and the
    receivers' table."""
    S.imports()
    paths = set()
    for r, ms in S.receivers:
        for i in [r["type"]] + [x for _, ai, _, ri in ms for x in (ai, ri)]:
            for p, a in S.alias.items():
                if S.uses(i, p):
                    paths.add((a, p))
    o = [header, f"//go:build netmodel || goose\n\npackage {pkg}\n\nimport (\n\trpcmodel \"net/rpc\"\n"]
    if paths:
        o.append("\n")
    o.extend(f"\t{a} \"{p}\"\n" for a, p in sorted(paths))
    o.append(""")

// Register registers this program's codec with the net/rpc model (in a model build: tag netmodel,
// or goose; rpc_real_gen.go's Register does nothing).
func Register() {
	rpcmodel.SetCodec(&rpcmodel.Codec{Encode: rpcEncode, Decode: rpcDecode, Receiver: rpcReceiver})
}
""")
    cases, funcs = [], []
    for n, (r, ms) in enumerate(S.receivers):
        rg = S.go(r["type"])
        nil = f"rcvr.({rg}) == nil" if r["pointer"] else "false"
        entries = "".join(f"\t\t\t\"{m}\": {{NewArg: rpcNewArg_r{n}_{m}, NewReply: rpcNewReply_r{n}_{m}, "
                          f"Call: rpcCall_r{n}_{m}}},\n" for m, _, _, _ in ms)
        cases.append(f"\tcase {rg}:\n\t\treturn &rpcmodel.Receiver{{Name: \"{r['name']}\", "
                     f"NilPtr: {nil}, Type: \"{r['string']}\", PtrHasMethods: "
                     f"{'true' if r['ptr_methods'] > 0 else 'false'}, Methods: map[string]*rpcmodel.Method{{\n"
                     f"{entries}\t\t}}}}\n")
        for m, ai, arg_ptr, ri in ms:
            ag, rgt = S.go(ai), S.go(ri)
            rk = S.t[ri]["kind"]
            mk = {"map": f"\t*r = make({rgt})\n", "slice": f"\t*r = make({rgt}, 0)\n"}.get(rk, "")
            arg = f"argv.(*{ag})" if arg_ptr else f"*argv.(*{ag})"
            funcs.append(f"\nfunc rpcNewArg_r{n}_{m}() any {{\n\treturn new({ag})\n}}\n"
                         f"\nfunc rpcNewReply_r{n}_{m}() any {{\n\tr := new({rgt})\n{mk}\treturn r\n}}\n"
                         f"\nfunc rpcCall_r{n}_{m}(rcvr, argv, replyv any) error {{\n"
                         f"\treturn rcvr.({rg}).{m}({arg}, replyv.(*{rgt}))\n}}\n")
    o.append("""
// rpcReceiver is the codec's Receiver: reflection's facts about a receiver of a listed type.
func rpcReceiver(rcvr any) *rpcmodel.Receiver {
	switch rcvr.(type) {
""" + "".join(cases) + """	}
	rpcStuck() // MODEL: not modelled (stuck): net/rpc model: Register of a receiver of a type the codec does not list
	return nil // (not reached: rpcStuck does not return)
}

// rpcStuck is the codec's not-modelled point: the net/rpc model's Stuck, which has no behavior
// (its Lean model is Perennial's stuck `Panic "not modelled"`; models/README.md, "Not modelled:
// stuck").
func rpcStuck() {
	rpcmodel.Stuck()
}
""")
    o.extend(funcs)
    return "".join(o)


def real_go(header, pkg):
    return header + f"""//go:build !netmodel && !goose

package {pkg}

// Register does nothing in a real build: net/rpc uses gob and reflection.
func Register() {{}}

// rpcStuck is the codec's not-modelled point (the model build's is the net/rpc model's Stuck): in a
// real build the codec runs only in its tests, where it blocks forever, as Stuck's Go body does.
func rpcStuck() {{
	select {{}}
}}
"""
