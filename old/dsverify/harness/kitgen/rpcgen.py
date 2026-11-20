"""rpcgen: the net/rpc model's codec for a kit (notes/craq-net.md decision 2), from kit.toml's [rpc].

The model of net/rpc (harness/rpcmodel) replaces gob and reflection by a Codec the kit registers:
encoders and decoders for exactly the listed types, and the dispatch table of the listed
receivers' methods. This module generates it, and the Go tests that check the trusted claims
against the real libraries: the listed structure of each type is the Go type's (reflection), the
listed methods are the ones net/rpc's reflection registers, a value of each type round-trips
through the model's codec exactly as through real gob, and for every pair of listed types the
model's decoder refuses an encoded value of one into the other exactly when gob does (and
otherwise gives gob's value).

[rpc] in kit.toml:

    [rpc]
    imports = { netrpc = "github.com/x/y/netrpc", ... }   # Go package aliases used below
    [rpc.types]                                           # every type passed to Call or a method
    "string" = "string"                                   #   (pointers flattened, as gob does)
    "netrpc.CommitArgs" = { struct = [["Key", "string"], ["Version", "uint64"]] }
    "transport.PropagateRequest" = "map[string]uint64"
    "[]transport.Item" = "[]transport.Item"
    [[rpc.service]]
    receiver = "*netrpc.NodeBinding"
    methods = [["Ping", "*netrpc.EmptyArgs", "*netrpc.EmptyReply"], ...]

A type's structure is a type expression over the basic types `string`, `[]byte`, `uint64`, `bool`,
`int`, `int32`, `int64`, `uint8`, `[]T`, `map[K]V` and the listed names, or a struct (its exported fields in order). A method's
argument type is a listed type or a pointer to one; its reply type a pointer to a listed type.
"""

import re

BASIC = {"string", "[]byte", "uint64", "bool", "int", "int32", "int64", "uint8"}

# the integer types other than uint64: (Go type, the wire's uint64 to the type, range check)
INTS = {
    "int": ("int", "int64(x)", "true"),
    "int32": ("int32", "int64(x)", "int64(x) >= -2147483648 && int64(x) <= 2147483647"),
    "int64": ("int64", "int64(x)", "true"),
    "uint8": ("uint8", "x", "x < 256"),
}


class RpcError(Exception):
    pass


def ident(name):
    """A Go identifier for a type name: netrpc.CommitArgs -> netrpc_CommitArgs."""
    return re.sub(r"[^A-Za-z0-9]", "_", name.replace("[]", "S_").replace("*", "P_"))


class Types:
    def __init__(self, rpc):
        self.imports = rpc.get("imports", {})
        self.decl = rpc.get("types", {})
        if not self.decl:
            raise RpcError("[rpc.types] is empty")
        self.names = list(self.decl)
        for n in self.names:
            self.check_name(n)
        self.tags = {n: i + 1 for i, n in enumerate(self.names)}
        for n in self.names:
            self.parse(self.struct_or_expr(n))
        self.services = rpc.get("service", [])
        # [rpc] name_total (default off; kits/gryff-net): rpcName returns "" for a receiver type
        # not listed (net/rpc's Register then fails: no service name), instead of panicking, so
        # that the harness's kitNameOk (nameOk: for every value) holds of the generated function
        self.name_total = rpc.get("name_total", False)
        # [rpc] map_nil (default off; kits/swift-net): a struct's map field is encoded with its
        # nil-ness, as gob distinguishes a nil map field (not sent: nil) from an empty one (sent:
        # an empty map); opt-in so that the other kits' generated codecs stay as they are
        self.map_nil = rpc.get("map_nil", False)
        # [rpc] gob (default off; kits/swift-net): the program sends values with encoding/gob
        # itself, which the lab's model of encoding/gob (harness/rpcmodel/src/encoding/gob) does
        # with this codec: registerRPC also registers it there, and goose and the model build use
        # goroot.sh's gob option; the model is translated with the target (lean.goose_pkgs and
        # lean.roots list encoding/gob)
        self.gob = rpc.get("gob", False)
        for s in self.services:
            r = s["receiver"]
            if not r.startswith("*") or not re.fullmatch(r"\w+\.\w+", r[1:]):
                raise RpcError(f"receiver {r!r}: a pointer to a named type (pkg.T)")
            for m in s["methods"]:
                if len(m) != 3 or not re.fullmatch(r"[A-Z]\w*", m[0]):
                    raise RpcError(f"{r}: method {m!r}: [name, arg type, reply type]")
                if m[1].lstrip("*") not in self.decl or m[1].count("*") > 1:
                    raise RpcError(f"{r}.{m[0]}: argument {m[1]!r}: a listed type or a pointer to one")
                if not m[2].startswith("*") or m[2][1:] not in self.decl:
                    raise RpcError(f"{r}.{m[0]}: reply {m[2]!r}: a pointer to a listed type")

    def check_name(self, n):
        if n in BASIC:
            return
        m = re.fullmatch(r"(\[\])?(\w+)\.(\w+)", n)
        if not m or m.group(2) not in self.imports:
            raise RpcError(f"type {n!r}: a basic type, pkg.T or []pkg.T with pkg in [rpc].imports")

    def struct_or_expr(self, n):
        d = self.decl[n]
        if isinstance(d, dict):
            if set(d) != {"struct"}:
                raise RpcError(f"type {n}: {{ struct = [[field, type], ...] }}")
            if n.startswith("[]") or n in BASIC:
                raise RpcError(f"type {n}: only a named type is a struct")
            return ("struct", [(f, self.parse(t)) for f, t in d["struct"]])
        if n == d and (n in BASIC or n.startswith("[]")):
            return self.parse_expr(d, top=True)
        if n in BASIC or n.startswith("[]"):
            raise RpcError(f"type {n}: its structure is {n!r} itself")
        return self.parse_expr(d, top=True)

    def parse(self, t):
        if isinstance(t, tuple):
            return t
        return self.parse_expr(t)

    def parse_expr(self, t, top=False):
        """A type expression: ('basic', b) | ('slice', T) | ('map', K, V) | ('named', n)."""
        t = t.strip()
        if t in BASIC:
            return ("basic", t)
        if t.startswith("[]"):
            return ("slice", self.parse_expr(t[2:]))
        if t.startswith("map["):
            depth, i = 0, 3
            while True:
                if t[i] == "[":
                    depth += 1
                elif t[i] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            return ("map", self.parse_expr(t[4:i]), self.parse_expr(t[i + 1:]))
        if t in self.decl:
            if top:
                raise RpcError(f"type {t}: a named type's structure must not be another name")
            return ("named", t)
        raise RpcError(f"type expression {t!r}: unknown (list it in [rpc.types])")

    def shape(self, n):
        """The type's structure: a struct's fields, or the expression (named types resolved)."""
        return self.struct_or_expr(n)

    def resolve(self, e):
        while e[0] == "named":
            e = self.shape(e[1])
        return e

    def gotype(self, e):
        """The Go type of an expression (a listed name is its own Go type)."""
        k = e[0]
        if k == "basic":
            return e[1]
        if k == "slice":
            return "[]" + self.gotype(e[1])
        if k == "map":
            return f"map[{self.gotype(e[1])}]{self.gotype(e[2])}"
        if k == "named":
            return e[1]
        raise RpcError(f"no Go type for {e}")

    def canon(self, e):
        """The canonical structure string the generated test computes by reflection."""
        e = self.resolve(e)
        k = e[0]
        if k == "basic":
            return {"[]byte": "[]uint8"}.get(e[1], e[1])
        if k == "slice":
            return "[]" + self.canon(e[1])
        if k == "map":
            return f"map[{self.canon(e[1])}]{self.canon(e[2])}"
        if k == "struct":
            return "struct{" + ";".join(f"{f} {self.canon(t)}" for f, t in e[1]) + "}"
        raise RpcError(f"canon {e}")

    def is_struct(self, n):
        return self.shape(n)[0] == "struct"

    def compat(self, w, l):
        """How gob decodes a value of listed type w into listed type l (w != l): None (an error),
        or a Go expression converting `w` (a value of w's type) into l's type."""
        sw, sl = self.shape(w), self.shape(l)
        if sw[0] == "struct" and sl[0] == "struct":
            fw, fl = dict(sw[1]), dict(sl[1])
            common = [f for f, _ in sl[1] if f in fw]
            if not common:
                # gob: "no fields matched" only when both have fields
                if fw and fl:
                    return None
                return f"{l}{{}}"
            for f in common:
                if self.canon(fw[f]) != self.canon(fl[f]):
                    return None
                if self.gotype(fw[f]) != self.gotype(fl[f]):
                    return None      # same structure, different Go types: not supported (none yet)
            return f"{l}{{" + ", ".join(f"{f}: w.{f}" for f in common) + "}"
        if sw[0] == "struct" or sl[0] == "struct":
            return None
        if self.canon(sw) == self.canon(sl):
            return f"{l}(w)"
        return None


# ---------------------------------------------------------------------------------------------
# Go generation


def gen_codec_go(T, header, pkg):
    """The codec (no build tag; it builds against real gob too, for the tests)."""
    imps = "".join(f"\t{a} \"{p}\"\n" for a, p in sorted(T.imports.items()))
    o = [header, f"package {pkg}\n\nimport (\n\t\"errors\"\n\n{imps})\n"]
    o.append("""
// The net/rpc model's codec for this kit (harness/kitgen/rpcgen.py, kit.toml's [rpc]): a value is
// its type's tag and its encoding; strings and byte slices are a length and the bytes, uint64s 8
// bytes little-endian, bools a byte, slices and maps a count and the elements, structs their
// fields in order. Decoding follows gob: empty slices decode as nil, maps in struct fields too;
// a value of one listed type decodes into another as gob would (rpc_gen_test.go checks both).

func rpcErrDecode() error {
	return errors.New("rpc model: malformed value")
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
""")
    o.append("\n// The listed types' tags.\nconst (\n")
    for n in T.names:
        o.append(f"\trpcTag_{ident(n)} uint64 = {T.tags[n]}\n")
    o.append(")\n")
    # encoders/decoders for every expression that occurs
    exprs = {}

    def collect(e):
        k = e[0]
        key = T.gotype(e) if k != "struct" else None
        if k == "struct":
            for _, t in e[1]:
                collect(t)
            return
        if key in exprs:
            return
        exprs[key] = e
        if k == "slice":
            collect(e[1])
        elif k == "map":
            collect(e[1])
            collect(e[2])
        elif k == "named":
            collect(T.shape(e[1]))

    for n in T.names:
        collect(("named", n) if n not in BASIC and not n.startswith("[]") else T.parse_expr(n))
    fn = lambda e: ident(T.gotype(e))       # noqa: E731
    for key, e in exprs.items():
        o.append(gen_encdec(T, e, fn))
    # zero checks and merges of listed types (Decode's target)
    for n in T.names:
        o.append(gen_zero_merge(T, n, fn))
    # DecodeAs per listed type
    for n in T.names:
        o.append(gen_decode_as(T, n, fn))
    o.append(gen_top(T, fn))
    o.append(gen_dispatch(T, fn))
    return "".join(o)


def enc_expr(T, e, b, v, fn):
    return f"rpcEnc_{fn(e)}({b}, {v})"


def gen_encdec(T, e, fn):
    k, g, f = e[0], T.gotype(e), fn(e)
    if k == "basic":
        b = e[1]
        if b == "string":
            return f"""
func rpcEnc_{f}(b []byte, v string) []byte {{
	b = rpcPutU64(b, uint64(len(v)))
	return append(b, []byte(v)...)
}}

func rpcDec_{f}(b []byte) (string, []byte, bool) {{
	n, r, ok := rpcGetU64(b)
	if !ok || n > uint64(len(r)) {{
		return "", nil, false
	}}
	return string(r[:n]), r[n:], true
}}
"""
        if b == "[]byte":
            return f"""
func rpcEnc_{f}(b []byte, v []byte) []byte {{
	b = rpcPutU64(b, uint64(len(v)))
	return append(b, v...)
}}

func rpcDec_{f}(b []byte) ([]byte, []byte, bool) {{
	n, r, ok := rpcGetU64(b)
	if !ok || n > uint64(len(r)) {{
		return nil, nil, false
	}}
	if n == 0 {{
		return nil, r, true
	}}
	v := make([]byte, n)
	copy(v, r[:n])
	return v, r[n:], true
}}
"""
        if b == "uint64":
            return f"""
func rpcEnc_{f}(b []byte, v uint64) []byte {{
	return rpcPutU64(b, v)
}}

func rpcDec_{f}(b []byte) (uint64, []byte, bool) {{
	return rpcGetU64(b)
}}
"""
        if b in INTS:
            gt, conv, ok = INTS[b]
            return f"""
func rpcEnc_{f}(b []byte, v {gt}) []byte {{
	return rpcPutU64(b, uint64(v))
}}

func rpcDec_{f}(b []byte) ({gt}, []byte, bool) {{
	x, r, ok := rpcGetU64(b)
	if !ok || !({ok}) {{
		return 0, nil, false
	}}
	return {gt}({conv}), r, true
}}
"""
        if b == "bool":
            return f"""
func rpcEnc_{f}(b []byte, v bool) []byte {{
	if v {{
		return append(b, 1)
	}}
	return append(b, 0)
}}

func rpcDec_{f}(b []byte) (bool, []byte, bool) {{
	if len(b) < 1 || b[0] > 1 {{
		return false, nil, false
	}}
	return b[0] == 1, b[1:], true
}}
"""
    if k == "slice":
        el = e[1]
        return f"""
func rpcEnc_{f}(b []byte, v {g}) []byte {{
	b = rpcPutU64(b, uint64(len(v)))
	for _, x := range v {{
		b = rpcEnc_{fn(el)}(b, x)
	}}
	return b
}}

func rpcDec_{f}(b []byte) ({g}, []byte, bool) {{
	n, r, ok := rpcGetU64(b)
	if !ok || n > uint64(len(r)) {{
		return nil, nil, false
	}}
	var v {g}
	for i := uint64(0); i < n; i++ {{
		x, r2, ok2 := rpcDec_{fn(el)}(r)
		if !ok2 {{
			return nil, nil, false
		}}
		v = append(v, x)
		r = r2
	}}
	return v, r, true
}}
"""
    if k == "map":
        ke, ve = e[1], e[2]
        return f"""
func rpcEnc_{f}(b []byte, v {g}) []byte {{
	b = rpcPutU64(b, uint64(len(v)))
	for x, y := range v {{
		b = rpcEnc_{fn(ke)}(b, x)
		b = rpcEnc_{fn(ve)}(b, y)
	}}
	return b
}}

func rpcDec_{f}(b []byte) ({g}, []byte, bool) {{
	n, r, ok := rpcGetU64(b)
	if !ok || n > uint64(len(r)) {{
		return nil, nil, false
	}}
	v := make({g})
	for i := uint64(0); i < n; i++ {{
		x, r2, ok2 := rpcDec_{fn(ke)}(r)
		if !ok2 {{
			return nil, nil, false
		}}
		y, r3, ok3 := rpcDec_{fn(ve)}(r2)
		if !ok3 {{
			return nil, nil, false
		}}
		v[x] = y
		r = r3
	}}
	return v, r, true
}}
"""
    if k == "named":
        n = e[1]
        s = T.shape(n)
        if s[0] != "struct":
            return f"""
func rpcEnc_{f}(b []byte, v {n}) []byte {{
	return rpcEnc_{fn(s)}(b, {T.gotype(s)}(v))
}}

func rpcDec_{f}(b []byte) ({n}, []byte, bool) {{
	v, r, ok := rpcDec_{fn(s)}(b)
	return {n}(v), r, ok
}}
"""
        # a map field: with [rpc] map_nil (swift-net's MSync), a byte saying whether it is nil
        # first, as gob sends an empty map field but not a nil one (an empty one decodes as an
        # empty map); without, an empty map field decodes as nil (the kits before map_nil, whose
        # codecs do not change)
        enc = ""
        dec = ""
        r = "b"
        for i, (fl, t) in enumerate(s[1]):
            ismap = T.resolve(t)[0] == "map"
            if ismap and T.map_nil:
                enc += (f"\tif v.{fl} == nil {{\n\t\tb = append(b, 0)\n\t}} else {{\n"
                        f"\t\tb = append(b, 1)\n\t\tb = rpcEnc_{fn(t)}(b, v.{fl})\n\t}}\n")
                dec += (f"\tvar f{i} {T.gotype(t)}\n\tr{i} := {r}\n"
                        f"\tok{i} := len({r}) > 0 && {r}[0] <= 1\n"
                        f"\tif ok{i} {{\n\t\tr{i} = {r}[1:]\n"
                        f"\t\tif {r}[0] == 1 {{\n\t\t\tf{i}, r{i}, ok{i} = rpcDec_{fn(t)}(r{i})\n\t\t}}\n\t}}\n"
                        f"\tif !ok{i} {{\n\t\treturn {n}{{}}, nil, false\n\t}}\n")
            else:
                enc += f"\tb = rpcEnc_{fn(t)}(b, v.{fl})\n"
                dec += (f"\tf{i}, r{i}, ok{i} := rpcDec_{fn(t)}({r})\n"
                        f"\tif !ok{i} {{\n\t\treturn {n}{{}}, nil, false\n\t}}\n")
                if ismap:
                    dec += f"\tif len(f{i}) == 0 {{\n\t\tf{i} = nil\n\t}}\n"
            r = f"r{i}"
        fields = ", ".join(f"{fl}: f{i}" for i, (fl, _) in enumerate(s[1]))
        return f"""
func rpcEnc_{f}(b []byte, v {n}) []byte {{
{enc}	return b
}}

func rpcDec_{f}(b []byte) ({n}, []byte, bool) {{
{dec}	return {n}{{{fields}}}, {r}, true
}}
"""
    raise RpcError(f"gen_encdec {e}")


def zero_test(T, e, v):
    r = T.resolve(e)
    k = r[0]
    if k == "basic":
        return {"string": f'{v} == ""', "uint64": f"{v} == 0", "bool": f"!{v}",
                "[]byte": f"len({v}) == 0", "int": f"{v} == 0", "int32": f"{v} == 0",
                "int64": f"{v} == 0", "uint8": f"{v} == 0"}[r[1]]
    if k in ("slice", "map"):
        return f"len({v}) == 0"
    if k == "struct":
        parts = [zero_test(T, t, f"{v}.{fl}") for fl, t in r[1]]
        return " && ".join(parts) if parts else "true"
    raise RpcError(f"zero {e}")


def merge_exact(T, e):
    """Whether rpcMerge is gob's decoding into any value of the type, not only a zero one: a
    basic type, a slice of basic values (gob sends every element of a non-empty slice and sets
    the length), or a struct whose fields are such (gob leaves the fields it does not send, the
    zero ones and empty slices, as they were). Not a map (gob adds the entries to the target's
    map, decoding each value into a fresh one), and not a struct or slice of structs or maps (gob
    merges into the target's nested values field by field)."""
    def flat(x):
        r = T.resolve(x)
        return r[0] == "basic" or (r[0] == "slice" and T.resolve(r[1])[0] == "basic")
    r = T.resolve(e)
    if r[0] == "struct":
        return all(flat(t) for _, t in r[1])
    if e[0] == "named" and r == ("basic", "[]byte"):
        # a named []byte (state.Value) decoded on its own: gob sets an empty one, which the
        # field-wise merge (empty slices leave the target's) does not; only zero targets
        return False
    return flat(e)


def gen_zero_merge(T, n, fn):
    e = T.parse_expr(n) if (n in BASIC or n.startswith("[]")) else ("named", n)
    s = T.resolve(e)
    f = ident(n)
    z = zero_test(T, e, "v")
    if s[0] == "struct":
        # with map_nil, an empty map field was sent (gob's) and is stored; a nil one was not
        def sent(fl, t):
            if T.map_nil and T.resolve(t)[0] == "map":
                return f"v.{fl} != nil"
            return f"!({zero_test(T, t, 'v.' + fl)})"
        merge = "".join(f"\tif {sent(fl, t)} {{\n\t\tp.{fl} = v.{fl}\n\t}}\n"
                        for fl, t in s[1])
    elif s[0] == "map":
        merge = ("\tif *p == nil {\n\t\t*p = v\n\t\treturn\n\t}\n"
                 "\tfor x, y := range v {\n\t\t(*p)[x] = y\n\t}\n")
    elif s[0] == "slice" or s == ("basic", "[]byte"):
        merge = "\tif len(v) != 0 {\n\t\t*p = v\n\t}\n"
    else:
        merge = "\t*p = v\n"
    return f"""
func rpcZero_{f}(v {n}) bool {{
	return {z}
}}

// rpcMerge_{f} stores the decoded v into *p as gob does: fields gob does not send
// (zero ones) and empty slices leave *p's; a map's entries go into *p's map if it has one.
func rpcMerge_{f}(p *{n}, v {n}) {{
{merge}}}
"""


def gen_decode_as(T, l, fn):
    f = ident(l)
    le = T.parse_expr(l) if (l in BASIC or l.startswith("[]")) else ("named", l)
    zero = {"string": '""', "uint64": "0", "bool": "false", "int": "0", "int32": "0",
            "int64": "0", "uint8": "0"}.get(l, None)
    if zero is None:
        r = T.resolve(le)
        if r[0] == "basic":
            # a named type over a basic one (state.Key = int64): that type's zero
            zero = {"string": '""', "bool": "false", "[]byte": "nil"}.get(r[1], "0")
        else:
            zero = "nil" if r[0] in ("slice", "map") or l == "[]byte" else f"{l}{{}}"
    o = [f"""
// rpcDecodeAs_{f} decodes an encoded value (its tag first) as a {l}, as gob would.
func rpcDecodeAs_{f}(data []byte) ({l}, error) {{
	tag, rest, ok := rpcGetU64(data)
	if !ok {{
		return {zero}, rpcErrDecode()
	}}
	if tag == rpcTag_{f} {{
		v, r, ok2 := rpcDec_{fn(le)}(rest)
		if !ok2 || len(r) != 0 {{
			return {zero}, rpcErrDecode()
		}}
		return v, nil
	}}
"""]
    for w in T.names:
        if w == l:
            continue
        conv = T.compat(w, l)
        if conv is None:
            continue
        we = T.parse_expr(w) if (w in BASIC or w.startswith("[]")) else ("named", w)
        wv = "w" if ("w." in conv or "(w)" in conv) else "_"
        o.append(f"""	if tag == rpcTag_{ident(w)} {{
		{wv}, r, ok2 := rpcDec_{fn(we)}(rest)
		if !ok2 || len(r) != 0 {{
			return {zero}, rpcErrDecode()
		}}
		return {conv}, nil
	}}
""")
    o.append(f'\treturn {zero}, errors.New("gob: decoding into local type {l}: a value of an '
             'incompatible type")\n}\n')
    return "".join(o)


def gen_top(T, fn):
    enc, dec = [], []
    for n in T.names:
        f = ident(n)
        e = T.parse_expr(n) if (n in BASIC or n.startswith("[]")) else ("named", n)
        enc.append(f"""	case {n}:
		return rpcEnc_{fn(e)}(rpcPutU64(nil, rpcTag_{f}), x)
	case *{n}:
		if x == nil {{
			panic("gob: cannot encode nil pointer of type *{n}")
		}}
		return rpcEnc_{fn(e)}(rpcPutU64(nil, rpcTag_{f}), *x)
""")
        zc = "" if merge_exact(T, e) else f"""		if !rpcZero_{f}(*p) {{
			panic("rpc model: Decode into a non-zero {n}")
		}}
"""
        dec.append(f"""	case *{n}:
		if p == nil {{
			panic("rpc model: Decode into a nil *{n}")
		}}
{zc}		v, err := rpcDecodeAs_{f}(data)
		if err != nil {{
			return err
		}}
		rpcMerge_{f}(p, v)
		return nil
""")
    return ("""
// rpcEncode is the codec's Encode: a listed type or a non-nil pointer to one.
func rpcEncode(v interface{}) []byte {
	switch x := v.(type) {
""" + "".join(enc) + """	}
	panic("rpc model: Encode of a type not in kit.toml's [rpc.types]")
}

// rpcDecode is the codec's Decode: into a non-nil pointer to a value of a listed type, a zero one
// unless the type's merge is gob's for any value (merge_exact in kitgen's rpcgen.py: basic values,
// slices of them, and structs of those), as when SwiftPaxos's master decodes into a reply whose
// fields are -1.
func rpcDecode(data []byte, ptr interface{}) error {
	switch p := ptr.(type) {
""" + "".join(dec) + """	}
	panic("rpc model: Decode into a type not in kit.toml's [rpc.types]")
}
""")


def gen_dispatch(T, fn):
    meth, call, bodies, names = [], [], [], []
    for s in T.services:
        r = s["receiver"]
        rf = ident(r[1:])
        meth.append(f"\tcase {r}:\n\t\treturn {len(s['methods'])}\n")
        names.append(f"\tcase {r}:\n\t\treturn \"{r.split('.')[-1]}\"\n")
        cs = "".join(f"\t\tif method == \"{m}\" {{\n\t\t\treturn rpcCall_{rf}_{m}(r, args)\n\t\t}}\n"
                     for m, _, _ in s["methods"])
        call.append(f"\tcase {r}:\n{cs}\t\treturn nil, \"\", false\n")
        for m, a, rep in s["methods"]:
            at, rt = a.lstrip("*"), rep[1:]
            arg = "&a" if a.startswith("*") else "a"
            re_ = T.parse_expr(rt) if (rt in BASIC or rt.startswith("[]")) else ("named", rt)
            bodies.append(f"""
func rpcCall_{rf}_{m}(r {r}, data []byte) ([]byte, string, bool) {{
	a, err := rpcDecodeAs_{ident(at)}(data)
	if err != nil {{
		return nil, err.Error(), true
	}}
	rep := new({rt})
	if err2 := r.{m}({arg}, rep); err2 != nil {{
		return nil, err2.Error(), true
	}}
	return rpcEnc_{fn(re_)}(rpcPutU64(nil, rpcTag_{ident(rt)}), *rep), "", true
}}
""")
    return ("""
// rpcMethods is the codec's Methods: how many methods net/rpc registers for a listed receiver.
func rpcMethods(rcvr interface{}) uint64 {
	switch rcvr.(type) {
""" + "".join(meth) + """	}
	panic("rpc model: a receiver type not in kit.toml's [[rpc.service]]")
}

// rpcName is the codec's Name: the service name net/rpc's Register gives a listed receiver (its
// type's name)""" + (""", and "" for any other value (Register then fails).
func rpcName(rcvr interface{}) string {
	switch rcvr.(type) {
""" + "".join(names) + """	}
	return ""
}
""" if T.name_total else """.
func rpcName(rcvr interface{}) string {
	switch rcvr.(type) {
""" + "".join(names) + """	}
	panic("rpc model: a receiver type not in kit.toml's [[rpc.service]]")
}
""") + """
// rpcCall is the codec's Call: the dispatch table of the listed receivers' methods.
func rpcCall(rcvr interface{}, method string, args []byte) ([]byte, string, bool) {
	switch r := rcvr.(type) {
""" + "".join(call) + """	}
	panic("rpc model: a receiver type not in kit.toml's [[rpc.service]]")
}
""" + "".join(bodies))


def gen_register_model(header, pkg, gob=False):
    if gob:
        # [rpc] gob = true (kits/swift-net): the encoding/gob model gets the same codec
        return header + f"""//go:build rpcmodel || goose

package {pkg}

import (
	"encoding/gob"
	"net/rpc"
)

// registerRPC registers the kit's codec with the net/rpc model and with the encoding/gob model
// (built for the model only: the theorem's build, tag goose, which goose always sets and which
// overrides GOFLAGS' tags, and model-mode tests, tag rpcmodel, with a GOROOT whose encoding/gob
// is the model, harness/rpcmodel/goroot.sh OUT gob; rpc_real_gen.go is the real build's).
func registerRPC() {{
	rpc.SetCodec(&rpc.Codec{{Encode: rpcEncode, Decode: rpcDecode, Methods: rpcMethods,
		Call: rpcCall, Name: rpcName}})
	gob.SetCodec(&gob.Codec{{Encode: rpcEncode, Decode: rpcDecode}})
}}
"""
    return header + f"""//go:build rpcmodel || goose

package {pkg}

import "net/rpc"

// registerRPC registers the kit's codec with the net/rpc model (built for the model only: the
// theorem's build, tag goose, which goose always sets and which overrides GOFLAGS' tags, and
// model-mode tests, tag rpcmodel; rpc_real_gen.go is the real build's).
func registerRPC() {{
	rpc.SetCodec(&rpc.Codec{{Encode: rpcEncode, Decode: rpcDecode, Methods: rpcMethods,
		Call: rpcCall, Name: rpcName}})
}}
"""


def gen_register_real(header, pkg, gob=False):
    what = "net/rpc and encoding/gob use" if gob else "net/rpc uses"
    return header + f"""//go:build !rpcmodel && !goose

package {pkg}

// registerRPC does nothing in the real build: {what} gob and reflection.
func registerRPC() {{}}
"""


def nonzero_case(n, g):
    """The round-trip test's decoding into a non-zero value (the same random value twice, from the
    same seed), for a type whose model decodes into any value (merge_exact)."""
    return f"""			{{
				r1, r2 := rand.New(rand.NewSource(int64(i))), rand.New(rand.NewSource(int64(i)))
				real3, model3 := new({n}), new({n})
				*real3, *model3 = rpcRand_{g}(r1), rpcRand_{g}(r2)
				if err := rpcGob(v, real3); err != nil {{
					t.Fatalf("{n} into a non-zero value: gob: %v", err)
				}}
				if err := rpcDecode(rpcEncode(v), model3); err != nil || !reflect.DeepEqual(real3, model3) {{
					t.Fatalf("{n} %#v into a non-zero value: gob gives %#v, the model %#v (%v)", v, *real3, *model3, err)
				}}
			}}
"""


def gen_test_go(T, header, pkg):
    imps = "".join(f"\t{a} \"{p}\"\n" for a, p in sorted(T.imports.items()))
    # rpcShape's int64 case, only for a kit that lists an int64 (the other kits' tests unchanged)
    uses64 = any(re.search(r"\bint64\b", repr(T.decl[n])) for n in T.names)
    i64 = '\tcase reflect.Int64:\n\t\treturn "int64"\n' if uses64 else ""
    o = [header, f"""//go:build !rpcmodel && !goose

package {pkg}

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"math/rand"
	"reflect"
	"sort"
	"strings"
	"testing"

{imps})

// The trusted claims of the kit's net/rpc codec (notes/craq-net.md decision 2), against the real
// libraries: each listed type's structure, the methods net/rpc registers, round trips through
// real gob, and gob's (in)compatibility of every pair of listed types.

func rpcShape(t reflect.Type) string {{
	switch t.Kind() {{
	case reflect.String:
		return "string"
	case reflect.Uint64:
		return "uint64"
	case reflect.Int:
		return "int"
	case reflect.Int32:
		return "int32"
{i64}	case reflect.Uint8:
		return "uint8"
	case reflect.Bool:
		return "bool"
	case reflect.Slice:
		return "[]" + rpcShape(t.Elem())
	case reflect.Map:
		return "map[" + rpcShape(t.Key()) + "]" + rpcShape(t.Elem())
	case reflect.Struct:
		var fs []string
		for i := 0; i < t.NumField(); i++ {{
			fs = append(fs, t.Field(i).Name+" "+rpcShape(t.Field(i).Type))
		}}
		return "struct{{" + strings.Join(fs, ";") + "}}"
	}}
	return "unsupported " + t.String()
}}

func TestRPCTypes(t *testing.T) {{
	want := map[string]string{{
"""]
    for n in T.names:
        e = T.parse_expr(n) if (n in BASIC or n.startswith("[]")) else ("named", n)
        o.append(f'\t\t"{n}": "{T.canon(e)}",\n')
    o.append("\t}\n\tgot := map[string]string{\n")
    for n in T.names:
        o.append(f'\t\t"{n}": rpcShape(reflect.TypeOf((*{n})(nil)).Elem()),\n')
    o.append("""	}
	for n, w := range want {
		if got[n] != w {
			t.Errorf("type %s: kit.toml says %s, Go has %s", n, w, got[n])
		}
	}
}

// rpcSuitable is net/rpc's suitableMethods (server.go): exported methods func(T1, *T2) error
// with T1, T2 exported or builtin.
func rpcSuitable(typ reflect.Type) []string {
	exported := func(t reflect.Type) bool {
		for t.Kind() == reflect.Pointer {
			t = t.Elem()
		}
		return t.PkgPath() == "" || (t.Name() != "" && t.Name()[0] >= 'A' && t.Name()[0] <= 'Z')
	}
	errT := reflect.TypeOf((*error)(nil)).Elem()
	var ms []string
	for i := 0; i < typ.NumMethod(); i++ {
		m := typ.Method(i)
		mt := m.Type
		if !m.IsExported() || mt.NumIn() != 3 || mt.NumOut() != 1 || mt.Out(0) != errT {
			continue
		}
		if !exported(mt.In(1)) || mt.In(2).Kind() != reflect.Pointer || !exported(mt.In(2)) {
			continue
		}
		ms = append(ms, m.Name+" "+mt.In(1).String()+" "+mt.In(2).String())
	}
	sort.Strings(ms)
	return ms
}

func TestRPCMethods(t *testing.T) {
""")
    for s in T.services:
        r = s["receiver"]
        want = sorted(f"{m} {a} {rep}" for m, a, rep in s["methods"])
        o.append(f"\t{{\n\t\twant := []string{{{', '.join(repr(w).replace(chr(39), chr(34)) for w in want)}}}\n"
                 f"\t\tgot := rpcSuitable(reflect.TypeOf(({r})(nil)))\n"
                 f"\t\tif fmt.Sprint(got) != fmt.Sprint(want) {{\n"
                 f"\t\t\tt.Errorf(\"{r}: kit.toml lists %v, net/rpc registers %v\", want, got)\n"
                 f"\t\t}}\n\t\tif rpcMethods(({r})(nil)) != uint64(len(want)) {{\n"
                 f"\t\t\tt.Errorf(\"{r}: rpcMethods\")\n\t\t}}\n"
                 f"\t\tif n := reflect.TypeOf(({r})(nil)).Elem().Name(); rpcName(({r})(nil)) != n {{\n"
                 f"\t\t\tt.Errorf(\"{r}: rpcName is %q, net/rpc's Register uses %q\", rpcName(({r})(nil)), n)\n"
                 f"\t\t}}\n\t}}\n")
    o.append("}\n")
    # random values
    rexprs = {}

    def collect(e):
        g = T.gotype(e)
        if e[0] == "struct" or g in rexprs:
            return
        rexprs[g] = e
        if e[0] == "slice":
            collect(e[1])
        elif e[0] == "map":
            collect(e[1])
            collect(e[2])
        elif e[0] == "named":
            s = T.shape(e[1])
            if s[0] == "struct":
                for _, t in s[1]:
                    collect(t)
            else:
                collect(s)

    tops = []
    for n in T.names:
        e = T.parse_expr(n) if (n in BASIC or n.startswith("[]")) else ("named", n)
        tops.append((n, e))
        collect(e)
    for g, e in rexprs.items():
        f = ident(g)
        k = e[0]
        if k == "basic":
            body = {"string": '\tif r.Intn(3) == 0 {\n\t\treturn ""\n\t}\n\treturn fmt.Sprint("s", r.Intn(1000))\n',
                    "uint64": "\tif r.Intn(3) == 0 {\n\t\treturn 0\n\t}\n\treturn r.Uint64()\n",
                    "bool": "\treturn r.Intn(2) == 0\n",
                    "int": "\tif r.Intn(3) == 0 {\n\t\treturn 0\n\t}\n\treturn int(r.Uint64())\n",
                    "int32": "\tif r.Intn(3) == 0 {\n\t\treturn 0\n\t}\n\treturn int32(r.Uint32())\n",
                    "int64": "\tif r.Intn(3) == 0 {\n\t\treturn 0\n\t}\n\treturn int64(r.Uint64())\n",
                    "uint8": "\tif r.Intn(3) == 0 {\n\t\treturn 0\n\t}\n\treturn uint8(r.Intn(256))\n",
                    "[]byte": "\tswitch r.Intn(4) {\n\tcase 0:\n\t\treturn nil\n\tcase 1:\n\t\treturn []byte{}\n\t}\n"
                              "\tb := make([]byte, 1+r.Intn(4))\n\tr.Read(b)\n\treturn b\n"}[e[1]]
        elif k == "slice":
            body = (f"\tswitch r.Intn(4) {{\n\tcase 0:\n\t\treturn nil\n\tcase 1:\n\t\treturn {g}{{}}\n\t}}\n"
                    f"\tvar v {g}\n\tfor i := r.Intn(4); i >= 0; i-- {{\n"
                    f"\t\tv = append(v, rpcRand_{ident(T.gotype(e[1]))}(r))\n\t}}\n\treturn v\n")
        elif k == "map":
            body = (f"\tswitch r.Intn(4) {{\n\tcase 0:\n\t\treturn nil\n\tcase 1:\n\t\treturn {g}{{}}\n\t}}\n"
                    f"\tv := {g}{{}}\n\tfor i := r.Intn(4); i >= 0; i-- {{\n"
                    f"\t\tv[rpcRand_{ident(T.gotype(e[1]))}(r)] = rpcRand_{ident(T.gotype(e[2]))}(r)\n"
                    "\t}\n\treturn v\n")
        else:
            s = T.shape(e[1])
            if s[0] == "struct":
                fs = ", ".join(f"{fl}: rpcRand_{ident(T.gotype(t))}(r)" for fl, t in s[1])
                body = f"\treturn {g}{{{fs}}}\n"
            else:
                body = f"\treturn {g}(rpcRand_{ident(T.gotype(s))}(r))\n"
        o.append(f"\nfunc rpcRand_{f}(r *rand.Rand) {g} {{\n{body}}}\n")
    # round trips and compatibility
    o.append("""
func rpcGob(v interface{}, into interface{}) error {
	var b bytes.Buffer
	if err := gob.NewEncoder(&b).Encode(v); err != nil {
		return err
	}
	return gob.NewDecoder(&b).Decode(into)
}

const rpcSamples = 300

func TestRPCRoundTrip(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for i := 0; i < rpcSamples; i++ {
""")
    for n, e in tops:
        g = ident(T.gotype(e))
        o.append(f"""		{{
			v := rpcRand_{g}(r)
			if i == 0 {{
				var z {n}
				v = z
			}}
			real, model := new({n}), new({n})
			if err := rpcGob(v, real); err != nil {{
				t.Fatalf("{n}: gob: %v", err)
			}}
			if err := rpcDecode(rpcEncode(v), model); err != nil {{
				t.Fatalf("{n}: model: %v", err)
			}}
			if !reflect.DeepEqual(real, model) {{
				t.Fatalf("{n} %#v: gob gives %#v, the model %#v", v, *real, *model)
			}}
			model2 := new({n})
			if err := rpcDecode(rpcEncode(&v), model2); err != nil || !reflect.DeepEqual(real, model2) {{
				t.Fatalf("*{n} %#v: gob gives %#v, the model %#v (%v)", v, *real, *model2, err)
			}}
{{nz}}		}}
""".replace("{nz}", nonzero_case(n, g) if merge_exact(T, e) else ""))
    o.append("""	}
}

func TestRPCCompat(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	for i := 0; i < rpcSamples; i++ {
""")
    for w, we in tops:
        for l, _ in tops:
            if w == l:
                continue
            o.append(f"""		{{
			v := rpcRand_{ident(T.gotype(we))}(r)
			real, model := new({l}), new({l})
			errR := rpcGob(v, real)
			errM := rpcDecode(rpcEncode(v), model)
			if (errR == nil) != (errM == nil) || (errR == nil && !reflect.DeepEqual(real, model)) {{
				t.Fatalf("{w} %#v into {l}: gob gives %#v (%v), the model %#v (%v)", v, *real, errR, *model, errM)
			}}
		}}
""")
    o.append("\t}\n}\n")
    return "".join(o)


def audit_lines(T):
    """The audit's summary of [rpc]: the types and the methods (the trusted claims' scope)."""
    nm = sum(len(s["methods"]) for s in T.services)
    return (f"{len(T.names)} types, {len(T.services)} receivers, {nm} methods "
            f"(receivers: {', '.join(s['receiver'] for s in T.services)})")
