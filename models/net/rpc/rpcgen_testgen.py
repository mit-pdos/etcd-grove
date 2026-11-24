"""rpcgen's regression test, generated beside each codec (untrusted: evidence for the claim).

`rpc_gen_test.go` runs in a real build (tags neither netmodel nor goose) and checks, for every
root type of the codec, on random values: that decoding `rpcEncode(v)` (and `rpcEncode(&v)`)
into a zero value gives what real gob gives, and into a random non-zero value (gob merges into
it) the same as real gob; and that the receivers' facts the codec was generated from are still
reflection's (the method names suitableMethods registers).
"""

from rpcgen_core import SIGNED, UNSIGNED, fn


def rand_body(S, i):
    e, g = S.t[i], S.go(i)
    k = e["kind"]
    if k == "bool":
        return f"\treturn {g}(r.Intn(2) == 0)\n"
    if k in SIGNED or k in UNSIGNED:
        return (f"\tswitch r.Intn(5) {{\n\tcase 0:\n\t\treturn 0\n\tcase 1:\n\t\treturn {g}(r.Intn(3))\n"
                f"\tcase 2:\n\t\tvar z {g}\n\t\treturn ^z\n\t}}\n\treturn {g}(r.Uint64())\n")
    if k == "string":
        return (f"\tswitch r.Intn(3) {{\n\tcase 0:\n\t\treturn \"\"\n\tcase 1:\n"
                f"\t\treturn {g}(fmt.Sprint(\"s\", r.Intn(100)))\n\t}}\n"
                f"\tb := make([]byte, r.Intn(6))\n\tr.Read(b)\n\treturn {g}(b)\n")
    if k == "slice":
        return (f"\tif d > 3 {{\n\t\treturn nil\n\t}}\n\tswitch r.Intn(4) {{\n\tcase 0:\n\t\treturn nil\n"
                f"\tcase 1:\n\t\treturn {g}{{}}\n\t}}\n\tv := make({g}, 0, r.Intn(3))\n"
                f"\tfor i := r.Intn(4); i >= 0; i-- {{\n\t\tv = append(v, rpcRand_{fn(e['elem'])}(r, d+1))\n"
                f"\t}}\n\treturn v\n")
    if k == "map":
        return (f"\tif d > 3 {{\n\t\treturn nil\n\t}}\n\tswitch r.Intn(4) {{\n\tcase 0:\n\t\treturn nil\n"
                f"\tcase 1:\n\t\treturn {g}{{}}\n\t}}\n\tv := {g}{{}}\n"
                f"\tfor i := r.Intn(4); i >= 0; i-- {{\n"
                f"\t\tv[rpcRand_{fn(e['key'])}(r, d+1)] = rpcRand_{fn(e['elem'])}(r, d+1)\n"
                f"\t}}\n\treturn v\n")
    if k == "struct":
        o = [f"\tvar v {g}\n"]
        for f in e["fields"]:
            if not f["exported"]:
                continue
            ft = S.t[f["type"]]
            if ft["kind"] == "ptr":
                el = ft["elem"]
                o.append(f"\tif r.Intn(3) != 0 {{\n\t\tx := rpcRand_{fn(el)}(r, d+1)\n"
                         f"\t\tv.{f['name']} = &x\n\t}}\n")
            else:
                o.append(f"\tv.{f['name']} = rpcRand_{fn(f['type'])}(r, d+1)\n")
        o.append("\treturn v\n")
        return "".join(o)
    raise AssertionError(e)


def gen_test_go(S, header, pkg):
    imps = S.imports()
    o = [header, f"""//go:build !netmodel && !goose

package {pkg}

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"math/rand"
	"os"
	"reflect"
	"strconv"
	"testing"
"""]
    if imps:
        o.append("\n")
    o.extend(f"\t{a} \"{p}\"\n" for a, p in imps)
    o.append(""")

// The net/rpc model's codec of this program's types against real gob (rpcgen_testgen.py).

var _ = fmt.Sprint

func rpcGob(v any, into any) error {
	var b bytes.Buffer
	if err := gob.NewEncoder(&b).Encode(v); err != nil {
		return err
	}
	return gob.NewDecoder(&b).Decode(into)
}

// rpcSamples: RPCGEN_TEST_SCALE (default 1) times 300 values per type.
func rpcSamples() int {
	n := 300
	if s, err := strconv.Atoi(os.Getenv("RPCGEN_TEST_SCALE")); err == nil && s > 0 {
		n *= s
	}
	return n
}
""")
    for i in S.closure:
        g = S.go(i)
        o.append(f"\nfunc rpcRand_{fn(i)}(r *rand.Rand, d int) {g} {{\n\t_ = d\n{rand_body(S, i)}}}\n")
    o.append("""
func TestRPCCodecAgainstGob(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for i := 0; i < rpcSamples(); i++ {
		seed := r.Int63()
""")
    for i in S.roots:
        g = S.go(i)
        o.append(f"""		{{
			v := rpcRand_{fn(i)}(r, 0)
			if i == 0 {{
				var z {g}
				v = z
			}}
			real, model, model2 := new({g}), new({g}), new({g})
			if err := rpcGob(v, real); err != nil {{
				t.Fatalf("{g}: gob: %v", err)
			}}
			if err := rpcDecode(rpcEncode(v), model); err != nil || !reflect.DeepEqual(real, model) {{
				t.Fatalf("{g} %#v: gob gives %#v, the model %#v (%v)", v, *real, *model, err)
			}}
			if err := rpcDecode(rpcEncode(&v), model2); err != nil || !reflect.DeepEqual(real, model2) {{
				t.Fatalf("*{g} %#v: gob gives %#v, the model %#v (%v)", v, *real, *model2, err)
			}}
			// into a non-zero value: the same random value twice
			r1, r2 := rand.New(rand.NewSource(seed)), rand.New(rand.NewSource(seed))
			real3, model3 := new({g}), new({g})
			*real3, *model3 = rpcRand_{fn(i)}(r1, 0), rpcRand_{fn(i)}(r2, 0)
			before := fmt.Sprintf("%#v", *real3)
			if err := rpcGob(v, real3); err != nil {{
				t.Fatalf("{g} into a non-zero value: gob: %v", err)
			}}
			if err := rpcDecode(rpcEncode(v), model3); err != nil || !reflect.DeepEqual(real3, model3) {{
				t.Fatalf("{g} %#v into %s: gob gives %#v, the model %#v (%v)", v, before, *real3, *model3, err)
			}}
		}}
""")
    o.append("\t}\n}\n")
    # the receivers' facts
    o.append("""
// rpcSuitable: the names of the methods net/rpc's suitableMethods registers (models/rpcdesc's
// copy of it is what the codec was generated from; this checks the generated table is current).
func rpcSuitable(typ reflect.Type) []string {
	var ms []string
	errT := reflect.TypeFor[error]()
	exported := func(t reflect.Type) bool {
		for t.Kind() == reflect.Pointer {
			t = t.Elem()
		}
		return t.PkgPath() == "" || (t.Name() != "" && t.Name()[0] >= 'A' && t.Name()[0] <= 'Z')
	}
	for i := 0; i < typ.NumMethod(); i++ {
		m := typ.Method(i)
		mt := m.Type
		if !m.IsExported() || mt.NumIn() != 3 || mt.NumOut() != 1 || mt.Out(0) != errT {
			continue
		}
		if !exported(mt.In(1)) || mt.In(2).Kind() != reflect.Pointer || !exported(mt.In(2)) {
			continue
		}
		ms = append(ms, m.Name)
	}
	return ms
}

func TestRPCReceivers(t *testing.T) {
""")
    for r, ms in S.receivers:
        rg = S.go(r["type"])
        want = ", ".join(f'"{m}"' for m, _, _, _ in sorted(ms))
        o.append(f"\tif got, want := fmt.Sprint(rpcSuitable(reflect.TypeFor[{rg}]())), "
                 f"fmt.Sprint([]string{{{want}}}); got != want {{\n"
                 f"\t\tt.Errorf(\"{rg}: generated for %s, net/rpc registers %s (regenerate)\", want, got)\n\t}}\n")
    o.append("}\n")
    return "".join(o)
