package pbgenrand

import (
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

// ordersMain is added to the generated codec package of TestOrders: before the generated tests,
// it marshals an empty message of each type named in PBGEN_ORDER, in that order, which makes
// protobuf-go build those types' coders (and compute their needsInitCheck, cached for good) in
// that order; and TestFullRequired, messages with every required field set or one missing.
const ordersMain = `package codec

import (
	"os"
	"reflect"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"
)

func TestMain(m *testing.M) {
	if o := os.Getenv("PBGEN_ORDER"); o != "" {
		byName := map[string]pbType{}
		for _, tp := range pbTypes() {
			byName[tp.name] = tp
		}
		for _, n := range strings.Split(o, ",") {
			tp, ok := byName[n]
			if !ok {
				panic("PBGEN_ORDER: no type " + n)
			}
			proto.Marshal(tp.new())
		}
	}
	os.Exit(m.Run())
}

// TestFullRequired: each type with required fields, with every scalar field of its own set
// (a message with 70 required fields: past protobuf-go's 64-bit mask, its full check), then
// with each of them missing in turn: Marshal, and Unmarshal of the partial encoding.
func TestFullRequired(t *testing.T) {
	ok := 0
	for _, tp := range pbTypes() {
		if !tp.req {
			continue
		}
		var ptrs []int
		m := tp.new()
		v := reflect.ValueOf(m).Elem()
		for i := 0; i < v.NumField(); i++ {
			f := v.Field(i)
			if v.Type().Field(i).IsExported() && f.Kind() == reflect.Pointer && f.Type().Elem().Kind() != reflect.Struct {
				f.Set(reflect.New(f.Type().Elem()))
				ptrs = append(ptrs, i)
			}
		}
		pbCheckMarshal(t, m)
		if b, err := proto.Marshal(m); err == nil {
			ok++
			if !pbCheckUnmarshalFresh(t, tp, b) {
				t.Fatalf("%s: a complete encoding does not decode", tp.name)
			}
		}
		for _, i := range ptrs {
			c := proto.Clone(m)
			cv := reflect.ValueOf(c).Elem().Field(i)
			cv.Set(reflect.Zero(cv.Type()))
			pbCheckMarshal(t, c)
			b, err := proto.MarshalOptions{AllowPartial: true}.Marshal(c)
			if err != nil {
				t.Fatal(err)
			}
			pbCheckUnmarshalFresh(t, tp, b)
		}
	}
	if ok == 0 {
		t.Fatalf("no type with required fields marshaled complete")
	}
}
`

// TestOrders: the generated codec of a schema of required fields in cycles (a self-loop and a
// cycle of two types, each type with required fields of its own; a self-loop reaching required
// fields only outside it; a cycle with no required fields; a type outside a cycle reaching it), a
// oneof whose first member needs the check (and later members that do not), a message with 70
// required fields, and proto2 (unchecked) and proto3 (checked) strings, against protobuf-go in
// 13 orders of protobuf-go's lazy type setup, each in a fresh process (protobuf-go caches each
// type's needsInitCheck once). pbgen must accept the schema (none of its types is refused for
// a protobuf-go quirk) and the codec agree with protobuf-go in every order.
func TestOrders(t *testing.T) {
	s := newSetup(t)
	dir := t.TempDir()
	s.newModule(t, dir)
	msg := func(name string, fs ...*descriptorpb.FieldDescriptorProto) *descriptorpb.DescriptorProto {
		return &descriptorpb.DescriptorProto{Name: proto.String(name), Field: fs}
	}
	m := func(name string, num int32, typ string, label descriptorpb.FieldDescriptorProto_Label) *descriptorpb.FieldDescriptorProto {
		return withType(fld(name, num, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, label), typ)
	}
	str := descriptorpb.FieldDescriptorProto_TYPE_STRING
	inOneof := func(f *descriptorpb.FieldDescriptorProto) *descriptorpb.FieldDescriptorProto {
		f.OneofIndex = proto.Int32(0)
		return f
	}
	om := msg("O", inOneof(m("first", 1, ".po.S", opt)), inOneof(fld("k", 2, i32, opt)),
		inOneof(fld("str", 3, str, opt)), inOneof(m("e", 4, ".po.E1", opt)), fld("s", 5, str, opt))
	om.OneofDecl = []*descriptorpb.OneofDescriptorProto{{Name: proto.String("u")}}
	big := msg("Big")
	for i := int32(1); i <= 70; i++ {
		big.Field = append(big.Field, fld(fmt.Sprintf("f%d", i), i, i32, req))
	}
	o := refusedFile("po", "proto2",
		msg("S", fld("x", 1, i32, req), m("s", 2, ".po.S", opt), m("ss", 3, ".po.S", rep)),
		msg("P", fld("x", 1, i32, req), m("q", 2, ".po.Q", opt)),
		msg("Q", fld("y", 1, i32, req), m("p", 2, ".po.P", opt), m("ps", 3, ".po.P", rep)),
		msg("R", m("p", 1, ".po.P", opt), m("s", 2, ".po.S", opt)),
		msg("SL", m("sl", 1, ".po.SL", opt), m("c", 2, ".po.C", opt)),
		msg("C", fld("x", 1, i32, req)),
		msg("E1", m("e", 1, ".po.E2", opt)),
		msg("E2", m("e", 1, ".po.E1", opt), fld("z", 2, i32, opt)),
		om, big)
	o3 := refusedFile("po3", "proto3", msg("T3", fld("s", 1, str, opt), m("p", 2, ".po.P", opt),
		fld("ss", 3, str, rep), m("o", 4, ".po.O", opt), m("sl", 5, ".po.SL", opt)))
	o3.Dependency = []string{o.GetName()}
	s.protocGenGo(t, dir, []*descriptorpb.FileDescriptorProto{o, o3}, "")
	names := []string{"po.S", "po.P", "po.Q", "po.R", "po.SL", "po.C", "po.E1", "po.E2", "po.O", "po.Big", "po3.T3"}
	toml := "[protobuf]\nimports = { po = \"pbgenrand.tmp/po\", po3 = \"pbgenrand.tmp/po3\" }\nroots = [\"" +
		strings.Join(names, "\", \"") + "\"]\n"
	tomlPath := filepath.Join(dir, "protobuf.toml")
	must(t, os.WriteFile(tomlPath, []byte(toml), 0o644))
	run(t, dir, nil, "python3", s.pbgen, tomlPath, filepath.Join(dir, "codec"), "--pkg", "codec")
	must(t, os.WriteFile(filepath.Join(dir, "codec", "orders_main_test.go"), []byte(ordersMain), 0o644))
	bin := filepath.Join(dir, "codec.test")
	run(t, dir, nil, "go", "test", "-c", "-o", bin, "./codec")

	orders := [][]string{names, nil}
	for i := len(names) - 1; i >= 0; i-- {
		orders[1] = append(orders[1], names[i])
	}
	r := rand.New(rand.NewSource(7))
	for len(orders) < 13 {
		p := append([]string{}, names...)
		r.Shuffle(len(p), func(i, j int) { p[i], p[j] = p[j], p[i] })
		orders = append(orders, p)
	}
	// (the depth tests, which do not depend on the order, are run once, by the first order)
	for k, ord := range orders {
		if k == 0 {
			out, code := runCode(filepath.Join(dir, "codec"), goEnv("PBGEN_ORDER="+strings.Join(ord, ","),
				"PBGEN_TEST_SCALE=0.1"), bin, "-test.count=1")
			if code != 0 {
				t.Fatalf("order %v: the codec differs from protobuf-go:\n%s", ord, tail(out, 40))
			}
			continue
		}
		out, code := runCode(filepath.Join(dir, "codec"), goEnv("PBGEN_ORDER="+strings.Join(ord, ","),
			"PBGEN_TEST_SCALE=0.1"), bin, "-test.count=1",
			"-test.run=^Test(ProtoShapes|ProtoMarshal|ProtoUnmarshal|ProtoMutations|ProtoFields|FullRequired)$")
		if code != 0 {
			t.Fatalf("order %v: the codec differs from protobuf-go:\n%s", ord, tail(out, 40))
		}
	}
	t.Logf("%d orders of protobuf-go's type setup, the codec agrees in each", len(orders))
}
