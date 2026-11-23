// Package pbmodeltest is the protobuf model's differential test (models/protobuf-go;
// models/README.md, "The protobuf model"): the same tests built against the real
// google.golang.org/protobuf v1.36.12 and against the model (run.sh), each writing a transcript of
// everything it observed of the proto package's entry points (bytes and their nil-ness, sizes,
// error classes, panics, decoded messages with nil-ness and unknown fields, clones, every level's
// size cache after every call); the two transcripts must be equal byte for byte. The messages are
// pbdifftest's (models.lab/internal/pbdifftest/{pb,xpb}: every field kind of pbgen's proto3 subset;
// oneofs and the proto2 constructs are covered method by method by models/internal/pbgenrand), with the
// methods pbgen's pbmodel mode wrote beside them (tag pbmodel, set in both builds: only the model
// calls them). So this tests the model's composition of the methods (proto/model.go: the size
// pass, the buffer, the append, the required check, Marshal's empty result, Clone's and
// MessageV2Of's typed results, the nil cases), where pbgenrand tests the methods themselves.
package pbmodeltest

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"sync/atomic"
	"testing"
	"unsafe"

	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/protoadapt"

	"models.lab/internal/pbdifftest/pb"
	"models.lab/internal/pbdifftest/xpb"
)

// transcript: what a test observed, line by line; saved to $PBMODEL_OUT/<name>.txt (run.sh
// compares the two builds' directories).
type transcript struct {
	name string
	buf  bytes.Buffer
	n    int
}

func (t *transcript) printf(format string, args ...interface{}) {
	fmt.Fprintf(&t.buf, format, args...)
	t.buf.WriteByte('\n')
	t.n++
}

func (t *transcript) save(tb testing.TB) {
	tb.Logf("%s: %d transcript lines (model build %v)", t.name, t.n, modelBuild)
	if dir := os.Getenv("PBMODEL_OUT"); dir != "" {
		if err := os.WriteFile(filepath.Join(dir, t.name+".txt"), t.buf.Bytes(), 0o644); err != nil {
			tb.Fatal(err)
		}
	}
}

// outcome runs f: "ok", "panic: NotModelled" (the model's panic value), or "panic" (any other;
// its value is not compared: protobuf-go's are runtime errors, the model's the same or its own).
func outcome(f func()) (s string) {
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(interface{ NotModelled() }); ok {
				s = "panic: NotModelled"
			} else {
				s = "panic"
			}
		}
	}()
	f()
	return "ok"
}

func class(err error) string {
	switch {
	case err == nil:
		return "nil"
	case strings.Contains(err.Error(), "invalid UTF-8"):
		return "utf8"
	case strings.Contains(err.Error(), "required field"):
		return "required"
	case strings.Contains(err.Error(), "size mismatch"):
		return "mismatch"
	}
	return "error"
}

// uclass: an Unmarshal error's class, as the model claims it: required-or-not (the methods'
// decoder does not tell invalid UTF-8 from malformed input or the recursion limit).
func uclass(err error) string {
	if c := class(err); c != "required" && c != "nil" {
		return "error"
	}
	return class(err)
}

func bs(b []byte) string {
	if b == nil {
		return "nil"
	}
	return "[" + hex.EncodeToString(b) + "]"
}

func sc(m proto.Message) *int32 {
	f := reflect.ValueOf(m).Elem().FieldByName("sizeCache")
	return (*int32)(unsafe.Pointer(f.UnsafeAddr()))
}

// dump: m's exported fields with nil-ness, unknown fields and size caches, at every level, in a
// fixed order (a shared sub-message printed once, then by its index).
func dump(m interface{}) string {
	var sb strings.Builder
	seen := map[uintptr]int{}
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Pointer:
			if v.IsNil() {
				sb.WriteString("nil")
				return
			}
			if pm, ok := v.Interface().(proto.Message); ok && v.Elem().Kind() == reflect.Struct {
				if k, ok := seen[v.Pointer()]; ok {
					fmt.Fprintf(&sb, "@%d", k)
					return
				}
				seen[v.Pointer()] = len(seen)
				fmt.Fprintf(&sb, "%s#%d{sc=%d uf=%s ", v.Elem().Type().Name(), seen[v.Pointer()],
					atomic.LoadInt32(sc(pm)), bs(pm.ProtoReflect().GetUnknown()))
				walk(v.Elem())
				sb.WriteString("}")
				return
			}
			sb.WriteString("&")
			walk(v.Elem())
		case reflect.Interface:
			if v.IsNil() {
				sb.WriteString("nil")
				return
			}
			fmt.Fprintf(&sb, "%s:", v.Elem().Type())
			walk(v.Elem())
		case reflect.Struct:
			sb.WriteString("{")
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					fmt.Fprintf(&sb, "%s=", v.Type().Field(i).Name)
					walk(v.Field(i))
					sb.WriteString(" ")
				}
			}
			sb.WriteString("}")
		case reflect.Slice:
			if v.IsNil() {
				sb.WriteString("nil")
				return
			}
			if v.Type().Elem().Kind() == reflect.Uint8 {
				sb.WriteString(bs(v.Bytes()))
				return
			}
			sb.WriteString("[")
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
				sb.WriteString(",")
			}
			sb.WriteString("]")
		default:
			fmt.Fprintf(&sb, "%v", v.Interface())
		}
	}
	walk(reflect.ValueOf(m))
	return sb.String()
}

var pieces = []string{"a", "xyz", "é", "日本", "\x00", "\xff", "\xed\xa0\x80"}

func rndString(r *rand.Rand) string {
	var sb strings.Builder
	for k := r.Intn(4); k > 0; k-- {
		p := pieces[r.Intn(len(pieces))]
		if (p == "\xff" || p == "\xed\xa0\x80") && r.Intn(4) != 0 {
			p = "b"
		}
		sb.WriteString(p)
	}
	return sb.String()
}

// fill: random exported fields (some left zero), sub-messages to depth 4.
func fill(r *rand.Rand, v reflect.Value, depth int) {
	for i := 0; i < v.NumField(); i++ {
		if v.Type().Field(i).IsExported() && r.Intn(3) != 0 {
			value(r, v.Field(i), depth)
		}
	}
}

func value(r *rand.Rand, f reflect.Value, depth int) {
	switch f.Kind() {
	case reflect.Int32, reflect.Int64:
		f.SetInt([]int64{0, 1, -1, 300, 1 << 40, -1 << 62}[r.Intn(6)])
	case reflect.Uint32, reflect.Uint64:
		f.SetUint([]uint64{0, 1, 300, 1 << 31, 1<<64 - 1}[r.Intn(5)])
	case reflect.Bool:
		f.SetBool(r.Intn(2) == 0)
	case reflect.String:
		f.SetString(rndString(r))
	case reflect.Pointer:
		if f.Type().Elem().Kind() != reflect.Struct {
			p := reflect.New(f.Type().Elem())
			value(r, p.Elem(), depth)
			f.Set(p)
			return
		}
		if depth >= 4 {
			return
		}
		p := reflect.New(f.Type().Elem())
		if r.Intn(4) != 0 {
			fill(r, p.Elem(), depth+1)
		}
		f.Set(p)
	case reflect.Slice:
		if f.Type().Elem().Kind() == reflect.Uint8 {
			switch r.Intn(3) {
			case 0:
				return
			case 1:
				f.SetBytes([]byte{})
			default:
				f.SetBytes([]byte{byte(r.Intn(256)), 0x80})
			}
			return
		}
		n := r.Intn(4)
		s := reflect.MakeSlice(f.Type(), n, n)
		for i := 0; i < n; i++ {
			if s.Index(i).Kind() == reflect.Pointer && r.Intn(6) == 0 {
				continue
			}
			value(r, s.Index(i), depth+1)
		}
		f.Set(s)
	}
}

func newOf(r *rand.Rand) proto.Message {
	ms := []func() proto.Message{
		func() proto.Message { return &pb.Args{} }, func() proto.Message { return &pb.Reply{} },
		func() proto.Message { return &pb.Inner{} }, func() proto.Message { return &xpb.Kinds{} },
		func() proto.Message { return &pb.Empty{} },
	}
	return ms[r.Intn(len(ms))]()
}

// mutate: an encoding with a field inserted (an unknown or known number, any wire type), cut
// short, or a byte changed.
func mutate(r *rand.Rand, b []byte) []byte {
	b = append([]byte{}, b...)
	switch r.Intn(4) {
	case 0:
		return b[:r.Intn(len(b)+1)]
	case 1:
		if len(b) > 0 {
			b[r.Intn(len(b))] = byte(r.Intn(256))
		}
		return b
	}
	num := protowire.Number([]int{1, 2, 5, 10, 11, 50, 99, 1000}[r.Intn(8)])
	var f []byte
	switch r.Intn(4) {
	case 0:
		f = protowire.AppendVarint(protowire.AppendTag(nil, num, protowire.VarintType), uint64(r.Intn(1000)))
	case 1:
		f = protowire.AppendFixed32(protowire.AppendTag(nil, num, protowire.Fixed32Type), r.Uint32())
	case 2:
		f = protowire.AppendBytes(protowire.AppendTag(nil, num, protowire.BytesType), []byte{0x08, 0x01})
	default:
		f = append(protowire.AppendTag(nil, num, protowire.StartGroupType),
			protowire.AppendTag(protowire.AppendVarint(protowire.AppendTag(nil, 1, protowire.VarintType), 7), num, protowire.EndGroupType)...)
	}
	at := 0
	if len(b) > 0 {
		at = r.Intn(len(b) + 1)
	}
	return append(append(append([]byte{}, b[:at]...), f...), b[at:]...)
}

// TestEntryPoints: every modelled entry point on random messages (fresh, with garbage caches, with
// a changed sub-message: stale caches), decoded ones (unknown fields included), and the nil cases.
func TestEntryPoints(t *testing.T) {
	tr := &transcript{name: "entrypoints"}
	r := rand.New(rand.NewSource(1))
	cached := proto.MarshalOptions{UseCachedSize: true}
	for it := 0; it < 1500; it++ {
		m := newOf(r)
		if r.Intn(2) == 0 {
			fill(r, reflect.ValueOf(m).Elem(), 0)
		} else {
			src := newOf(r)
			fill(r, reflect.ValueOf(src).Elem(), 0)
			data, _ := proto.MarshalOptions{AllowPartial: true}.Marshal(src)
			data = mutate(r, data)
			err := proto.Unmarshal(data, m)
			tr.printf("Unmarshal(%s) into %T: %s %s", bs(data), m, uclass(err), dump(m))
		}
		if r.Intn(3) == 0 {
			atomic.StoreInt32(sc(m), int32(r.Intn(40)-5))
		}
		for k := 0; k < 6; k++ {
			var line string
			switch op := r.Intn(10); op {
			case 0:
				line = fmt.Sprintf("Size %d", proto.Size(m))
			case 1:
				line = fmt.Sprintf("cached Size %d", cached.Size(m))
			case 2:
				b, err := proto.Marshal(m)
				line = fmt.Sprintf("Marshal %s %s", bs(b), class(err))
			case 3:
				b, err := cached.Marshal(m)
				line = fmt.Sprintf("cached Marshal %s %s", bs(b), class(err))
			case 4:
				pre := []byte{1, 2, 3}[:r.Intn(4)]
				if r.Intn(3) == 0 {
					pre = nil
				}
				b, err := cached.MarshalAppend(pre, m)
				line = fmt.Sprintf("cached MarshalAppend(%s) %s %s", bs(pre), bs(b), class(err))
			case 5:
				b, err := proto.MarshalOptions{Deterministic: true, AllowPartial: r.Intn(2) == 0}.MarshalAppend(nil, m)
				line = fmt.Sprintf("Deterministic MarshalAppend %s %s", bs(b), class(err))
			case 6:
				c := proto.Clone(m)
				line = fmt.Sprintf("Clone %T %s", c, dump(c))
			case 7:
				c := proto.CloneOf(m)
				v2 := protoadapt.MessageV2Of(m.(protoadapt.MessageV1))
				line = fmt.Sprintf("CloneOf %T %s; MessageV2Of identical %v", c, dump(c), v2 == m)
			case 8: // a sub-message changed: stale caches below
				v := reflect.ValueOf(m).Elem()
				for i := 0; i < v.NumField(); i++ {
					if f := v.Field(i); v.Type().Field(i).IsExported() && f.Kind() == reflect.Pointer &&
						!f.IsNil() && f.Elem().Kind() == reflect.Struct {
						fill(r, f.Elem(), 2)
						break
					}
				}
				line = "changed"
			case 9:
				var x proto.Message
				if r.Intn(2) == 0 {
					x = newOf(r)
				} else {
					x = m
				}
				data, _ := proto.MarshalOptions{AllowPartial: true}.Marshal(newOf(r))
				err := proto.UnmarshalOptions{}.Unmarshal(mutate(r, data), x)
				line = fmt.Sprintf("UnmarshalOptions{}.Unmarshal %s %s", uclass(err), dump(x))
			}
			tr.printf("%s | %s", line, dump(m))
		}
	}
	// the nil cases
	var nilIface proto.Message
	typedNil := (*pb.Args)(nil)
	tr.printf("Marshal(nil) %s", outcome(func() { b, err := proto.Marshal(nilIface); tr.printf("  %s %s", bs(b), class(err)) }))
	tr.printf("MarshalAppend(b, nil) %s", outcome(func() {
		b, err := cached.MarshalAppend([]byte{9}, nilIface)
		tr.printf("  %s %s", bs(b), class(err))
	}))
	tr.printf("Size(nil) %s", outcome(func() { tr.printf("  %d", proto.Size(nilIface)) }))
	tr.printf("Clone(nil) %s", outcome(func() { tr.printf("  %v", proto.Clone(nilIface) == nil) }))
	tr.printf("MessageV2Of(nil) %s", outcome(func() { tr.printf("  %v", protoadapt.MessageV2Of(nil) == nil) }))
	tr.printf("Marshal(typed nil) %s", outcome(func() { b, err := proto.Marshal(typedNil); tr.printf("  %s %s", bs(b), class(err)) }))
	tr.printf("Size(typed nil) %s", outcome(func() { tr.printf("  %d", proto.Size(typedNil)) }))
	tr.printf("Clone(typed nil) %s", outcome(func() {
		c := proto.Clone(typedNil)
		tr.printf("  %T %v", c, c.(*pb.Args) == nil)
	}))
	tr.printf("Unmarshal into typed nil %s", outcome(func() { _ = proto.Unmarshal([]byte{8, 1}, typedNil) }))
	tr.printf("Marshal(empty) %s", outcome(func() { b, err := proto.Marshal(&pb.Empty{}); tr.printf("  %s %s", bs(b), class(err)) }))
	tr.save(t)
}

// Embedded messages: a struct embedding a message pointer (as etcd's client and raft's node do)
// is marshalled, sized and cloned as the embedded message.
type embedding struct {
	*pb.Inner
}

func TestEmbedded(t *testing.T) {
	tr := &transcript{name: "embedded"}
	e := embedding{&pb.Inner{K: "k", V: 3, Sub: &pb.Inner{K: "sub"}}}
	b, err := proto.Marshal(e)
	tr.printf("Marshal %s %s", bs(b), class(err))
	tr.printf("Size %d", proto.Size(e))
	c := proto.Clone(e)
	tr.printf("Clone %T %s", c, dump(c))
	err = proto.Unmarshal([]byte{0x0a, 0x01, 'x', 0x10, 0x05, 0xf8, 0x01, 0x01}, e)
	tr.printf("Unmarshal %s %s", uclass(err), dump(e.Inner))
	tr.save(t)
}
