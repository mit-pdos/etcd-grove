// Package pbcachetest characterises protobuf-go v1.36.12's size cache (the `sizeCache` field of a
// generated message), the behavior the proto model's cache methods must reproduce (etcd-grove #37,
// "S3 design: protobuf-go's size cache"). Each test names the protobuf-go lines it pins down; the
// paths are under google.golang.org/protobuf@v1.36.12. The messages are pbdifftest's `pb.Args` and
// `pb.Inner` (a singular `Inner` at field 10, a repeated `Inners` at 11, and `Inner.Sub` at 3, so
// nesting of any depth through both the singular and the repeated coder).
//
// The cache is read and written through its address (reflection, unsafe): the test is the only
// program that does so; protobuf-go itself goes through atomics.
package pbcachetest

import (
	"bytes"
	"errors"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"unsafe"

	"google.golang.org/protobuf/proto"

	"models.lab/internal/pbdifftest/pb"
)

var cached = proto.MarshalOptions{UseCachedSize: true}

// sc is the address of m's `sizeCache` (protoimpl.SizeCache = int32).
func sc(m proto.Message) *int32 {
	f := reflect.ValueOf(m).Elem().FieldByName("sizeCache")
	if !f.IsValid() || f.Kind() != reflect.Int32 {
		panic("no int32 sizeCache field")
	}
	return (*int32)(unsafe.Pointer(f.UnsafeAddr()))
}

func get(m proto.Message) int32    { return atomic.LoadInt32(sc(m)) }
func set(m proto.Message, v int32) { atomic.StoreInt32(sc(m), v) }

// tree builds root -> Inner(a) -> Sub(b) -> Sub(c), and root.Inners = [d, e], d.Sub = f.
type tree struct {
	root             *pb.Args
	a, b, c, d, e, f *pb.Inner
}

func newTree() tree {
	var t tree
	t.c = &pb.Inner{K: "grandchild", V: 3}
	t.b = &pb.Inner{K: "child", V: 2, Sub: t.c}
	t.a = &pb.Inner{K: "a", V: 1, Sub: t.b}
	t.f = &pb.Inner{K: "f", V: 6}
	t.d = &pb.Inner{K: "d", V: 4, Sub: t.f}
	t.e = &pb.Inner{K: "e", V: 5}
	t.root = &pb.Args{A: 7, Tag: "root", Inner: t.a, Inners: []*pb.Inner{t.d, t.e}}
	return t
}

func (t tree) all() []proto.Message {
	return []proto.Message{t.root, t.a, t.b, t.c, t.d, t.e, t.f}
}

// wire is m's encoding computed on a fresh deep copy (proto.Clone does not copy the size cache:
// every cache of the copy is 0), so it never depends on m's caches.
func wire(t *testing.T, m proto.Message) []byte {
	t.Helper()
	c := proto.Clone(m)
	if get(c) != 0 {
		t.Fatalf("Clone copied a size cache")
	}
	b, err := proto.Marshal(c)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// isMismatch: the error proto.MarshalOptions.marshal returns for a SizeMismatchError
// (proto/encode.go:199-203): `fmt.Errorf("marshaling %s: %v", ...)` with the message's full name
// and internal/errors/errors.go:95-96's text, formatted with %v, so it does not unwrap (a caller
// cannot errors.As it).
func isMismatch(err error) bool {
	return err != nil && strings.HasPrefix(err.Error(), "marshaling arith.Args: size mismatch") &&
		errors.Unwrap(err) == nil
}

// Size stores size+1 at every level it walks (internal/impl/encode.go:118-129, the store at 128;
// 123 stores 0 instead past math.MaxInt32-1, not exercised here), and so does the size pass of a
// default proto.Marshal (proto/encode.go:184-188, which runs Size without UseCachedSize).
func TestSizeStoresSizePlusOne(t *testing.T) {
	for _, viaMarshal := range []bool{false, true} {
		tr := newTree()
		for _, m := range tr.all() {
			if get(m) != 0 {
				t.Fatal("fresh message with a nonzero cache")
			}
		}
		if viaMarshal {
			if _, err := proto.Marshal(tr.root); err != nil {
				t.Fatal(err)
			}
		} else {
			proto.Size(tr.root)
		}
		for i, m := range tr.all() {
			if want := int32(len(wire(t, m)) + 1); get(m) != want {
				t.Errorf("viaMarshal=%v level %d: cache %d, want size+1 = %d", viaMarshal, i, get(m), want)
			}
		}
	}
}

// Under UseCachedSize a level whose cache is above 0 returns cache-1 without walking
// (internal/impl/encode.go:52-58); a cache at 0 or below is recomputed (60). The top level:
// MarshalOptions{UseCachedSize: true}.Size returns the stale value; a stale top-level cache alone
// changes only the buffer growth of Marshal (proto/encode.go:184-192: the size is used for
// `growcap` only; the top level is never checked against what is appended), so the bytes are right.
func TestCachedTopLevelStale(t *testing.T) {
	for _, stale := range []int32{1, 2, 5, 1000, 1 << 16} {
		tr := newTree()
		want := wire(t, tr.root)
		set(tr.root, stale)
		if got := cached.Size(tr.root); got != int(stale-1) {
			t.Errorf("stale %d: cached Size %d, want %d", stale, got, stale-1)
		}
		if get(tr.root) != stale {
			t.Errorf("cached Size wrote a positive top-level cache")
		}
		got, err := cached.Marshal(tr.root)
		if err != nil || !bytes.Equal(got, want) {
			t.Errorf("stale %d: cached Marshal = %x, %v; want %x", stale, got, err, want)
		}
		// MarshalAppend into a buffer whose capacity the stale size misjudges: still right.
		pre := []byte{0xAA, 0xBB}
		b := make([]byte, 2, 4)
		copy(b, pre)
		out, err := cached.MarshalAppend(b, tr.root)
		if err != nil || !bytes.Equal(out, append(append([]byte{}, pre...), want...)) {
			t.Errorf("stale %d: cached MarshalAppend = %x, %v", stale, out, err)
		}
	}
}

// Under UseCachedSize a level at 0 is recomputed (internal/impl/encode.go:60, 63-131) while its
// children are still read from their caches (the field sizers, internal/impl/codec_field.go:159-161,
// call sizePointer with the same options), and the result is stored into the level
// (encode.go:128): a stale child's cache derives a stale write into its parent.
func TestCachedZeroReadsChildren(t *testing.T) {
	tr := newTree()
	proto.Size(tr.root) // every level fresh
	set(tr.root, 0)
	set(tr.a, 0)
	bSize := int32(len(wire(t, tr.b)))
	set(tr.b, bSize+1+10) // b's cache claims 10 more bytes than b has
	fresh := len(wire(t, tr.root))
	got := cached.Size(tr.root)
	// b's length prefix stays one byte (b is short), so the stale-derived sizes are 10 more.
	if got != fresh+10 {
		t.Errorf("cached Size over a stale child = %d, want the stale-derived %d", got, fresh+10)
	}
	if get(tr.root) != int32(fresh+10+1) {
		t.Errorf("root cache %d, want stale-derived %d", get(tr.root), fresh+10+1)
	}
	if want := int32(len(wire(t, tr.a)) + 10 + 1); get(tr.a) != want {
		t.Errorf("a's cache %d, want stale-derived %d", get(tr.a), want)
	}
	if get(tr.b) != bSize+1+10 {
		t.Errorf("b's positive cache was rewritten: %d", get(tr.b))
	}
	// A default Size recomputes everything and repairs the caches (encode.go:52: no UseCachedSize).
	proto.Size(tr.root)
	for i, m := range tr.all() {
		if want := int32(len(wire(t, m)) + 1); get(m) != want {
			t.Errorf("level %d not repaired: %d, want %d", i, get(m), want)
		}
	}
}

// A stale cache on a nested level makes UseCachedSize marshalling fail with a SizeMismatchError: the
// singular message coder appends the cached size as the length prefix, then compares it with what
// it appended (internal/impl/codec_field.go:163-172, the check at 169-170), the repeated one likewise
// (codec_field.go:420-433, the check at 431-432). The error comes back as nil bytes (172/432 return
// nil, which every enclosing level passes up: encode.go:197-199), from MarshalAppend too, whatever
// buffer it was given (proto/encode.go:159-160 returns out.Buf). The levels the size pass walked
// keep the caches it wrote.
func TestCachedStaleNestedFails(t *testing.T) {
	cases := []struct {
		name  string
		stale func(tr tree) proto.Message // which level is made stale (after a fresh Size)
		how   string
	}{
		{"grandchild via singular", func(tr tree) proto.Message { return tr.c }, "mutate"},
		{"child via singular", func(tr tree) proto.Message { return tr.a }, "mutate"},
		{"repeated element", func(tr tree) proto.Message { return tr.e }, "mutate"},
		{"under a repeated element", func(tr tree) proto.Message { return tr.f }, "mutate"},
		{"grandchild garbage cache", func(tr tree) proto.Message { return tr.c }, "garbage"},
		{"grandchild cache smaller", func(tr tree) proto.Message { return tr.c }, "smaller"},
	}
	for _, c := range cases {
		for _, parentsZero := range []bool{false, true} {
			tr := newTree()
			proto.Size(tr.root)
			m := c.stale(tr)
			switch c.how {
			case "mutate": // the message changes after Size: its cache is now stale
				in := m.(*pb.Inner)
				in.K += "-longer"
			case "garbage":
				set(m, get(m)+7)
			case "smaller":
				set(m, get(m)-1)
			}
			if parentsZero { // every level but the stale one at 0: recomputed, over the stale one
				for _, x := range tr.all() {
					if x != m {
						set(x, 0)
					}
				}
			}
			label := c.name
			if parentsZero {
				label += ", others at 0"
			}
			out, err := cached.Marshal(tr.root)
			if !isMismatch(err) || out != nil {
				t.Errorf("%s: cached Marshal = %x, %v; want nil and a size mismatch", label, out, err)
			}
			buf := []byte{1, 2, 3}
			out, err = cached.MarshalAppend(buf, tr.root)
			if !isMismatch(err) || out != nil {
				t.Errorf("%s: cached MarshalAppend = %x, %v; want nil and a size mismatch", label, out, err)
			}
			// Default Marshal recomputes every level first and succeeds (proto/encode.go:184-193).
			got, err := proto.Marshal(tr.root)
			if err != nil || !bytes.Equal(got, wire(t, tr.root)) {
				t.Errorf("%s: default Marshal = %x, %v", label, got, err)
			}
		}
	}
}

// Levels never sized (cache 0 everywhere) under UseCachedSize: each nested level is recomputed and
// stored just before its prefix is appended (codec_field.go:164, encode.go:60,128), so the prefixes
// agree and marshalling succeeds, leaving every level's cache fresh.
func TestCachedNeverSized(t *testing.T) {
	tr := newTree()
	got, err := cached.Marshal(tr.root)
	if err != nil || !bytes.Equal(got, wire(t, tr.root)) {
		t.Fatalf("cached Marshal of an unsized message = %x, %v", got, err)
	}
	for i, m := range tr.all() {
		if want := int32(len(wire(t, m)) + 1); get(m) != want {
			t.Errorf("level %d: cache %d, want %d", i, get(m), want)
		}
	}
}

// A sub-message referenced more than once (a DAG: x is root.Inner and both of root.Inners). The
// cache is per object, so every reference reads the same cell (encode.go:56).
func TestCachedDAG(t *testing.T) {
	mk := func() (*pb.Args, *pb.Inner) {
		x := &pb.Inner{K: "shared", V: 9, Sub: &pb.Inner{K: "leaf"}}
		return &pb.Args{Tag: "dag", Inner: x, Inners: []*pb.Inner{x, x}}, x
	}
	// x never sized, root at 0: the first reference computes and stores x's size, the later ones
	// read it, fresh: success.
	root, x := mk()
	got, err := cached.Marshal(root)
	if err != nil || !bytes.Equal(got, wire(t, root)) {
		t.Errorf("DAG, unsized: %x, %v", got, err)
	}
	// x fresh, root at 0: success.
	root, x = mk()
	proto.Size(root)
	set(root, 0)
	if got, err := cached.Marshal(root); err != nil || !bytes.Equal(got, wire(t, root)) {
		t.Errorf("DAG, fresh x: %x, %v", got, err)
	}
	// x stale (mutated after Size), root at 0: root's recomputation reads x's stale cache three
	// times, and the first prefix check fails.
	root, x = mk()
	proto.Size(root)
	set(root, 0)
	x.K = "shared, now longer"
	if out, err := cached.Marshal(root); !isMismatch(err) || out != nil {
		t.Errorf("DAG, stale x: %x, %v; want a size mismatch", out, err)
	}
	if want := int32(len(wire(t, root)) + 1); get(root) == want || get(root) == 0 {
		t.Errorf("DAG: root's cache %d is not the stale-derived write (fresh would be %d)", get(root), want)
	}
	// Default Marshal of the same: success, and every cache fresh.
	if got, err := proto.Marshal(root); err != nil || !bytes.Equal(got, wire(t, root)) {
		t.Errorf("DAG, default Marshal over stale x: %x, %v", got, err)
	}
	if want := int32(len(wire(t, x)) + 1); get(x) != want {
		t.Errorf("DAG: x's cache %d after default Marshal, want %d", get(x), want)
	}
}

// Default proto.Marshal ignores whatever the caches hold, sequentially: its size pass runs without
// UseCachedSize (proto/encode.go:184-188 with o.flags() of the zero options, so encode.go:52 is
// false at every level) and stores every level's size, and only then marshals with
// MarshalUseCachedSize (proto/encode.go:193) reading those fresh values.
func TestDefaultMarshalIgnoresStaleCaches(t *testing.T) {
	vals := []int32{0, 1, 2, -1, -1000, 1 << 30, 0x7fffffff, -0x80000000}
	for i := 0; i < 64; i++ {
		tr := newTree()
		proto.Size(tr.root)
		tr.c.K += strings.Repeat("x", i)
		for j, m := range tr.all() {
			set(m, vals[(i+j)%len(vals)])
		}
		want := wire(t, tr.root)
		got, err := proto.Marshal(tr.root)
		if err != nil || !bytes.Equal(got, want) {
			t.Fatalf("round %d: default Marshal = %x, %v; want %x", i, got, err, want)
		}
		if got := proto.Size(tr.root); got != len(want) {
			t.Fatalf("round %d: default Size %d, want %d", i, got, len(want))
		}
	}
}

// Concurrent Size and Marshal of one shared, unmodified message: the cache is read and written only
// with atomics (encode.go:56, 123, 128), so this is race-free under -race, and since every
// writer stores the same fresh value, every result is the same. Run by etc/gates.sh with -race.
func TestConcurrentSizeMarshal(t *testing.T) {
	tr := newTree()
	want := wire(t, tr.root)
	var wg sync.WaitGroup
	errs := make(chan string, 64)
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for i := 0; i < 200; i++ {
				switch (g + i) % 4 {
				case 0:
					if n := proto.Size(tr.root); n != len(want) {
						errs <- "Size"
					}
				case 1:
					if b, err := proto.Marshal(tr.root); err != nil || !bytes.Equal(b, want) {
						errs <- "Marshal"
					}
				case 2:
					if b, err := cached.Marshal(tr.root); err != nil || !bytes.Equal(b, want) {
						errs <- "cached Marshal"
					}
				case 3:
					if n := cached.Size(tr.root); n != len(want) {
						errs <- "cached Size"
					}
				}
			}
		}(g)
	}
	wg.Wait()
	close(errs)
	for e := range errs {
		t.Errorf("concurrent %s differed", e)
	}
	for i, m := range tr.all() {
		if w := int32(len(wire(t, m)) + 1); get(m) != w {
			t.Errorf("level %d: cache %d, want %d", i, get(m), w)
		}
	}
}

// Default proto.Marshal CAN fail concurrently, on a message nobody writes during the race: b was
// sized, then changed (its cache stale), then put under a (never sized, cache 0) under root (0). A
// concurrent UseCachedSize Size of root recomputes a over b's stale cache and stores a stale-derived
// size in a (internal/impl/encode.go:60, 128) between default Marshal's size pass, which stored a's
// fresh size (proto/encode.go:184-188), and its marshal pass, which reads a's cache as a's length
// prefix and checks it (proto/encode.go:193, internal/impl/codec_field.go:163-172): a size mismatch.
// Rare (measured 2026-11-23: 2 of 200,000 races); the test asserts only that every outcome is the
// right bytes or a size mismatch, and logs how many mismatches it saw.
func TestConcurrentDefaultMarshalOverStaleChild(t *testing.T) {
	mismatches := 0
	for i := 0; i < 20000; i++ {
		b := &pb.Inner{K: "b"}
		proto.Size(b)
		b.K = "b, now longer than it was"
		a := &pb.Inner{K: "a", Sub: b}
		root := &pb.Args{Inner: a}
		want := wire(t, root)
		var wg sync.WaitGroup
		var out []byte
		var err error
		wg.Add(2)
		go func() { defer wg.Done(); out, err = proto.Marshal(root) }()
		go func() { defer wg.Done(); cached.Size(root) }()
		wg.Wait()
		switch {
		case isMismatch(err) && out == nil:
			mismatches++
		case err != nil || !bytes.Equal(out, want):
			t.Fatalf("iteration %d: %x, %v; want %x or a size mismatch", i, out, err, want)
		}
	}
	t.Logf("default Marshal failed with a size mismatch in %d of 20000 races", mismatches)
}
