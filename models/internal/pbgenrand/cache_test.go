//go:build pbmodel

// The size cache on the same-package methods (pbgen's pbmodel mode), fixed cases: each case is run
// on two graphs built alike, one by real protobuf-go v1.36.12 and one by the methods (composed as
// the proto model composes them: models/protobuf-go/proto/model.go), step by step, and after every
// step the results (bytes and their nil-ness, sizes, error classes) and every level's size cache
// must be equal. The cases are those of internal/pbcachetest (which characterises protobuf-go
// alone) and the ones #37's reviews asked for: a sub-message reachable from two parents, one parent
// marshalled (re-sizing it) and the other then marshalled with UseCachedSize. The random
// interleavings are in each generated test (pbmodel_gen_test.go's TestPbModelCache); this file
// keeps the named regressions. Run by etc/gates.sh with -tags pbmodel, under -race.
package pbgenrand

import (
	"bytes"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"unsafe"

	"google.golang.org/protobuf/proto"

	"models.lab/internal/pbdifftest/pb"
)

// pbModel: the methods pbgen's pbmodel mode emits.
type pbModel interface {
	PbModelSize(cached bool) int
	PbModelAppend(b []byte, cached bool) ([]byte, error)
	PbModelIsInit() bool
	PbModelIsNil() bool
}

func sc(m proto.Message) *int32 {
	f := reflect.ValueOf(m).Elem().FieldByName("sizeCache")
	return (*int32)(unsafe.Pointer(f.UnsafeAddr()))
}

func growcap(oldcap, wantcap int) int {
	if wantcap > oldcap*2 {
		return wantcap
	}
	if oldcap < 1024 {
		return oldcap * 2
	}
	n := oldcap
	for 0 < n && n < wantcap {
		n += n / 4
	}
	if n <= 0 {
		return wantcap
	}
	return n
}

// modelMarshal: the proto model's MarshalOptions{UseCachedSize: cached}.Marshal (b nil, appending
// false) or .MarshalAppend(b, m).
func modelMarshal(b []byte, m pbModel, cached, appending bool) ([]byte, error) {
	n := m.PbModelSize(cached)
	if cap(b) < len(b)+n {
		g := make([]byte, len(b), growcap(cap(b), len(b)+n))
		copy(g, b)
		b = g
	}
	out, err := m.PbModelAppend(b, true)
	if err == nil && !m.PbModelIsInit() {
		err = errRequired
	}
	if !appending && len(out) == 0 && err == nil {
		if m.PbModelIsNil() {
			return nil, nil
		}
		return []byte{}, nil
	}
	return out, err
}

type errText string

func (e errText) Error() string { return string(e) }

const errRequired = errText("required field not set")

func class(err error) string {
	switch {
	case err == nil:
		return "nil"
	case strings.Contains(err.Error(), "size mismatch"):
		return "mismatch"
	case strings.Contains(err.Error(), "invalid UTF-8"):
		return "utf8"
	}
	return "other: " + err.Error()
}

// graph: root -> Inner(a) -> Sub(b) -> Sub(c); root.Inners = [d, e]; d.Sub = f (as pbcachetest's
// tree); nodes in that order.
type graph struct {
	nodes []proto.Message
}

func newGraph() graph {
	c := &pb.Inner{K: "grandchild", V: 3}
	b := &pb.Inner{K: "child", V: 2, Sub: c}
	a := &pb.Inner{K: "a", V: 1, Sub: b}
	f := &pb.Inner{K: "f", V: 6}
	d := &pb.Inner{K: "d", V: 4, Sub: f}
	e := &pb.Inner{K: "e", V: 5}
	root := &pb.Args{A: 7, Tag: "root", Inner: a, Inners: []*pb.Inner{d, e}}
	return graph{[]proto.Message{root, a, b, c, d, e, f}}
}

// step: an operation (on node i) or a change (to node i: mut), run alike on both graphs.
type step struct {
	op  string // "size", "csize", "marshal", "cmarshal", "cappend", "set", "mut"
	i   int
	val int32 // for "set"
	mut func(m proto.Message)
}

type result struct {
	b     []byte
	isNil bool
	n     int
	err   string
}

func runReal(s step, m proto.Message) result {
	var r result
	var err error
	switch s.op {
	case "size":
		r.n = proto.Size(m)
	case "csize":
		r.n = proto.MarshalOptions{UseCachedSize: true}.Size(m)
	case "marshal":
		r.b, err = proto.Marshal(m)
	case "cmarshal":
		r.b, err = proto.MarshalOptions{UseCachedSize: true}.Marshal(m)
	case "cappend":
		r.b, err = proto.MarshalOptions{UseCachedSize: true}.MarshalAppend([]byte{1, 2}, m)
	}
	r.isNil, r.err = r.b == nil, class(err)
	return r
}

func runModel(s step, m proto.Message) result {
	x := m.(pbModel)
	var r result
	var err error
	switch s.op {
	case "size":
		r.n = x.PbModelSize(false)
	case "csize":
		r.n = x.PbModelSize(true)
	case "marshal":
		r.b, err = modelMarshal(nil, x, false, false)
	case "cmarshal":
		r.b, err = modelMarshal(nil, x, true, false)
	case "cappend":
		r.b, err = modelMarshal([]byte{1, 2}, x, true, true)
	}
	r.isNil, r.err = r.b == nil, class(err)
	return r
}

// twin runs the steps on two graphs made by mk, real protobuf-go on one, the methods on the other,
// comparing after every step; it returns the real results, for the case's own expectations.
func twin(t *testing.T, name string, mk func() graph, steps []step) []result {
	t.Helper()
	gr, gm := mk(), mk()
	var out []result
	for k, s := range steps {
		var rr, rm result
		switch s.op {
		case "set":
			atomic.StoreInt32(sc(gr.nodes[s.i]), s.val)
			atomic.StoreInt32(sc(gm.nodes[s.i]), s.val)
		case "mut":
			s.mut(gr.nodes[s.i])
			s.mut(gm.nodes[s.i])
		default:
			rr, rm = runReal(s, gr.nodes[s.i]), runModel(s, gm.nodes[s.i])
		}
		if !bytes.Equal(rr.b, rm.b) || rr.isNil != rm.isNil || rr.n != rm.n || rr.err != rm.err {
			t.Fatalf("%s, step %d (%s %d): real %x nil %v n %d %s; methods %x nil %v n %d %s", name, k, s.op, s.i,
				rr.b, rr.isNil, rr.n, rr.err, rm.b, rm.isNil, rm.n, rm.err)
		}
		for i := range gr.nodes {
			if a, b := atomic.LoadInt32(sc(gr.nodes[i])), atomic.LoadInt32(sc(gm.nodes[i])); a != b {
				t.Fatalf("%s, step %d (%s %d): node %d's cache: real %d, methods %d", name, k, s.op, s.i, i, a, b)
			}
		}
		out = append(out, rr)
	}
	return out
}

func longer(m proto.Message) { m.(*pb.Inner).K += "-longer" }

// TestCacheCases: the characterised behaviors (internal/pbcachetest), on the methods.
func TestCacheCases(t *testing.T) {
	// Size stores size+1 at every level (internal/impl/encode.go:118-130), default Marshal too.
	twin(t, "size stores", newGraph, []step{{op: "size"}})
	twin(t, "marshal stores", newGraph, []step{{op: "marshal"}})
	// a stale top-level cache: cached Size returns it, cached Marshal is right (encode.go:52-58;
	// proto/encode.go:184-192)
	for _, v := range []int32{1, 2, 5, 1000, 1 << 16, -1, -1000, 0x7fffffff} {
		twin(t, "stale top", newGraph, []step{{op: "set", i: 0, val: v}, {op: "csize"}, {op: "cmarshal"},
			{op: "set", i: 0, val: v}, {op: "cappend"}})
	}
	// a level at 0 recomputed over a stale child: the stale-derived write (encode.go:60, 128)
	twin(t, "stale-derived", newGraph, []step{{op: "size"}, {op: "set", i: 0}, {op: "set", i: 1},
		{op: "set", i: 2, val: 40}, {op: "csize"}, {op: "size"}})
	// a stale nested level: a size mismatch, nil (codec_field.go:163-172, 419-436), at every depth,
	// by a change or by garbage, with the levels above fresh or at 0; default Marshal right
	for _, i := range []int{1, 2, 3, 4, 5, 6} {
		for _, zero := range []bool{false, true} {
			for _, how := range []string{"mut", "garbage", "smaller"} {
				st := []step{{op: "size"}}
				switch how {
				case "mut":
					st = append(st, step{op: "mut", i: i, mut: longer})
				case "garbage":
					st = append(st, step{op: "set", i: i, val: 200})
				case "smaller":
					st = append(st, step{op: "set", i: i, val: 1})
				}
				if zero {
					for j := 0; j < 7; j++ {
						if j != i {
							st = append(st, step{op: "set", i: j})
						}
					}
				}
				st = append(st, step{op: "cmarshal"}, step{op: "cappend"}, step{op: "csize"}, step{op: "marshal"},
					step{op: "cmarshal"})
				res := twin(t, "stale nested "+how, newGraph, st)
				if n := len(res); res[n-5].err != "mismatch" || !res[n-5].isNil || res[n-2].err != "nil" {
					t.Fatalf("stale nested %s at %d (zero %v): real %v", how, i, zero, res)
				}
			}
		}
	}
	// never sized, under UseCachedSize: each level computed before its prefix (codec_field.go:164)
	twin(t, "never sized", newGraph, []step{{op: "cmarshal"}, {op: "cappend"}})
}

// dag: x is root.Inner and both of root.Inners (pbcachetest's TestCachedDAG), and a second parent
// p2 holding x too; nodes root, x, x.Sub, p2.
func dag() graph {
	x := &pb.Inner{K: "shared", V: 9, Sub: &pb.Inner{K: "leaf"}}
	root := &pb.Args{Tag: "dag", Inner: x, Inners: []*pb.Inner{x, x}}
	p2 := &pb.Args{Tag: "second parent", Inners: []*pb.Inner{{K: "other"}, x}}
	return graph{[]proto.Message{root, x, x.Sub, p2}}
}

// TestCacheShared: a sub-message reachable from two parents (#37, zeldovich's review): one
// parent marshalled (re-sizing the shared child), the other then marshalled with UseCachedSize;
// and the child changed between them.
func TestCacheShared(t *testing.T) {
	twin(t, "dag unsized", dag, []step{{op: "cmarshal"}, {op: "cmarshal", i: 3}})
	twin(t, "dag fresh", dag, []step{{op: "size"}, {op: "set"}, {op: "cmarshal"}})
	twin(t, "dag stale", dag, []step{{op: "size"}, {op: "set"}, {op: "mut", i: 1, mut: longer}, {op: "cmarshal"},
		{op: "marshal"}})
	// both parents sized; the shared child changed; the first parent's default Marshal re-sizes it
	// (fresh again); the second parent's cached Marshal then reads the fresh child: right bytes
	// (its own top-level cache is stale, which only changes the buffer's capacity)
	res := twin(t, "two parents", dag, []step{{op: "size"}, {op: "size", i: 3}, {op: "mut", i: 1, mut: longer},
		{op: "marshal"}, {op: "cmarshal", i: 3}, {op: "cappend", i: 3}, {op: "csize", i: 3}})
	if res[4].err != "nil" || res[5].err != "nil" {
		t.Fatalf("two parents: %v", res)
	}
	// the same with the leaf under the shared child changed: the first parent's cached Marshal
	// fails (the leaf's cache is stale), the second's too; a default Size of the second repairs
	// every level it reaches, and its cached Marshal then succeeds
	res = twin(t, "two parents, stale leaf", dag, []step{{op: "size"}, {op: "size", i: 3}, {op: "mut", i: 2, mut: longer},
		{op: "cmarshal"}, {op: "cmarshal", i: 3}, {op: "size", i: 3}, {op: "cmarshal", i: 3}, {op: "cmarshal"}})
	if res[3].err != "mismatch" || res[4].err != "mismatch" || res[6].err != "nil" {
		t.Fatalf("two parents, stale leaf: %v", res)
	}
}

// TestCacheConcurrentStaleChild: pbcachetest's TestConcurrentDefaultMarshalOverStaleChild with the
// methods: default Marshal (by the methods) racing a cached Size (by the methods, or by real
// protobuf-go: they write the same field) over a stale child can fail with a size mismatch, as
// protobuf-go's can; every outcome must be the right bytes or a mismatch with nil. Under -race:
// the methods' and protobuf-go's accesses to the cache are atomic.
func TestCacheConcurrentStaleChild(t *testing.T) {
	mism := 0
	for i := 0; i < 5000; i++ {
		b := &pb.Inner{K: "b"}
		proto.Size(b)
		b.K = "b, now longer than it was"
		a := &pb.Inner{K: "a", Sub: b}
		root := &pb.Args{Inner: a}
		want, _ := proto.Marshal(proto.Clone(root))
		var wg sync.WaitGroup
		var out []byte
		var err error
		wg.Add(2)
		go func() { defer wg.Done(); out, err = modelMarshal(nil, root, false, false) }()
		go func() {
			defer wg.Done()
			if i%2 == 0 {
				root.PbModelSize(true)
			} else {
				proto.MarshalOptions{UseCachedSize: true}.Size(root)
			}
		}()
		wg.Wait()
		switch {
		case class(err) == "mismatch" && out == nil:
			mism++
		case err != nil || !bytes.Equal(out, want):
			t.Fatalf("iteration %d: %x, %v; want %x or a size mismatch", i, out, err, want)
		}
	}
	t.Logf("the methods' default Marshal failed with a size mismatch in %d of 5000 races", mism)
}
