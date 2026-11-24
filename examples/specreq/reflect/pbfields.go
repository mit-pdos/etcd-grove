package reflect

// protobuf-go's repeated and map fields as reflect.Values: protoreflect.List
// and protoreflect.Map over a *[]T and a map[K]V of the generated struct.
//
// Mirrors google.golang.org/protobuf@v1.36.12 internal/impl/
// convert_list.go:102-140 (listReflect{v *[]T}: Len is `ls.v.Elem().Len()`
// (0 if v.IsNil()), Get `conv.PBValueOf(ls.v.Elem().Index(i))`, Set
// `ls.v.Elem().Index(i).Set(conv.GoValueOf(v))`, Append
// `ls.v.Elem().Set(reflect.Append(ls.v.Elem(), conv.GoValueOf(v)))`, Truncate
// `ls.v.Elem().Set(ls.v.Elem().Slice(0, i))`) and convert_map.go:60-115
// (mapReflect{v map[K]V}: Len, Has `v.MapIndex(rk).IsValid()`, Get, Set
// `v.SetMapIndex(rk, rv)`, Clear `v.SetMapIndex(rk, reflect.Value{})`,
// Range by `v.MapRange()`), with a scalar converter (convert.go:145-200).
// In protobuf-go the *[]T comes from the message pointer and the field's
// offset (`p.Apply(off).AsValueOf(fs.Type)`, reflect.NewAt: unsafedep.go);
// here it is `&msg.Voters` taken by Go. Users: every repeated and map field
// of a generated message through its ProtoReflect: raftpb.ConfState's
// Voters, Learners, VotersOutgoing, LearnersNext (proto.Clone of a
// ConfState: raftpb/confstate.go:31-32, raft log.go:295, raft.go:835,
// storage.go:213-262), etcdserverpb's repeated fields (TxnRequest's
// Compare/Success/Failure, RangeResponse's Kvs), proto.Equal, proto.Merge
// (client/v3 kv.go:105, golang/protobuf), the text and JSON formats.
//
// Go's panics: Index out of range "reflect: slice index out of range";
// Slice(0, i) beyond the capacity "reflect.Value.Slice: slice index out of
// bounds"; SetMapIndex on a nil map "assignment to entry in nil map".
//
// To prove: the list view's Len/Get/Set/Append/Truncate are those of the
// field's slice (writes are visible in the message), and the map view's
// Len/Has/Get/Set/Clear/Range are those of the field's map, Range in some
// order visiting each entry once.
//
// Needs R2 (Elem of a pointer to a slice field, Len, Index, Set, Append,
// Slice, MapIndex with IsValid, SetMapIndex including deletion by the zero
// Value, MapRange) and R1 (identity for the converter's check).

import (
	"fmt"
	"reflect"
	"sort"
)

type ConfState struct {
	Voters   []uint64
	Learners []uint64
	Labels   map[string]uint64
}

// scalarConv is the uint64 converter (convert.go: uint64Converter); values in the
// protoreflect view are plain uint64s.
type scalarConv struct{ goType reflect.Type }

func (c scalarConv) PBValueOf(v reflect.Value) uint64 {
	if v.Type() != c.goType {
		panic(fmt.Sprintf("invalid type: got %v, want %v", v.Type(), c.goType))
	}
	return v.Uint()
}

func (c scalarConv) GoValueOf(x uint64) reflect.Value {
	return reflect.ValueOf(x).Convert(c.goType)
}

type listReflect struct {
	v    reflect.Value // *[]T
	conv scalarConv
}

func (ls *listReflect) Len() int {
	if ls.v.IsNil() {
		return 0
	}
	return ls.v.Elem().Len()
}
func (ls *listReflect) Get(i int) uint64    { return ls.conv.PBValueOf(ls.v.Elem().Index(i)) }
func (ls *listReflect) Set(i int, x uint64) { ls.v.Elem().Index(i).Set(ls.conv.GoValueOf(x)) }
func (ls *listReflect) Append(x uint64) {
	ls.v.Elem().Set(reflect.Append(ls.v.Elem(), ls.conv.GoValueOf(x)))
}
func (ls *listReflect) Truncate(i int) { ls.v.Elem().Set(ls.v.Elem().Slice(0, i)) }

type mapReflect struct {
	v               reflect.Value // map[K]V
	keyConv, valCon reflect.Type
}

func (ms *mapReflect) Len() int { return ms.v.Len() }
func (ms *mapReflect) Has(k string) bool {
	return ms.v.MapIndex(reflect.ValueOf(k).Convert(ms.keyConv)).IsValid()
}
func (ms *mapReflect) Get(k string) (uint64, bool) {
	rv := ms.v.MapIndex(reflect.ValueOf(k).Convert(ms.keyConv))
	if !rv.IsValid() {
		return 0, false
	}
	return rv.Uint(), true
}
func (ms *mapReflect) Set(k string, x uint64) {
	ms.v.SetMapIndex(reflect.ValueOf(k).Convert(ms.keyConv), reflect.ValueOf(x).Convert(ms.valCon))
}
func (ms *mapReflect) Clear(k string) {
	ms.v.SetMapIndex(reflect.ValueOf(k).Convert(ms.keyConv), reflect.Value{})
}
func (ms *mapReflect) Range(f func(string, uint64) bool) {
	iter := ms.v.MapRange()
	for iter.Next() {
		if !f(iter.Key().String(), iter.Value().Uint()) {
			return
		}
	}
}

// cloneVoters is proto.Clone's copy of a repeated field through the list views.
func cloneVoters(dst, src *listReflect) {
	for i := 0; i < src.Len(); i++ {
		dst.Append(src.Get(i))
	}
}

// REQ reflect/pb-fields: the list view of ConfState.Voters reads, writes, appends and
// truncates the message's own slice; Clone through two views copies the elements (the copy
// does not alias); the map view sets, finds, clears and ranges over the message's map.
// Users: protobuf-go internal/impl/convert_list.go:102-140, convert_map.go:60-115 (every
// repeated and map field: proto.Clone of raftpb.ConfState, raft log.go:295, raft.go:835,
// storage.go:213-262; proto.Equal; proto.Merge, client/v3 kv.go:105).
// Assumes: nothing.
// Specs: none yet; needs R1 and R2 (doc.go).
func ReqPBFields() {
	u64 := reflect.TypeOf(uint64(0))
	cs := &ConfState{Voters: []uint64{1, 2}}
	ls := &listReflect{v: reflect.ValueOf(&cs.Voters), conv: scalarConv{u64}}
	if ls.Len() != 2 || ls.Get(1) != 2 {
		panic("pb-fields: Len, Get")
	}
	ls.Set(0, 5)
	ls.Append(7)
	if len(cs.Voters) != 3 || cs.Voters[0] != 5 || cs.Voters[2] != 7 {
		panic("pb-fields: Set and Append write the message's field")
	}
	ls.Truncate(1)
	if len(cs.Voters) != 1 || cs.Voters[0] != 5 {
		panic("pb-fields: Truncate")
	}
	clone := &ConfState{}
	cl := &listReflect{v: reflect.ValueOf(&clone.Learners), conv: scalarConv{u64}}
	cloneVoters(cl, ls)
	cs.Voters[0] = 9
	if len(clone.Learners) != 1 || clone.Learners[0] != 5 {
		panic("pb-fields: the clone does not alias")
	}
	cs.Labels = map[string]uint64{}
	ms := &mapReflect{v: reflect.ValueOf(cs.Labels), keyConv: reflect.TypeOf(""), valCon: u64}
	ms.Set("b", 2)
	ms.Set("a", 1)
	if ms.Len() != 2 || !ms.Has("a") || ms.Has("z") {
		panic("pb-fields: map Set, Has")
	}
	if x, ok := ms.Get("b"); !ok || x != 2 || cs.Labels["b"] != 2 {
		panic("pb-fields: map Get")
	}
	ms.Clear("b")
	if ms.Len() != 1 || ms.Has("b") {
		panic("pb-fields: map Clear")
	}
	var keys []string
	ms.Set("c", 3)
	ms.Range(func(k string, _ uint64) bool { keys = append(keys, k); return true })
	sort.Strings(keys)
	if len(keys) != 2 || keys[0] != "a" || keys[1] != "c" {
		panic("pb-fields: map Range visits each entry once")
	}
}
