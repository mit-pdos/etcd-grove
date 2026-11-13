package walpb

// The ownership clause of proto.MarshalAppendCachedRecord.spec
// (LinuxFs/Spec/google_golang_org/protobuf/proto/MarshalAppendCachedRecord.lean): the result b' of
// MarshalOptions{UseCachedSize: true}.MarshalAppend(b, rec) either reuses b's array (same pointer,
// same capacity) or is a fresh array that does not share b's, so b's array comes back to the caller
// (with its contents past len(b) possibly overwritten).
//
// The source, protobuf-go v1.36.12 (examples/go.mod):
//   - proto/encode.go:153-161, MarshalAppend: o.marshal(b, m.ProtoReflect()), returns out.Buf;
//   - proto/encode.go:174-210, marshal: with a Size method (walpb.Record's generated fast path),
//     `if cap(b) < len(b)+sout.Size { in.Buf = make([]byte, len(b), growcap(...)); copy(in.Buf, b) }`
//     (:189-192): a fresh array when the (possibly cached) size does not fit, b itself otherwise;
//   - internal/impl/encode.go:135-146, (*MessageInfo).marshal: marshalAppendPointer(in.Buf, ...), which
//     only appends (protowire.Append*, Go's append) to the slice it is given and returns it.
// So the result is append semantics on b (or on the fresh copy): when the appends fit b's capacity the
// result is b's array with b's capacity; otherwise Go's append moved to a new array, and nothing keeps
// b (no field, global or cache of protobuf-go stores a []byte argument). A stale cached size (the size
// cache of a record modified after proto.Size) only changes which case happens, and in the
// reallocating case after a wrong "fits" guess, b's array past len(b) has been written: hence the
// spec's "b ↦* ys" with arbitrary ys.

import (
	"bytes"
	"math/rand"
	"testing"
	"unsafe"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"google.golang.org/protobuf/proto"
)

func arr(b []byte) unsafe.Pointer { return unsafe.Pointer(unsafe.SliceData(b)) }

// check runs MarshalAppend(b, m) with the cached size and checks the two cases.
// cacheOk: the size cache is up to date, so a result fitting b's capacity must be in place.
func check(t *testing.T, b []byte, m *walpb.Record, want []byte, cacheOk bool) {
	t.Helper()
	prefix := append([]byte(nil), b...)
	got, err := proto.MarshalOptions{UseCachedSize: true}.MarshalAppend(b, m)
	if err != nil {
		t.Fatalf("MarshalAppend: %v", err)
	}
	if !bytes.Equal(got, append(prefix, want...)) {
		t.Fatalf("MarshalAppend %x, want %x ++ %x", got, prefix, want)
	}
	if arr(got) == arr(b) && cap(b) > 0 {
		// Reuses b's array: then with b's capacity.
		if cap(got) != cap(b) {
			t.Fatalf("same array, capacity %d, b's %d", cap(got), cap(b))
		}
		return
	}
	// A fresh array: disjoint from b's. Overwrite all of b's array; the result must not change.
	if cacheOk && len(prefix)+len(want) <= cap(b) && cap(b) > 0 {
		// With an up-to-date cache a fitting result is always in place.
		t.Fatalf("result fits b's capacity %d but was reallocated", cap(b))
	}
	saved := append([]byte(nil), got...)
	full := b[:cap(b)]
	for i := range full {
		full[i] ^= 0xff
	}
	if !bytes.Equal(got, saved) {
		t.Fatalf("the reallocated result shares b's array")
	}
}

func TestMarshalAppendOwnership(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	for i := 0; i < 50000; i++ {
		c := genRec(r)
		m := toGo(c)
		want := recEnc(c)
		_ = proto.Size(m) // encode's path: Size, then MarshalAppend with the cached size
		l := r.Intn(16)
		capb := l + r.Intn(len(want)+16)
		b := make([]byte, l, capb)
		r.Read(b)
		check(t, b, m, want, true)
		// A nil b (cap 0).
		_ = proto.Size(m)
		check(t, nil, m, want, true)
	}
}

// A stale cache (the record grew after proto.Size): marshal's capacity check is made with the stale
// size, b's array is reused, Go's append then reallocates mid-way. The result is still correct (no
// nested message, so no length prefix comes from the cache) and does not share b's array.
func TestMarshalAppendStaleCache(t *testing.T) {
	typ := int64(1)
	m := &walpb.Record{Type: &typ, Data: []byte("x")}
	small := proto.Size(m)
	m.Data = bytes.Repeat([]byte("y"), 1000)
	want, err := proto.Marshal(m) // recomputes; the cache now holds the large size
	if err != nil {
		t.Fatal(err)
	}
	m.Data = []byte("x")
	_ = proto.Size(m)
	m.Data = bytes.Repeat([]byte("y"), 1000) // stale: the cache says small
	b := make([]byte, 0, small+4)
	full := b[:cap(b)]
	for i := range full {
		full[i] = 0xaa
	}
	got, err := proto.MarshalOptions{UseCachedSize: true}.MarshalAppend(b, m)
	if err != nil || !bytes.Equal(got, want) {
		t.Fatalf("MarshalAppend %x (%v), want %x", got, err, want)
	}
	if arr(got) == arr(b) {
		t.Fatalf("expected a reallocation")
	}
	// b's array past len(b) was written before the reallocation: its contents are not kept.
	if bytes.Equal(full, bytes.Repeat([]byte{0xaa}, len(full))) {
		t.Fatalf("expected b's array to have been written")
	}
	saved := append([]byte(nil), got...)
	for i := range full {
		full[i] ^= 0xff
	}
	if !bytes.Equal(got, saved) {
		t.Fatalf("the reallocated result shares b's array")
	}
}
