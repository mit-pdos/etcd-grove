// Package authpbmarshal backs the trust-boundary axioms proto.MarshalUser / proto.MarshalRole and the
// restated message predicates auth.userOptsIs / auth.ownPermW / auth.ownPermS (auth-schema-srv A3,
// 2026-11-17; Draft notes/auth-schema-srv-a3-draft.md). Each test is one claim of those texts, or
// one behaviour they must exclude, against protobuf-go v1.36.12 (examples/go.mod's pin) and the
// fork's authpb (the etcd pin 8c28a4296f). Run with -race: TestConcurrentSharedNested is the
// concurrency claim.
//
// protobuf-go lines cited (v1.36.12): proto/encode.go:105-116 (Marshal), 173-207 (marshal: Size
// first, then Marshal with UseCachedSize); internal/impl/encode.go:47-60 (sizePointer reads the
// cache only under UseCachedSize), 63-125 (sizePointerSlow stores size+1, or 0, atomically),
// codec_field.go:159-173 (a nested message: its size, then its bytes, checked against each other),
// codec_gen.go:5250-5260 (repeated proto3 string: UTF-8 checked).
package authpbmarshal

import (
	"bytes"
	"reflect"
	"sync"
	"sync/atomic"
	"testing"
	"unsafe"

	"go.etcd.io/etcd/api/v3/authpb"
	"google.golang.org/protobuf/proto"
)

// --- access to protobuf-go's internal fields (test only) ---

func field(m any, name string) reflect.Value {
	return reflect.ValueOf(m).Elem().FieldByName(name)
}

func sizeCacheP(m any) *int32 { return (*int32)(unsafe.Pointer(field(m, "sizeCache").UnsafeAddr())) }

func sizeCache(m any) int32 { return atomic.LoadInt32(sizeCacheP(m)) }

func setSizeCache(m any, v int32) { atomic.StoreInt32(sizeCacheP(m), v) }

// stateSet: the message's MessageState holds a message info (ProtoReflect stored it).
func stateSet(m any) bool {
	return atomic.LoadPointer((*unsafe.Pointer)(unsafe.Pointer(
		field(m, "state").FieldByName("atomicMessageInfo").UnsafeAddr()))) != nil
}

func mustMarshal(t *testing.T, m proto.Message) []byte {
	t.Helper()
	b, err := proto.Marshal(m)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	return b
}

// unknown fields for UserAddOptions that are valid wire format and use no known field
// (`ufWire userOptsSchema`): field 2 varint 5, field 7 bytes "xy", field 1 as fixed32 (field 1 with
// another wire type than varint stays unknown).
var optsUF = []byte{0x10, 0x05, 0x3a, 0x02, 'x', 'y', 0x0d, 1, 2, 3, 4}

func newOpts(noPw bool, uf []byte) *authpb.UserAddOptions {
	o := &authpb.UserAddOptions{NoPassword: noPw}
	if uf != nil {
		o.ProtoReflect().SetUnknown(uf)
	}
	return o
}

func sampleUser(o *authpb.UserAddOptions) *authpb.User {
	return &authpb.User{
		Name: []byte("alice"), Password: []byte("$2a$10$hash"),
		Roles: []string{"", "r1", "r2"}, Options: o,
	}
}

func samplePerms() []*authpb.Permission {
	return []*authpb.Permission{
		{PermType: authpb.READ, Key: []byte("a"), RangeEnd: []byte("b")},
		{PermType: authpb.WRITE, Key: []byte("k")},
		{PermType: authpb.READWRITE, Key: []byte("x"), RangeEnd: []byte{0}},
		{PermType: authpb.Permission_Type(7), Key: []byte("u")},
		{PermType: authpb.Permission_Type(-1), Key: []byte("n"), RangeEnd: []byte("o")},
	}
}

// 1. Marshal writes the size cache of every nested message (the Options, each permission): the
// pre-A3 predicates' `↦□` of `sizeCache` claimed a cell that Marshal changes.
func TestMarshalWritesNestedSizeCache(t *testing.T) {
	o := newOpts(true, optsUF)
	u := sampleUser(o)
	if sizeCache(o) != 0 || sizeCache(u) != 0 {
		t.Fatal("fresh messages have a size cache")
	}
	mustMarshal(t, u)
	if sizeCache(o) == 0 {
		t.Fatal("Options' sizeCache not written by Marshal of the User")
	}
	if got, want := int(sizeCache(o)), proto.Size(o)+1; got != want {
		t.Fatalf("Options' sizeCache %d, want size+1 = %d", got, want)
	}
	ps := samplePerms()
	r := &authpb.Role{Name: []byte("r"), KeyPermission: ps}
	mustMarshal(t, r)
	for i, p := range ps {
		if sizeCache(p) == 0 {
			t.Fatalf("permission %d's sizeCache not written by Marshal of the Role", i)
		}
	}
}

// 2. Marshal stores the top message's `state` (ProtoReflect) but not a nested message's; a
// reflective use of the parent (String) does store the nested one's: `state` is not stable either,
// so the restated predicates hold no `state` of a nested message.
func TestStateWrites(t *testing.T) {
	o := newOpts(false, nil)
	u := sampleUser(o)
	if stateSet(u) || stateSet(o) {
		t.Fatal("fresh messages have a state")
	}
	mustMarshal(t, u)
	if !stateSet(u) {
		t.Fatal("Marshal did not set the top message's state")
	}
	if stateSet(o) {
		t.Fatal("Marshal set the nested Options' state")
	}
	_ = u.String()
	if !stateSet(o) {
		t.Fatal("String did not set the nested Options' state")
	}
	p := samplePerms()[0]
	r := &authpb.Role{Name: []byte("r"), KeyPermission: []*authpb.Permission{p}}
	mustMarshal(t, r)
	if stateSet(p) {
		t.Fatal("Marshal set a nested permission's state")
	}
}

// 3. A stale or garbage size cache (any int32, in the top message or a nested one) does not change
// the result: Marshal recomputes every size first (no UseCachedSize in its Size pass) and only then
// reads the caches. So the invariant may hold any value.
func TestStaleSizeCacheIgnored(t *testing.T) {
	want := mustMarshal(t, sampleUser(newOpts(true, optsUF)))
	wantR := mustMarshal(t, &authpb.Role{Name: []byte("r"), KeyPermission: samplePerms()})
	for _, v := range []int32{1, 2, 3, 1000, -1, -1 << 31, 1<<31 - 1} {
		o := newOpts(true, optsUF)
		u := sampleUser(o)
		setSizeCache(o, v)
		setSizeCache(u, v)
		if got := mustMarshal(t, u); !bytes.Equal(got, want) {
			t.Fatalf("garbage sizeCache %d: %x, want %x", v, got, want)
		}
		ps := samplePerms()
		r := &authpb.Role{Name: []byte("r"), KeyPermission: ps}
		setSizeCache(r, v)
		for _, p := range ps {
			setSizeCache(p, v)
		}
		if got := mustMarshal(t, r); !bytes.Equal(got, wantR) {
			t.Fatalf("garbage sizeCache %d (role): %x, want %x", v, got, wantR)
		}
	}
}

// 4. The encoding is a function of the record: representations of one record (nil vs empty byte
// fields and lists, the Options' unknown fields nil vs empty, a fresh vs a decoded vs an already
// marshaled message, repeated calls) give the same bytes.
func TestDeterministicRecord(t *testing.T) {
	mk := []func() *authpb.User{
		func() *authpb.User { return &authpb.User{Roles: nil, Options: newOpts(false, nil)} },
		func() *authpb.User {
			return &authpb.User{Name: []byte{}, Password: []byte{}, Roles: []string{}, Options: newOpts(false, []byte{})}
		},
	}
	a, b := mustMarshal(t, mk[0]()), mustMarshal(t, mk[1]())
	if !bytes.Equal(a, b) {
		t.Fatalf("nil vs empty fields: %x vs %x", a, b)
	}
	u := sampleUser(newOpts(true, optsUF))
	want := mustMarshal(t, u)
	for i := 0; i < 100; i++ {
		if got := mustMarshal(t, u); !bytes.Equal(got, want) {
			t.Fatalf("call %d differs", i)
		}
	}
	dec := &authpb.User{}
	if err := proto.Unmarshal(want, dec); err != nil {
		t.Fatal(err)
	}
	if got := mustMarshal(t, dec); !bytes.Equal(got, want) {
		t.Fatalf("decoded copy: %x, want %x", got, want)
	}
	// Roles in a fresh slice of the same strings: same bytes.
	u2 := sampleUser(newOpts(true, append([]byte(nil), optsUF...)))
	u2.Roles = append([]string(nil), u.Roles...)
	if got := mustMarshal(t, u2); !bytes.Equal(got, want) {
		t.Fatalf("fresh copy: %x, want %x", got, want)
	}
	// Role: permission Key nil vs empty, RangeEnd nil vs empty.
	r1 := &authpb.Role{Name: []byte("r"), KeyPermission: []*authpb.Permission{{PermType: authpb.READ}}}
	r2 := &authpb.Role{Name: []byte("r"), KeyPermission: []*authpb.Permission{{PermType: authpb.READ, Key: []byte{}, RangeEnd: []byte{}}}}
	if x, y := mustMarshal(t, r1), mustMarshal(t, r2); !bytes.Equal(x, y) {
		t.Fatalf("role nil vs empty: %x vs %x", x, y)
	}
	wantR := mustMarshal(t, &authpb.Role{Name: []byte("r"), KeyPermission: samplePerms()})
	decR := &authpb.Role{}
	if err := proto.Unmarshal(wantR, decR); err != nil {
		t.Fatal(err)
	}
	if got := mustMarshal(t, decR); !bytes.Equal(got, wantR) {
		t.Fatalf("decoded role: %x, want %x", got, wantR)
	}
}

// 5. A nil Options and an empty one encode differently (field 4 absent vs present with length 0),
// and decode back to nil and to a non-nil message without unknown fields: the record's `optsUF`
// none vs some []. An empty role name is encoded and decoded back.
func TestNilVsEmptyOptions(t *testing.T) {
	un := &authpb.User{Name: []byte("a"), Roles: []string{""}}
	ue := &authpb.User{Name: []byte("a"), Roles: []string{""}, Options: &authpb.UserAddOptions{}}
	bn, be := mustMarshal(t, un), mustMarshal(t, ue)
	if bytes.Equal(bn, be) {
		t.Fatal("nil and empty Options encode the same")
	}
	dn, de := &authpb.User{}, &authpb.User{}
	if err := proto.Unmarshal(bn, dn); err != nil {
		t.Fatal(err)
	}
	if err := proto.Unmarshal(be, de); err != nil {
		t.Fatal(err)
	}
	if dn.Options != nil || de.Options == nil || len(de.Options.ProtoReflect().GetUnknown()) != 0 {
		t.Fatalf("decoded Options: %v, %v", dn.Options, de.Options)
	}
	if len(dn.Roles) != 1 || dn.Roles[0] != "" {
		t.Fatalf("empty role lost: %q", dn.Roles)
	}
}

// 6. The Options' unknown fields go into the encoding verbatim and come back unchanged (with either
// NoPassword); the top message's unknown fields decode nil.
func TestOptionsUnknownRoundTrip(t *testing.T) {
	for _, np := range []bool{false, true} {
		u := sampleUser(newOpts(np, optsUF))
		b := mustMarshal(t, u)
		d := &authpb.User{}
		if err := proto.Unmarshal(b, d); err != nil {
			t.Fatal(err)
		}
		if d.Options == nil || d.Options.NoPassword != np ||
			!bytes.Equal(d.Options.ProtoReflect().GetUnknown(), optsUF) {
			t.Fatalf("NoPassword=%v: decoded %v unknown %x", np, d.Options, d.Options.ProtoReflect().GetUnknown())
		}
		if len(d.ProtoReflect().GetUnknown()) != 0 {
			t.Fatal("top-level unknown fields after decode")
		}
		if !bytes.Equal(d.Name, u.Name) || !bytes.Equal(d.Password, u.Password) ||
			!reflect.DeepEqual(d.Roles, u.Roles) {
			t.Fatalf("fields differ: %v vs %v", d, u)
		}
	}
}

// 7. A role's permissions (any int32 type, open enum) come back as they were, in order.
func TestRoleRoundTrip(t *testing.T) {
	ps := samplePerms()
	b := mustMarshal(t, &authpb.Role{Name: []byte("r"), KeyPermission: ps})
	d := &authpb.Role{}
	if err := proto.Unmarshal(b, d); err != nil {
		t.Fatal(err)
	}
	if len(d.KeyPermission) != len(ps) {
		t.Fatalf("%d permissions, want %d", len(d.KeyPermission), len(ps))
	}
	for i, p := range ps {
		q := d.KeyPermission[i]
		if q.PermType != p.PermType || !bytes.Equal(q.Key, p.Key) || !bytes.Equal(q.RangeEnd, p.RangeEnd) ||
			len(q.ProtoReflect().GetUnknown()) != 0 {
			t.Fatalf("permission %d: %v, want %v", i, q, p)
		}
	}
}

// 8. A role name that is not valid UTF-8 makes Marshal fail (the premise of MarshalUser).
func TestInvalidUTF8Role(t *testing.T) {
	_, err := proto.Marshal(&authpb.User{Name: []byte("a"), Roles: []string{"ok", "\xff"}})
	if err == nil {
		t.Fatal("Marshal accepted an invalid UTF-8 role")
	}
	t.Logf("error: %v", err)
}

// 9. The result is fresh: writing it does not change the message or the next encoding.
func TestFreshResult(t *testing.T) {
	u := sampleUser(newOpts(true, optsUF))
	b := mustMarshal(t, u)
	want := append([]byte(nil), b...)
	for i := range b {
		b[i] = 0xee
	}
	if got := mustMarshal(t, u); !bytes.Equal(got, want) {
		t.Fatal("result aliases the message")
	}
	if string(u.Name) != "alice" || u.Roles[1] != "r1" {
		t.Fatal("message changed")
	}
}

// 10. Concurrency (run with -race): two Users sharing one Options message, two Roles sharing a
// permission message (one of them holding it twice), marshaled by many goroutines at once while
// others read the read-only fields: no race report (the size cache is accessed atomically, the other
// fields only read), and every result is the encoding of its record.
func TestConcurrentSharedNested(t *testing.T) {
	o := newOpts(true, optsUF)
	u1 := sampleUser(o)
	u2 := &authpb.User{Name: []byte("bob"), Roles: []string{"r3"}, Options: o}
	p := &authpb.Permission{PermType: authpb.READWRITE, Key: []byte("k"), RangeEnd: []byte("l")}
	r1 := &authpb.Role{Name: []byte("r1"), KeyPermission: []*authpb.Permission{p, p}}
	r2 := &authpb.Role{Name: []byte("r2"), KeyPermission: []*authpb.Permission{samplePerms()[0], p}}
	// expected: from independent copies
	c := func(m proto.Message) []byte { return mustMarshal(t, proto.Clone(m)) }
	want := map[proto.Message][]byte{u1: c(u1), u2: c(u2), r1: c(r1), r2: c(r2)}
	// Each top message is owned by one goroutine (the axioms take the top message exclusively);
	// the nested ones are shared.
	var wg sync.WaitGroup
	var bad atomic.Int32
	for m, w := range want {
		wg.Add(1)
		go func(m proto.Message, w []byte) {
			defer wg.Done()
			for i := 0; i < 2000; i++ {
				b, err := proto.Marshal(m)
				if err != nil || !bytes.Equal(b, w) {
					bad.Add(1)
				}
			}
		}(m, w)
	}
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 2000; j++ {
				if !o.GetNoPassword() || len(o.ProtoReflect().GetUnknown()) != len(optsUF) ||
					string(p.GetKey()) != "k" || p.GetPermType() != authpb.READWRITE {
					bad.Add(1)
				}
			}
		}()
	}
	wg.Wait()
	if n := bad.Load(); n != 0 {
		t.Fatalf("%d wrong results", n)
	}
}
