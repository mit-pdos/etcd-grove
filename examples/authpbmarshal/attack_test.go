// The independent attack of auth-schema-srv A3 (2026-11-17, for etcd-grove-03; notes/axiom-review/auth-a3-marshal.md),
// copied from its scratch module (/shared/tmp/a3-attack/mod/att/attack_test.go) with the package renamed.

package authpbmarshal

import (
	"bytes"
	"fmt"
	"sync"
	"testing"
	"unsafe"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"google.golang.org/protobuf/encoding/protojson"
	"google.golang.org/protobuf/encoding/prototext"
	"google.golang.org/protobuf/proto"
)

func snap[T any](p *T) []byte {
	n := unsafe.Sizeof(*p)
	b := make([]byte, n)
	copy(b, unsafe.Slice((*byte)(unsafe.Pointer(p)), n))
	return b
}

// offsets of state and sizeCache to mask
func diffOutside(t *testing.T, name string, before, after []byte, allowed [][2]uintptr) {
	for i := range before {
		if before[i] == after[i] {
			continue
		}
		ok := false
		for _, a := range allowed {
			if uintptr(i) >= a[0] && uintptr(i) < a[1] {
				ok = true
			}
		}
		if !ok {
			t.Errorf("%s: byte %d changed outside allowed (%d->%d)", name, i, before[i], after[i])
		}
	}
}

// A3: Marshal of a User / Role writes nothing in the nested message but its size cache.
func TestNestedOnlySizeCache(t *testing.T) {
	o := &authpb.UserAddOptions{NoPassword: true}
	proto.Unmarshal(append([]byte{0x08, 0x01}, optsUF...), o)
	var oz authpb.UserAddOptions
	scO := unsafe.Offsetof(oz.NoPassword) // placeholder
	_ = scO
	stO := [2]uintptr{0, unsafe.Sizeof(oz.NoPassword) * 0}
	_ = stO
	// sizeCache is last field (int32)
	szO := unsafe.Sizeof(oz)
	allowedO := [][2]uintptr{{szO - 8, szO}} // sizeCache (+pad)
	u := &authpb.User{Name: []byte("n"), Password: []byte("p"), Roles: []string{"r", ""}, Options: o}
	b0 := snap(o)
	for i := 0; i < 3; i++ {
		mustMarshal(t, u)
		proto.Size(u)
	}
	diffOutside(t, "opts after Marshal", b0, snap(o), allowedO)
	// String/protojson/prototext/Equal/Clone: state may change (first 8 bytes of struct)
	_ = u.String()
	protojson.Marshal(u)
	prototext.Marshal(u)
	proto.Equal(u, proto.Clone(u))
	allowedO2 := append(allowedO, [2]uintptr{0, 8})
	diffOutside(t, "opts after reflective uses", b0, snap(o), allowedO2)

	pm := &authpb.Permission{PermType: 7, Key: []byte("a"), RangeEnd: []byte("b")}
	var pz authpb.Permission
	szP := unsafe.Sizeof(pz)
	r := &authpb.Role{Name: []byte("x"), KeyPermission: []*authpb.Permission{pm, pm}}
	p0 := snap(pm)
	mustMarshal(t, r)
	diffOutside(t, "perm after Marshal", p0, snap(pm), [][2]uintptr{{szP - 8, szP}})
	_ = r.String()
	proto.Clone(r)
	diffOutside(t, "perm after reflective", p0, snap(pm), [][2]uintptr{{szP - 8, szP}, {0, 8}})
	t.Logf("sizes opts=%d perm=%d", szO, szP)
}

// A1: concurrent Marshal of two users / roles sharing the nested message with every reflective
// reader and sizer of the nested message and of other parents (the IRR, a request).
func TestConcurrentEverything(t *testing.T) {
	o := &authpb.UserAddOptions{NoPassword: true}
	proto.Unmarshal(append([]byte{0x08, 0x01}, optsUF...), o)
	pm := &authpb.Permission{PermType: -1, Key: []byte("k"), RangeEnd: []byte("kz")}
	u1 := &authpb.User{Name: []byte("a"), Roles: []string{"r"}, Options: o}
	u2 := &authpb.User{Name: []byte("bb"), Password: []byte("pw"), Options: o}
	r1 := &authpb.Role{Name: []byte("x"), KeyPermission: []*authpb.Permission{pm, pm}}
	req := &pb.AuthUserAddRequest{Name: "zz", Options: o}
	irr := &pb.InternalRaftRequest{AuthUserAdd: req, AuthRoleGrantPermission: &pb.AuthRoleGrantPermissionRequest{Name: "q", Perm: pm}}
	w1, w2, wr := mustMarshal(t, u1), mustMarshal(t, u2), mustMarshal(t, r1)
	var wg sync.WaitGroup
	fail := make(chan string, 100)
	chk := func(m proto.Message, want []byte) {
		defer wg.Done()
		for i := 0; i < 3000; i++ {
			b, err := proto.Marshal(m)
			if err != nil || !bytes.Equal(b, want) {
				fail <- fmt.Sprintf("%T %v", m, err)
				return
			}
		}
	}
	other := func(f func()) {
		defer wg.Done()
		for i := 0; i < 3000; i++ {
			f()
		}
	}
	wg.Add(9)
	go chk(u1, w1)
	go chk(u2, w2)
	go chk(r1, wr)
	go other(func() { proto.Marshal(irr) })
	go other(func() { proto.Size(o); proto.Size(pm); proto.Size(req) })
	go other(func() { _ = o.String(); _ = pm.String() })
	go other(func() { protojson.Marshal(irr) })
	go other(func() { proto.MarshalOptions{Deterministic: true}.Marshal(irr) })
	go other(func() { proto.Equal(proto.Clone(irr), irr) })
	wg.Wait()
	close(fail)
	for f := range fail {
		t.Error(f)
	}
}

// deep group in Options' unknown fields: decode at depth 1 (request), re-encode in User and IRR,
// decode at depth 1 (User) and depth 2 (IRR).
func deepGroup(d int) []byte {
	var b []byte
	for i := 0; i < d; i++ {
		b = append(b, 0x13) // field 2 start group
	}
	for i := 0; i < d; i++ {
		b = append(b, 0x14)
	}
	return b
}

func TestDeepGroupDepths(t *testing.T) {
	for _, d := range []int{9999, 10000, 10001, 10002} {
		raw := append([]byte{0x22}, appendLen(deepGroup(d))...) // AuthUserAddRequest field 3? check
		_ = raw
		o := &authpb.UserAddOptions{}
		errO := proto.Unmarshal(deepGroup(d), o)
		reqB := append([]byte{0x1a}, appendLen(deepGroup(d))...) // AuthUserAddRequest.options = 3
		req := &pb.AuthUserAddRequest{}
		errR := proto.Unmarshal(reqB, req)
		res := fmt.Sprintf("d=%d opts:%v req:%v", d, errO, errR)
		if errR == nil {
			u := &authpb.User{Options: req.Options}
			ub, err := proto.Marshal(u)
			var u2 authpb.User
			err2 := proto.Unmarshal(ub, &u2)
			irr := &pb.InternalRaftRequest{AuthUserAdd: req}
			ib, err3 := proto.Marshal(irr)
			var irr2 pb.InternalRaftRequest
			err4 := proto.Unmarshal(ib, &irr2)
			res += fmt.Sprintf(" user marshal:%v unmarshal:%v irr marshal:%v unmarshal:%v", err, err2, err3, err4)
		}
		t.Log(res)
	}
}

func appendLen(b []byte) []byte {
	n := len(b)
	var v []byte
	for n >= 128 {
		v = append(v, byte(n%128+128))
		n /= 128
	}
	v = append(v, byte(n))
	return append(v, b...)
}
