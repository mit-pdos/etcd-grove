// The independent attack of auth-schema-srv A3 (2026-11-17, for etcd-grove-03; notes/axiom-review/auth-a3-marshal.md),
// copied from its scratch module (/shared/tmp/a3-attack/mod/att/big_test.go) with the package renamed.

package authpbmarshal

import (
	"os"
	"testing"

	"go.etcd.io/etcd/api/v3/authpb"
	"google.golang.org/protobuf/proto"
)

// nested size above MaxInt32-1: the cache stores 0, the marshal pass recomputes.
func TestBigNested(t *testing.T) {
	if os.Getenv("A3BIG") == "" {
		t.Skip()
	}
	k := make([]byte, 1<<31)
	pm := &authpb.Permission{PermType: 1, Key: k, RangeEnd: []byte("z")}
	r := &authpb.Role{Name: []byte("x"), KeyPermission: []*authpb.Permission{pm}}
	b, err := proto.Marshal(r)
	t.Logf("len=%d err=%v cache=%d", len(b), err, sizeCache(pm))
	var r2 authpb.Role
	err = proto.Unmarshal(b, &r2)
	t.Logf("unmarshal err=%v keylen=%d", err, len(r2.KeyPermission[0].Key))
}
