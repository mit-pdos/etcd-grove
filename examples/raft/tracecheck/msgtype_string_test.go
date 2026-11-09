//go:build with_tla

package tracecheck

import (
	"strconv"
	"testing"

	"go.etcd.io/raft/v3/raftpb"
)

// TestMessageTypeStringIsNameTable: protoc-gen-go's MessageType.String (protoimpl.X.EnumStringOf
// over the file descriptor) returns MessageType_name's entry for every key of the table, and the
// decimal for a number the enum does not declare: what the trusted model of the method
// (TrustedCode/go_etcd_io/raft/v3/raftpb.lean, Q9 of notes/trace-validation-plan.md) computes.
func TestMessageTypeStringIsNameTable(t *testing.T) {
	if len(raftpb.MessageType_name) != 24 {
		t.Errorf("MessageType_name has %d entries, the model's table 24", len(raftpb.MessageType_name))
	}
	for v, name := range raftpb.MessageType_name {
		if got := raftpb.MessageType(v).String(); got != name {
			t.Errorf("MessageType(%d).String() = %q, MessageType_name[%d] = %q", v, got, v, name)
		}
	}
	// the descriptor names no other value: the fallback is strconv.Itoa(int(x))
	for _, v := range []int32{-1, 24, 25, 1000, -2147483648, 2147483647} {
		if _, ok := raftpb.MessageType_name[v]; ok {
			t.Fatalf("MessageType_name has key %d", v)
		}
		if got, want := raftpb.MessageType(v).String(), strconv.Itoa(int(v)); got != want {
			t.Errorf("MessageType(%d).String() = %q, want %q", v, got, want)
		}
	}
}
