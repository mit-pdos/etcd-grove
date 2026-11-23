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

// TestConfChangeEnumStringIsNameTable: the same of ConfChangeType.String and
// ConfChangeTransition.String against ConfChangeType_name and ConfChangeTransition_name, what their
// trusted models (TrustedCode/go_etcd_io/raft/v3/raftpb.lean, etcd-grove#25) compute;
// DescribeConfChange formats both with %v.
func TestConfChangeEnumStringIsNameTable(t *testing.T) {
	if len(raftpb.ConfChangeType_name) != 4 {
		t.Errorf("ConfChangeType_name has %d entries, the model's table 4", len(raftpb.ConfChangeType_name))
	}
	if len(raftpb.ConfChangeTransition_name) != 3 {
		t.Errorf("ConfChangeTransition_name has %d entries, the model's table 3",
			len(raftpb.ConfChangeTransition_name))
	}
	for v, name := range raftpb.ConfChangeType_name {
		if got := raftpb.ConfChangeType(v).String(); got != name {
			t.Errorf("ConfChangeType(%d).String() = %q, ConfChangeType_name[%d] = %q", v, got, v, name)
		}
	}
	for v, name := range raftpb.ConfChangeTransition_name {
		if got := raftpb.ConfChangeTransition(v).String(); got != name {
			t.Errorf("ConfChangeTransition(%d).String() = %q, ConfChangeTransition_name[%d] = %q",
				v, got, v, name)
		}
	}
	// the descriptors name no other value: the fallback is strconv.Itoa(int(x))
	for _, v := range []int32{-1, 3, 4, 5, 1000, -2147483648, 2147483647} {
		if _, ok := raftpb.ConfChangeType_name[v]; !ok {
			if got, want := raftpb.ConfChangeType(v).String(), strconv.Itoa(int(v)); got != want {
				t.Errorf("ConfChangeType(%d).String() = %q, want %q", v, got, want)
			}
		}
		if _, ok := raftpb.ConfChangeTransition_name[v]; !ok {
			if got, want := raftpb.ConfChangeTransition(v).String(), strconv.Itoa(int(v)); got != want {
				t.Errorf("ConfChangeTransition(%d).String() = %q, want %q", v, got, want)
			}
		}
	}
}
