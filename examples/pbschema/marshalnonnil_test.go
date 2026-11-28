package pbschema

// Evidence for the post `⌜l ≠ null → d ≠ slice.nil⌝` of the trust-boundary axiom proto.MarshalPb.spec
// (Spec/google_golang_org/protobuf/proto/MarshalPb.lean; notes/specs-only/ledger.md, 2026-11-28): at
// protobuf-go v1.36.12 (examples/go.mod's pin), proto.Marshal of a non-nil *T returns a non-nil slice and
// a nil error, also when the encoding is empty (proto/encode.go: Marshal replaces an empty result by
// emptyBytesForMessage(m), the non-nil emptyBuf[:] for a valid message). The types: every type the proofs
// register with pbModelOf (walpb.Record, walpb.Snapshot, raftpb.Entry, raftpb.HardState, raftpb.Message)
// and those the WAL's records carry (raftpb.Snapshot, raftpb.ConfState), at etcd's and raft's pins
// (examples/go.mod's replaces). A nil *T (an invalid message; outside the post's l ≠ null) is recorded too.
//
// Run: cd examples && go test ./pbschema -run TestMarshalNonNil -v. Output (2026-11-28, go1.27.1, PASS):
//
//	walpb.Record{} (empty)                 d==nil=false len=0   err=<nil>
//	walpb.Record (populated)               d==nil=false len=14  err=<nil>
//	walpb.Record (Data empty, not nil)     d==nil=false len=4   err=<nil>
//	walpb.Snapshot{} (empty)               d==nil=false len=0   err=<nil>
//	walpb.Snapshot (populated)             d==nil=false len=14  err=<nil>
//	raftpb.Entry{} (empty)                 d==nil=false len=0   err=<nil>
//	raftpb.Entry (populated)               d==nil=false len=9   err=<nil>
//	raftpb.HardState{} (empty)             d==nil=false len=0   err=<nil>
//	raftpb.HardState (zero fields set)     d==nil=false len=6   err=<nil>
//	raftpb.HardState (populated)           d==nil=false len=6   err=<nil>
//	raftpb.Snapshot{} (empty)              d==nil=false len=0   err=<nil>
//	raftpb.Snapshot (populated)            d==nil=false len=22  err=<nil>
//	raftpb.ConfState{} (empty)             d==nil=false len=0   err=<nil>
//	raftpb.ConfState (populated)           d==nil=false len=8   err=<nil>
//	raftpb.Message{} (empty)               d==nil=false len=0   err=<nil>
//	raftpb.Message (populated)             d==nil=false len=14  err=<nil>
//	nil *walpb.Record                      d==nil=true  len=0   err=<nil>
//	nil *walpb.Snapshot                    d==nil=true  len=0   err=<nil>
//	nil *raftpb.Entry                      d==nil=true  len=0   err=<nil>
//	nil *raftpb.HardState                  d==nil=true  len=0   err=<nil>
//	nil *raftpb.Snapshot                   d==nil=true  len=0   err=<nil>
//	nil *raftpb.ConfState                  d==nil=true  len=0   err=<nil>
//	nil *raftpb.Message                    d==nil=true  len=0   err=<nil>
//
// Every non-nil *T, empty or not, gives a non-nil slice and nil. A nil *T gives (nil, nil): the case the
// post's premise l ≠ null leaves out.

import (
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

func TestMarshalNonNil(t *testing.T) {
	u64 := func(x uint64) *uint64 { return &x }
	i64 := func(x int64) *int64 { return &x }
	u32 := func(x uint32) *uint32 { return &x }
	et := raftpb.EntryType_EntryNormal
	mt := raftpb.MessageType_MsgApp
	cs := &raftpb.ConfState{Voters: []uint64{1, 2, 3}, Learners: []uint64{4}}
	md := &raftpb.SnapshotMetadata{Index: u64(10), Term: u64(2), ConfState: cs}
	cases := []struct {
		name  string
		m     proto.Message
		valid bool // a non-nil *T: the post claims d != nil
	}{
		{"walpb.Record{} (empty)", &walpb.Record{}, true},
		{"walpb.Record (populated)", &walpb.Record{Type: i64(2), Crc: u32(0xdeadbeef), Data: []byte("data")}, true},
		{"walpb.Record (Data empty, not nil)", &walpb.Record{Type: i64(0), Data: []byte{}}, true},
		{"walpb.Snapshot{} (empty)", &walpb.Snapshot{}, true},
		{"walpb.Snapshot (populated)", &walpb.Snapshot{Index: u64(7), Term: u64(3), ConfState: cs}, true},
		{"raftpb.Entry{} (empty)", &raftpb.Entry{}, true},
		{"raftpb.Entry (populated)", &raftpb.Entry{Term: u64(1), Index: u64(5), Type: &et, Data: []byte("x")}, true},
		{"raftpb.HardState{} (empty)", &raftpb.HardState{}, true},
		{"raftpb.HardState (zero fields set)", &raftpb.HardState{Term: u64(0), Vote: u64(0), Commit: u64(0)}, true},
		{"raftpb.HardState (populated)", &raftpb.HardState{Term: u64(4), Vote: u64(1), Commit: u64(9)}, true},
		{"raftpb.Snapshot{} (empty)", &raftpb.Snapshot{}, true},
		{"raftpb.Snapshot (populated)", &raftpb.Snapshot{Data: []byte("snap"), Metadata: md}, true},
		{"raftpb.ConfState{} (empty)", &raftpb.ConfState{}, true},
		{"raftpb.ConfState (populated)", cs, true},
		{"raftpb.Message{} (empty)", &raftpb.Message{}, true},
		{"raftpb.Message (populated)", &raftpb.Message{Type: &mt, To: u64(2), From: u64(1), Term: u64(3),
			Entries: []*raftpb.Entry{{Term: u64(3), Index: u64(1)}}}, true},
		{"nil *walpb.Record", (*walpb.Record)(nil), false},
		{"nil *walpb.Snapshot", (*walpb.Snapshot)(nil), false},
		{"nil *raftpb.Entry", (*raftpb.Entry)(nil), false},
		{"nil *raftpb.HardState", (*raftpb.HardState)(nil), false},
		{"nil *raftpb.Snapshot", (*raftpb.Snapshot)(nil), false},
		{"nil *raftpb.ConfState", (*raftpb.ConfState)(nil), false},
		{"nil *raftpb.Message", (*raftpb.Message)(nil), false},
	}
	for _, c := range cases {
		d, err := proto.Marshal(c.m)
		t.Logf("%-38s d==nil=%-5v len=%-3d err=%v", c.name, d == nil, len(d), err)
		if c.valid && (d == nil || err != nil) {
			t.Errorf("%s: proto.Marshal returned d==nil=%v err=%v; the post claims a non-nil slice and nil",
				c.name, d == nil, err)
		}
	}
}
