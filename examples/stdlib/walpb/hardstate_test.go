package walpb

// Checks the Lean model of raftpb.HardState's wire format, hsEnc of
// Proof/go_etcd_io/etcd/server/v3/storage/wal/RaftModel/Codec.lean (the encoder of the registered
// instance pbHsC, Proof/go_etcd_io/etcd/server/v3/storage/wal/RaftModel/PbHardState.lean, whose trusted
// fact is hsEncC_ok), against protobuf-go (the version examples/go.mod selects) and raftpb at the
// raft fork's pin. hsEnc below transcribes the Lean definition one for one. For random wire contents
// (Term, Vote, Commit nil or set, zero included; unknown fields routed to the unknown fields at
// hsSchema) TestHardStateEncoder compares proto.Marshal with hsEnc, proto.Size with hsEnc's length,
// and proto.Unmarshal(hsEnc c) with c itself (presence, values, the unknown fields verbatim), the
// getters with WalHsC.model; TestHardStateSchema compares the descriptor with hsSchema.

import (
	"bytes"
	"math/rand"
	"testing"

	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// hsC is the Lean WalHsC.
type hsC struct {
	term, vote, commit *uint64
	uf                 []byte
}

// hsEnc is the Lean hsEnc.
func hsEnc(c hsC) []byte {
	var b []byte
	b = optVarint(b, 1, c.term)
	b = optVarint(b, 2, c.vote)
	b = optVarint(b, 3, c.commit)
	return append(b, c.uf...)
}

// hsSchema is the Lean hsSchema.
var hsSchema = map[protowire.Number][]protowire.Type{
	1: {protowire.VarintType},
	2: {protowire.VarintType},
	3: {protowire.VarintType},
}

func genOpt(r *rand.Rand) *uint64 {
	if r.Intn(4) == 0 {
		return nil
	}
	v := rval(r)
	return &v
}

func genHs(r *rand.Rand) hsC {
	c := hsC{term: genOpt(r), vote: genOpt(r), commit: genOpt(r)}
	if r.Intn(3) == 0 {
		c.uf = genUFAt(r, hsSchema)
	}
	return c
}

func hsToGo(c hsC) *raftpb.HardState {
	m := &raftpb.HardState{Term: c.term, Vote: c.vote, Commit: c.commit}
	if c.uf != nil {
		m.ProtoReflect().SetUnknown(protoreflect.RawFields(c.uf))
	}
	return m
}

func getD(p *uint64) uint64 {
	if p == nil {
		return 0
	}
	return *p
}

func TestHardStateEncoder(t *testing.T) {
	r := rand.New(rand.NewSource(3))
	for i := 0; i < 200000; i++ {
		c := genHs(r)
		want := hsEnc(c)
		m := hsToGo(c)
		if got := proto.Size(m); got != len(want) {
			t.Fatalf("proto.Size %d, hsEnc's length %d", got, len(want))
		}
		got, err := proto.Marshal(m)
		if err != nil || !bytes.Equal(got, want) {
			t.Fatalf("proto.Marshal %x (%v), hsEnc %x", got, err, want)
		}
		var d raftpb.HardState
		if err := proto.Unmarshal(want, &d); err != nil {
			t.Fatalf("Unmarshal(hsEnc) failed: %v", err)
		}
		if !sameOpt(d.Term, c.term) || !sameOpt(d.Vote, c.vote) || !sameOpt(d.Commit, c.commit) {
			t.Fatalf("Term/Vote/Commit differ, encoding %x", want)
		}
		if !bytes.Equal(d.ProtoReflect().GetUnknown(), c.uf) {
			t.Fatalf("unknown fields differ, encoding %x", want)
		}
		// WalHsC.model: what the getters read
		if d.GetTerm() != getD(c.term) || d.GetVote() != getD(c.vote) || d.GetCommit() != getD(c.commit) {
			t.Fatalf("getters differ from WalHsC.model, encoding %x", want)
		}
	}
}

func TestHardStateSchema(t *testing.T) {
	checkSchema(t, (&raftpb.HardState{}).ProtoReflect().Descriptor().Fields(), hsSchema)
}
