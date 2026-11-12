package pbschema

// out_size C3 (decided by etcd-grove-81, option (a)): `pbEntryC`'s decoded object (`decC`) is owned,
// `entPtsCC l (DFrac.own 1) c`, as `pbMessageC`'s is. `proto.ClonePb` and `proto.UnmarshalPb` hand
// out `decC`, so at `Entry` (and inside a `Message`) they claim objects nothing else reaches:
//
//   - `proto.Unmarshal` (the default options, as `pbutil.MustUnmarshalMessage` calls it) copies
//     `bytes` fields and unknown fields out of its input buffer: overwriting the buffer afterwards
//     leaves the decoded content unchanged;
//   - `proto.Clone` returns an object sharing nothing with its source: storing into every field of
//     the clone (scalars, `Data`'s bytes in place, unknown fields) leaves the source unchanged, and
//     the clone held the source's content before the stores.
//
// Against protobuf-go at examples/go.mod's pin and the raft fork's raftpb.

import (
	"math/rand"
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

func scribble(bs []byte) {
	for i := range bs {
		bs[i] ^= 0xff
	}
}

// mutateEnt stores into every field of e, and into Data's and the unknown fields' bytes in place.
func mutateEnt(e *pb.Entry) {
	e.Term, e.Index = pu(0xdead), pu(0xbeef)
	t := pb.EntryConfChange
	e.Type = &t
	scribble(e.Data)
	scribble(e.ProtoReflect().GetUnknown())
}

func TestC3DecodedFresh(t *testing.T) {
	r := rand.New(rand.NewSource(31))
	adv := ufOpts{nonMinOuter: true, badNums: true, badEnds: true, takenOK: true, innerNumMax: 1<<31 - 1}
	nEnt, nMsg, nClone, withData := 0, 0, 0, 0
	for it := 0; it < 20000; it++ {
		var bs []byte
		if it%2 == 0 {
			bs = encodeWithUF(r, "Entry", 0, adv)
		} else {
			bs = genAdv(r, "Entry", 0)
		}
		var e pb.Entry
		if proto.Unmarshal(bs, &e) != nil {
			continue
		}
		nEnt++
		if len(e.Data) > 0 {
			withData++
		}
		before := contentOfEnt(&e).show()
		scribble(bs)
		if after := contentOfEnt(&e).show(); after != before {
			t.Fatalf("Unmarshal(Entry) aliases its input: %s became %s", before, after)
		}
		e2 := proto.Clone(&e).(*pb.Entry)
		if got := contentOfEnt(e2).show(); got != before {
			t.Fatalf("Clone(Entry): content %s, want %s", got, before)
		}
		mutateEnt(e2)
		if after := contentOfEnt(&e).show(); after != before {
			t.Fatalf("Clone(Entry) shares with its source: %s became %s", before, after)
		}
		nClone++
	}
	for it := 0; it < 20000; it++ {
		var bs []byte
		if it%2 == 0 {
			bs = encodeWithUF(r, "Message", 0, adv)
		} else {
			bs = genAdv(r, "Message", 0)
		}
		var m pb.Message
		if proto.Unmarshal(bs, &m) != nil {
			continue
		}
		nMsg++
		before := contentOfMsg(&m).show()
		scribble(bs)
		if after := contentOfMsg(&m).show(); after != before {
			t.Fatalf("Unmarshal(Message) aliases its input: %s became %s", before, after)
		}
		m2 := proto.Clone(&m).(*pb.Message)
		if got := contentOfMsg(m2).show(); got != before {
			t.Fatalf("Clone(Message): content %s, want %s", got, before)
		}
		for _, e := range m2.Entries {
			mutateEnt(e)
		}
		if after := contentOfMsg(&m).show(); after != before {
			t.Fatalf("Clone(Message)'s entries share with the source's: %s became %s", before, after)
		}
	}
	if nEnt < 1000 || withData < 100 || nMsg < 1000 {
		t.Fatalf("too few decoded inputs: %d entries (%d with data), %d messages", nEnt, withData, nMsg)
	}
	t.Logf("%d entries (%d with data, %d clones), %d messages: decoded objects and clones fresh", nEnt, withData, nClone, nMsg)
}
