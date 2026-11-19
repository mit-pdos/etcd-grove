package pbschema

// Hm1, option (A) (decided by etcd-grove-03, 2026-11-19): `proto.CloneConfState.spec`'s third conjunct,
// `csPts p dq c true` in, `csPts p dq c true ∗ csPts p' 1 c true` out: the clone of a `*pb.ConfState`
// whose `AutoLeave` pointer is set has its `AutoLeave` pointer set (proto3 `optional`: presence is the
// pointer being non-nil), to the same value. What the test checks, for conf states with `AutoLeave`
// nil, set to false and set to true, and voter/learner lists empty, nil or not:
//
//   - the clone's `AutoLeave` is non-nil exactly when the source's is, and then holds the same value
//     (in particular a set `false` stays set: presence, not the value, decides);
//   - the clone's `AutoLeave` cell is not the source's (a fresh cell: storing through it leaves the
//     source's unchanged), and nor are its slices' arrays;
//   - the clone's four id lists equal the source's and it has no unknown fields (as the source);
//   - the source is unchanged by the clone.
//
// Against protobuf-go at examples/go.mod's pin and the raft fork's raftpb.

import (
	"math/rand"
	"reflect"
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

func randIDs(r *rand.Rand) []uint64 {
	switch r.Intn(4) {
	case 0:
		return nil
	case 1:
		return []uint64{}
	}
	n := 1 + r.Intn(7)
	s := make([]uint64, n)
	for i := range s {
		s[i] = r.Uint64() >> uint(r.Intn(64))
	}
	return s
}

// norm reads a list as the model does (nil and empty are the same list).
func norm(s []uint64) []uint64 {
	if len(s) == 0 {
		return []uint64{}
	}
	return append([]uint64{}, s...)
}

type csShow struct {
	V, L, O, N []uint64
	AL         *bool
	UF         int
}

func showCS(c *pb.ConfState) csShow {
	var al *bool
	if c.AutoLeave != nil {
		v := *c.AutoLeave
		al = &v
	}
	return csShow{norm(c.Voters), norm(c.Learners), norm(c.VotersOutgoing), norm(c.LearnersNext), al,
		len(c.ProtoReflect().GetUnknown())}
}

func TestCloneConfStateAutoLeave(t *testing.T) {
	r := rand.New(rand.NewSource(1119))
	counts := map[string]int{}
	for it := 0; it < 30000; it++ {
		c := &pb.ConfState{
			Voters: randIDs(r), Learners: randIDs(r), VotersOutgoing: randIDs(r), LearnersNext: randIDs(r),
		}
		kind := "nil"
		switch it % 3 {
		case 1:
			c.AutoLeave = proto.Bool(false)
			kind = "false"
		case 2:
			c.AutoLeave = proto.Bool(true)
			kind = "true"
		}
		before := showCS(c)
		c2 := proto.Clone(c).(*pb.ConfState)
		if !reflect.DeepEqual(showCS(c), before) {
			t.Fatalf("Clone changed its source: %+v became %+v", before, showCS(c))
		}
		got := showCS(c2)
		if (c.AutoLeave == nil) != (c2.AutoLeave == nil) {
			t.Fatalf("AutoLeave %s: clone's pointer set = %v, source's = %v", kind, c2.AutoLeave != nil, c.AutoLeave != nil)
		}
		if c.AutoLeave != nil {
			if *c2.AutoLeave != *c.AutoLeave {
				t.Fatalf("AutoLeave %s: clone holds %v", kind, *c2.AutoLeave)
			}
			if c2.AutoLeave == c.AutoLeave {
				t.Fatalf("AutoLeave %s: the clone shares the source's cell", kind)
			}
		}
		if got.UF != 0 {
			t.Fatalf("clone has %d bytes of unknown fields", got.UF)
		}
		if !reflect.DeepEqual(got, before) {
			t.Fatalf("Clone: content %+v, want %+v", got, before)
		}
		// Freshness: store into every field of the clone, in place.
		if c2.AutoLeave != nil {
			*c2.AutoLeave = !*c2.AutoLeave
		}
		for _, s := range [][]uint64{c2.Voters, c2.Learners, c2.VotersOutgoing, c2.LearnersNext} {
			for i := range s {
				s[i] ^= 0xffff
			}
		}
		if !reflect.DeepEqual(showCS(c), before) {
			t.Fatalf("Clone shares with its source: %+v became %+v", before, showCS(c))
		}
		counts[kind]++
	}
	t.Logf("conf states cloned, by AutoLeave: %v; presence and value kept, cells and arrays fresh", counts)
}
