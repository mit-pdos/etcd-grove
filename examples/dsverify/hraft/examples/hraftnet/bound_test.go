package hraftnet

import (
	"math/rand"
	"testing"

	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/hraftnet/rpctransport"
)

// TestBounds: rpctransport's wire-size bounds (*ReqBound, the size check before a request is
// sent) are at least the length of the generated encoder's encoding (rpcEncode, rpc_gen.go) of
// random requests, values and pointers.

func bndBytes(r *rand.Rand) []byte {
	switch r.Intn(4) {
	case 0:
		return nil
	case 1:
		return []byte{}
	}
	b := make([]byte, r.Intn(200))
	r.Read(b)
	return b
}

func bndU64(r *rand.Rand) uint64 {
	if r.Intn(3) == 0 {
		return 0
	}
	return r.Uint64()
}

func bndHdr(r *rand.Rand) rpctransport.Header {
	return rpctransport.Header{ProtocolVersion: raft.ProtocolVersion(r.Intn(5)), ID: bndBytes(r),
		Addr: bndBytes(r)}
}

func bndCheck(t *testing.T, name string, bound uint64, v any, p any) {
	t.Helper()
	for _, x := range []any{v, p} {
		if n := uint64(len(rpcEncode(x))); n > bound {
			t.Fatalf("%s: encoding of %d bytes above the bound %d: %#v", name, n, bound, x)
		}
	}
}

func TestBounds(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for i := 0; i < 3000; i++ {
		var es []rpctransport.Entry
		if r.Intn(4) != 0 {
			es = []rpctransport.Entry{}
		}
		for k := r.Intn(40); k > 0; k-- {
			es = append(es, rpctransport.Entry{Index: bndU64(r), Term: bndU64(r),
				Type: raft.LogType(r.Intn(6)), Data: bndBytes(r), Extensions: bndBytes(r)})
		}
		a := rpctransport.AppendReq{Hdr: bndHdr(r), Term: bndU64(r), Leader: bndBytes(r),
			PrevLogEntry: bndU64(r), PrevLogTerm: bndU64(r), Entries: es, LeaderCommitIndex: bndU64(r)}
		bndCheck(t, "AppendReq", rpctransport.AppendReqBound(&a), a, &a)
		v := rpctransport.VoteReq{Hdr: bndHdr(r), Term: bndU64(r), Candidate: bndBytes(r),
			LastLogIndex: bndU64(r), LastLogTerm: bndU64(r), LeadershipTransfer: r.Intn(2) == 0}
		bndCheck(t, "VoteReq", rpctransport.VoteReqBound(&v), v, &v)
		pv := rpctransport.PreVoteReq{Hdr: bndHdr(r), Term: bndU64(r), LastLogIndex: bndU64(r),
			LastLogTerm: bndU64(r)}
		bndCheck(t, "PreVoteReq", rpctransport.PreVoteReqBound(&pv), pv, &pv)
		s := rpctransport.SnapReq{Hdr: bndHdr(r), SnapshotVersion: raft.SnapshotVersion(r.Intn(3)),
			Term: bndU64(r), Leader: bndBytes(r), LastLogIndex: bndU64(r), LastLogTerm: bndU64(r),
			Peers: bndBytes(r), Configuration: bndBytes(r), ConfigurationIndex: bndU64(r),
			Size: int64(bndU64(r)), Data: bndBytes(r)}
		bndCheck(t, "SnapReq", rpctransport.SnapReqBound(&s), s, &s)
		tn := rpctransport.TimeoutReq{Hdr: bndHdr(r)}
		bndCheck(t, "TimeoutReq", rpctransport.TimeoutReqBound(&tn), tn, &tn)
	}
}
