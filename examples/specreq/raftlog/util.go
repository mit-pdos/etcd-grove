//go:build ignore

// Requirement snippets for raft's log (batch R3): util.go's helpers.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftlog/limit-size: a size-limited prefix of a non-empty list is non-empty (storage reads
// and log slices always make progress).
// Users: storage.go:161 (MemoryStorage.Entries), log.go (slice).
// Specs: limitSize.spec.
func ReqLimitSize(ents []*pb.Entry, maxSize uint64) {
	got := limitSize(ents, entryEncodingSize(maxSize))
	if len(ents) > 0 && len(got) == 0 {
		panic("limit-size: empty prefix")
	}
	if len(got) > len(ents) {
		panic("limit-size: longer than the input")
	}
}

// REQ raftlog/vote-resp: the response type of a vote or pre-vote.
// Users: raft.go:1077,1270,1279.
// Specs: voteRespMsgType.spec.
func ReqVoteResp() {
	if voteRespMsgType(pb.MsgVote) != pb.MsgVoteResp || voteRespMsgType(pb.MsgPreVote) != pb.MsgPreVoteResp {
		panic("vote-resp: wrong type")
	}
}

// REQ raftlog/payload-sizes: payload sizes are the data lengths (an empty entry is 0), summed.
// Users: raft.go:659,984-990,1227,2100 (flow control, the uncommitted budget).
// Specs: payloadSize.spec, payloadsSize.spec.
func ReqPayloadSizes(ents []*pb.Entry) {
	var sum entryPayloadSize
	for _, e := range ents {
		if payloadSize(e) != entryPayloadSize(len(e.GetData())) {
			panic("payload: wrong size")
		}
		sum += payloadSize(e)
	}
	if payloadsSize(ents) != sum {
		panic("payloads: wrong sum")
	}
}

// REQ raftlog/conf-states-equivalent: two listings of the same configuration (in any order) pass
// the assertion.
// Users: raft.go:479 (newRaft), raft.go:787 (appliedSnap).
// Assumes: cs1, cs2 list the same sets of ids and the same auto-leave flag.
// Specs: assertConfStatesEquivalent.spec.
func ReqConfStatesEquivalent(lg Logger, cs1, cs2 *pb.ConfState) {
	assertConfStatesEquivalent(lg, cs1, cs2)
}
