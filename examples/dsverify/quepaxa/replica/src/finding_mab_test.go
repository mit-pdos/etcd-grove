package raxos

import (
	"testing"

	"raxos/proto/client"
)

// mabProxy is replica `name` of the 3 replicas of testConfig in leader mode 2 (the multi-armed
// bandit) with epochs of `epoch` slots and a pipeline of `pipeline` slots.
func mabProxy(name int64, epoch int, pipeline int64) *Proxy {
	return NewProxy(name, testConfig(), make(chan ProposeRequest, 100), make(chan ProposeResponse, 100),
		make(chan Decision, 100), "/tmp/", 50, pipeline, 20000, false, 0, nil, 2, &ClientBatchStore{}, 0,
		make(chan FetchRequest, 100), make(chan FetchResposne, 100), 0, epoch, make(chan Decision, 100),
		0, 8, 8, 0)
}

// learn makes pr learn, from its recorder, the decisions of slots from..to, each a client batch
// of its own (in its store).
func learn(pr *Proxy, from, to int) {
	d := Decision{}
	for i := from; i <= to; i++ {
		b := put("21.9."+string(rune('a'+i)), "key00000", "v")
		pr.clientBatchStore.Add(b)
		d.indexes = append(d.indexes, i)
		d.decisions = append(d.decisions, []string{b.Id})
		d.proposers = append(d.proposers, 1)
	}
	pr.handleRecorderResponse(d)
}

// lastProposal is the proposal pr last sent to its proposers.
func lastProposal(t *testing.T, pr *Proxy) ProposeRequest {
	var r ProposeRequest
	n := 0
	for len(pr.proxyToProposerChan) > 0 {
		r = <-pr.proxyToProposerChan
		n++
	}
	if n == 0 {
		t.Fatalf("no proposal sent")
	}
	return r
}

// TestQ5FirstSummaryWithEpochsOfOneSlot (finding Q5): with epochs of 1 slot, a replica proposing
// the first epoch summary (slot 2N) has measured no epoch (epoch 0 is the genesis alone and is
// never started), so every replica's average epoch time is over no measurement. The summary
// orders the replicas by their averages; it must be proposed, not end the replica.
func TestQ5FirstSummaryWithEpochsOfOneSlot(t *testing.T) {
	pr := mabProxy(1, 1, 1)
	learn(pr, 1, 5)
	pr.proposeToIndex(6) // epoch 6 = 2N: the first summary
	p := lastProposal(t, pr)
	if len(p.proposalStr) != 1 || len(p.proposalStr[0]) < 5 || p.proposalStr[0][:5] != "Epoch" {
		t.Fatalf("slot 6 proposed %v, not an epoch summary", p.proposalStr)
	}
}

// TestQ6LeaderOrderOfAnEpochWhoseSummaryIsUnknown (finding Q6): a replica with a pipeline
// proposes slots of an epoch after 2N, whose leader order is the summary decided in the previous
// epoch's first slot, before it has learned that slot. It must propose, not end; and since it does
// not know the epoch's order, it must not propose as the slot's leader (priority hi at step 4,
// QuePaxa's fast path): only the slot's one leader may, and the replicas that know the summary
// may take another replica as the leader. Replica 2 would lead slot 7 in the round-robin order.
func TestQ6LeaderOrderOfAnEpochWhoseSummaryIsUnknown(t *testing.T) {
	pr := mabProxy(2, 1, 2)
	learn(pr, 1, 5)
	pr.handleClientBatch(put("21.0.0", "key00000", "v1")) // slot 6 (epoch 6: round robin)
	pr.handleClientBatch(put("21.0.1", "key00000", "v2")) // slot 7: epoch 7's order is slot 6's summary
	if pr.lastProposedIndex != 7 {
		t.Fatalf("last proposed slot %d, want 7", pr.lastProposedIndex)
	}
	pr.proposeToIndex(7) // slot 7's timer fired
	if p := lastProposal(t, pr); p.instance != 7 || p.isLeader {
		t.Fatalf("slot 7 proposed as its leader (%v) by a replica that does not know epoch 7's leader order", p.isLeader)
	}
}

// TestQ6SummaryOverEpochsNotTracked (finding Q6): a replica proposing an epoch summary computes
// it from the epochs it saw end, stopping at the first one it did not see end; one that has not
// tracked every earlier epoch (with a pipeline, it may propose ahead of what it learned) must
// propose the summary of those it tracked, not end.
func TestQ6SummaryOverEpochsNotTracked(t *testing.T) {
	pr := mabProxy(1, 2, 5)
	learn(pr, 1, 9) // epochs 0..4 tracked, and each ended
	pr.proposeToIndex(12) // epoch 6 = 2N: a summary over epochs 0..5
	p := lastProposal(t, pr)
	if len(p.proposalStr) != 1 || p.proposalStr[0][:5] != "Epoch" {
		t.Fatalf("slot 12 proposed %v, not an epoch summary", p.proposalStr)
	}
}

// TestQ7LostSummaryNotProposedAsClientBatch (finding Q7): a replica that proposed an epoch
// summary in an epoch's first slot, where another replica's summary was decided, puts back
// only client batches into the batches to propose: a summary is not a client batch (it is not in
// the client batch store unless this replica's recorder received it). Its next proposal must be
// of client batches, not end the replica.
func TestQ7LostSummaryNotProposedAsClientBatch(t *testing.T) {
	pr := mabProxy(1, 2, 5)
	learn(pr, 1, 11)      // epochs 0..5, all ended
	pr.proposeToIndex(12) // epoch 6's first slot: this replica's summary
	own := lastProposal(t, pr).proposalStr[0]
	other := "Epoch3,2,1"
	if own == other {
		other = "Epoch2,3,1"
	}
	// another replica's summary was decided in slot 12 (not in this replica's store)
	pr.handleRecorderResponse(Decision{indexes: []int{12}, decisions: [][]string{{other}}, proposers: []int32{2}})
	b := put("21.0.0", "key00000", "v1")
	pr.clientBatchStore.Add(b)
	pr.toBeProposed = append(pr.toBeProposed, b.Id)
	pr.proposeToIndex(13)
	p := lastProposal(t, pr)
	for _, id := range p.proposalStr {
		if id == own {
			t.Fatalf("slot 13 proposed the lost summary %s as a client batch", own)
		}
	}
	_ = client.ClientBatch{}
}
