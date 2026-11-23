package raxos

import (
	"testing"

	"raxos/proto/client"
)

func testProxy(name int64) *Proxy {
	cfg := testConfig()
	return NewProxy(name, cfg, make(chan ProposeRequest, 100), make(chan ProposeResponse, 100),
		make(chan Decision, 100), "/tmp/", 50, 1, 20000, false, 0, nil, 1, &ClientBatchStore{}, 0,
		make(chan FetchRequest, 100), make(chan FetchResposne, 100), 0, 5, make(chan Decision, 100),
		0, 8, 8, 0)
}

func put(id, key, val string) client.ClientBatch {
	return client.ClientBatch{Sender: 21, Id: id,
		Messages: []*client.ClientBatch_SingleMessage{{Message: "0" + key + val}}}
}

// TestQ2BatchDecidedTwiceExecutedOnce (finding Q2): a client batch decided in two slots (a replica
// that had not learned the first decision proposed it again) takes effect once: the replicated
// key-value store executes each client request at most once, and answers it once.
func TestQ2BatchDecidedTwiceExecutedOnce(t *testing.T) {
	pr := testProxy(2)
	a := put("21.0.0", "key00000", "v1")
	b := put("21.1.0", "key00000", "v2")
	pr.clientBatchStore.Add(a)
	pr.clientBatchStore.Add(b)
	// slots 1 and 3 decided a's batch, slot 2 b's (decisions learned from the recorder)
	pr.handleRecorderResponse(Decision{indexes: []int{1, 2}, decisions: [][]string{{a.Id}, {b.Id}},
		proposers: []int32{1, 1}})
	// slot 3 decided by this replica's proposer: it answers the clients of the slots it executes
	pr.replicatedLog = append(pr.replicatedLog, Slot{})
	pr.handleProposeResponse(ProposeResponse{index: 3, decisions: []string{a.Id}, proposer: 2, s: 4})
	if v := pr.benchmark.KVStore["key00000"]; v != "v2" {
		t.Fatalf("key00000 = %q after put v1 (slot 1), put v2 (slot 2): request %s executed twice", v, a.Id)
	}
	for len(pr.outgoingMessageChan) > 0 {
		m := <-pr.outgoingMessageChan
		if m.RpcPair.Obj.(*client.ClientBatch).Id == a.Id {
			t.Fatalf("request %s answered again at its second slot", a.Id)
		}
	}
}
