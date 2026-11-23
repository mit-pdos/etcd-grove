package raxos

import (
	"context"
	"errors"
	"sync"
	"testing"

	"google.golang.org/grpc"
	"raxos/proto/client"
)

// batchesFailRecorder is a ConsensusClient that calls a Recorder in process and fails, with an
// error, its first `fail` ESP calls that carry client batches (server mode 1's second call of
// step 4), as a gRPC call fails when its connection breaks or its context expires.
type batchesFailRecorder struct {
	mu   sync.Mutex
	fail int
	rec  *Recorder
}

func (f *batchesFailRecorder) ESP(ctx context.Context, in *ProposerMessage, opts ...grpc.CallOption) (*RecorderResponse, error) {
	f.mu.Lock()
	if f.fail > 0 && len(in.P.ClientBatches) > 0 {
		f.fail--
		f.mu.Unlock()
		return nil, errors.New("unavailable")
	}
	f.mu.Unlock()
	return f.rec.HandleESP(in), nil
}

func (f *batchesFailRecorder) FetchBatches(ctx context.Context, in *DecideRequest, opts ...grpc.CallOption) (*DecideResponse, error) {
	return f.rec.HandleFetch(in), nil
}

func (f *batchesFailRecorder) InformDecision(ctx context.Context, in *Decisions, opts ...grpc.CallOption) (*Empty, error) {
	f.rec.HandleDecisions(in)
	return &Empty{}, nil
}

// TestQ3ServerMode1MajorityOfFailedCalls (finding Q3): in server mode 1, step 4 sends the batch
// ids only, and the batches in a second call to a recorder that lacks them. A step whose second
// calls fail at a majority of the recorders must not end the proposer (QuePaxa's proposer waits
// for a majority of replies at each step); it tries the step again, and decides once the
// recorders answer.
func TestQ3ServerMode1MajorityOfFailedCalls(t *testing.T) {
	var peers []peer
	for i := int64(1); i <= 3; i++ {
		rec := NewRecorder(testConfig(), &ClientBatchStore{}, make(chan Decision, 100), i, false, 0)
		fail := 0
		if i != 1 {
			fail = 1 // the call with the batches to recorders 2 and 3 fails once: one reply, no majority
		}
		peers = append(peers, peer{name: i, client: &batchesFailRecorder{fail: fail, rec: rec}})
	}
	prop := NewProposer(1, 0, peers, nil, nil, nil, nil, false, 0, 100000, 1, nil, false, 0, 0)
	b := client.ClientBatch{Sender: 21, Id: "21.0.0", Messages: []*client.ClientBatch_SingleMessage{{Message: "1key00000"}}}
	done := make(chan ProposeResponse, 1)
	go func() {
		done <- prop.handleProposeRequest(ProposeRequest{instance: 1, proposalStr: []string{b.Id},
			proposalBtch: []client.ClientBatch{b}, isLeader: true})
	}()
	r := <-done
	if r.index != 1 || len(r.decisions) != 1 || r.decisions[0] != b.Id {
		t.Fatalf("decided %v", r)
	}
}
