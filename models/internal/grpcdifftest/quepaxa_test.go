package grpcdifftest_test

import (
	"context"
	"net"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"

	"models.lab/internal/grpcdifftest/quepaxa"
)

// consensus answers QuePaxa's three methods.
type consensus struct {
	quepaxa.UnimplementedConsensusServer
}

func (consensus) ESP(ctx context.Context, m *quepaxa.ProposerMessage) (*quepaxa.RecorderResponse, error) {
	return &quepaxa.RecorderResponse{S: m.S + 1, ClientBatchesNotFound: m.Sender == 2}, nil
}

func (consensus) FetchBatches(ctx context.Context, r *quepaxa.DecideRequest) (*quepaxa.DecideResponse, error) {
	var bs []*quepaxa.DecideResponse_ClientBatch
	for _, id := range r.Ids {
		bs = append(bs, &quepaxa.DecideResponse_ClientBatch{Id: id})
	}
	return &quepaxa.DecideResponse{ClientBatches: bs}, nil
}

// TestQuePaxa: QuePaxa's generated service (the kit quepaxa-net-2's use of gRPC), served and
// called as the kit does (NewServer, the generated registration, NewClient with insecure
// credentials, the three unary methods; InformDecision unimplemented by this server).
func TestQuePaxa(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	quepaxa.RegisterConsensusServer(s, consensus{})
	go s.Serve(l)
	defer s.Stop()
	cc, err := grpc.NewClient(l.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer cc.Close()
	c := quepaxa.NewConsensusClient(cc)
	r, err := c.ESP(ctx5(t), &quepaxa.ProposerMessage{Sender: 2, Index: 7, S: 4,
		P: &quepaxa.ProposerMessage_Proposal{}, DecidedSlots: []*quepaxa.ProposerMessage_DecidedSlot{{}}})
	if err != nil || r.S != 5 || !r.ClientBatchesNotFound {
		t.Fatal(r, err)
	}
	d, err := c.FetchBatches(ctx5(t), &quepaxa.DecideRequest{Ids: []string{"a", "b"}})
	if err != nil || len(d.ClientBatches) != 2 || d.ClientBatches[1].Id != "b" {
		t.Fatal(d, err)
	}
	_, err = c.InformDecision(ctx5(t), &quepaxa.Decisions{})
	wantStatus(t, err, codes.Unimplemented, "method InformDecision not implemented")
}
