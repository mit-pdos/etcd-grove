// Package arith is the grpc difftest's service: pb's Arith (Add, Div) with counters and gates, so
// the tests can observe how often a handler ran and hold a handler while the caller gives up.
package arith

import (
	"context"
	"errors"
	"sync"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"dsverify.lab/grpcdifftest/pb"
)

// Server implements pb.ArithServer. Div's behavior depends on the arguments:
//   - B == 0: a status error InvalidArgument "division by zero";
//   - Op == SUB and Tag == "plain": a plain error "plain failure" (Unknown at the client);
//   - Tag == "deadline": the error context.DeadlineExceeded (DeadlineExceeded at the client);
//   - Tag == "typednil": a nil *Reply and a nil error (the generated handler returns it as a
//     non-nil interface: an empty reply at the client);
//   - Tag == "big": a reply of more than 4 MiB (ResourceExhausted at the client);
//   - Tag == "wait": waits until Release(Id) or its context is done, recording which;
//   - else A / B, echoing the arguments.
type Server struct {
	pb.UnimplementedArithServer
	mu      sync.Mutex
	runs    map[uint64]int // runs per Id (Add and Div)
	gates   map[uint64]chan struct{}
	ctxDone map[uint64]bool // a "wait" call ended by its context
}

// New returns a fresh server.
func New() *Server {
	return &Server{runs: make(map[uint64]int), gates: make(map[uint64]chan struct{}),
		ctxDone: make(map[uint64]bool)}
}

func (s *Server) count(id uint64) {
	s.mu.Lock()
	s.runs[id]++
	s.mu.Unlock()
}

// Runs returns how many times a handler ran for id.
func (s *Server) Runs(id uint64) int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.runs[id]
}

// CtxDone reports whether the "wait" call id ended because its context was done.
func (s *Server) CtxDone(id uint64) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.ctxDone[id]
}

func (s *Server) gate(id uint64) chan struct{} {
	s.mu.Lock()
	defer s.mu.Unlock()
	g, ok := s.gates[id]
	if !ok {
		g = make(chan struct{})
		s.gates[id] = g
	}
	return g
}

// Release lets the "wait" call id return.
func (s *Server) Release(id uint64) {
	close(s.gate(id))
}

// Add returns A + B (and echoes the arguments).
func (s *Server) Add(ctx context.Context, a *pb.Args) (*pb.Reply, error) {
	s.count(a.Id)
	return &pb.Reply{C: a.A + a.B, Echo: a}, nil
}

// Div: see the type's doc.
func (s *Server) Div(ctx context.Context, a *pb.Args) (*pb.Reply, error) {
	s.count(a.Id)
	switch {
	case a.Tag == "plain":
		return nil, errors.New("plain failure")
	case a.Tag == "deadline":
		return nil, context.DeadlineExceeded
	case a.Tag == "typednil":
		return nil, nil
	case a.Tag == "big":
		return &pb.Reply{Echo: &pb.Args{Blob: make([]byte, 4*1024*1024+1)}}, nil
	case a.Tag == "wait":
		select {
		case <-s.gate(a.Id):
		case <-ctx.Done():
			s.mu.Lock()
			s.ctxDone[a.Id] = true
			s.mu.Unlock()
			return nil, ctx.Err()
		}
	}
	if a.B == 0 {
		return nil, status.Error(codes.InvalidArgument, "division by zero")
	}
	return &pb.Reply{C: a.A / a.B, Echo: a}, nil
}
