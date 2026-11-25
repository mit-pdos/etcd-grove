// Package service is rpcdriver's service: its one method, Echo, and the types it carries (a
// package of its own, so that the codec rpcgen generates for package rpcdriver can name them).
package service

import (
	"errors"
	"sync"
)

// Args is a request: a unique id (the client's call counter), a payload, and the error the
// method should answer with ("" for none).
type Args struct {
	ID   uint64
	Data []byte
	Fail string
}

// Reply is the method's answer: the request's id and payload, and how many times the method has
// run on that id (counting this run).
type Reply struct {
	ID   uint64
	Data []byte
	Runs uint64
}

// Svc is the service the server registers.
type Svc struct {
	mu   sync.Mutex
	runs map[uint64]uint64
}

// Echo answers its request: the id, the payload, the number of runs on this id; and the request's
// error, if it asks for one.
func (s *Svc) Echo(a *Args, r *Reply) error {
	s.mu.Lock()
	s.runs[a.ID] = s.runs[a.ID] + 1
	n := s.runs[a.ID]
	s.mu.Unlock()
	r.ID = a.ID
	r.Data = a.Data
	r.Runs = n
	if a.Fail != "" {
		return errors.New(a.Fail)
	}
	return nil
}

// NoMethods is a type with no method net/rpc can serve.
type NoMethods struct{}

// New is a service that has run no request.
func New() *Svc {
	return &Svc{runs: make(map[uint64]uint64)}
}
