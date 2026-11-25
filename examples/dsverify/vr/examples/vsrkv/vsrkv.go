// Package vsrkv is the replicated service of the vsr-net kit (added by the kit, not part of
// go-vsr): a key-value map driven by go-vsr's replica through replica.Config.SrvHandler, as in
// go-vsr's cmd/example server. An operation is "SET k v" or "GET k" (fields separated by single
// spaces); the reply is the value set, or the key's value ("" if the key has none). Any other
// operation changes nothing and gets "".
//
// It is part of the system the theorem is about: translated and proved like go-vsr's packages
// (not trusted).
package vsrkv

import "strings"

// Store is the map. Only the replica's event loop calls Handle (one goroutine).
type Store struct {
	m map[string]string
}

// New returns an empty store.
func New() *Store {
	return &Store{m: make(map[string]string)}
}

// Handle applies one operation and returns its reply.
func (s *Store) Handle(op string) string {
	f := strings.Split(op, " ")
	if len(f) == 3 && f[0] == "SET" {
		s.m[f[1]] = f[2]
		return f[2]
	}
	if len(f) == 2 && f[0] == "GET" {
		return s.m[f[1]]
	}
	return ""
}
