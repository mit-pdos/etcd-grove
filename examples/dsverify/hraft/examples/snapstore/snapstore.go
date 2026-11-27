// Package snapstore: an in-memory raft.SnapshotStore with upstream's FileSnapshotStore's semantics for one retained
// snapshot: a snapshot becomes visible (List, Open) only when its sink is closed, Cancel discards it, and a newer
// closed snapshot replaces the older one. Open returns a reader over a copy of the snapshot's bytes. (raft's own
// InmemSnapshotStore, a test helper, makes a snapshot the latest as it is created, before it is written.)
package snapstore

import (
	"errors"
	"io"
	"strconv"
	"sync"

	"github.com/hashicorp/raft"
)

var ErrNoSnapshot = errors.New("snapstore: no such snapshot")
var ErrClosed = errors.New("snapstore: sink closed")

type Store struct {
	mu     *sync.Mutex
	has    bool
	meta   raft.SnapshotMeta // the latest closed snapshot's
	data   []byte
	nextID uint64
}

func New() *Store {
	return &Store{mu: new(sync.Mutex)}
}

type Sink struct {
	st     *Store
	meta   raft.SnapshotMeta
	data   []byte
	closed bool
}

// Create: a sink for a snapshot of the log up to index (in term); visible once closed
func (s *Store) Create(version raft.SnapshotVersion, index, term uint64, configuration raft.Configuration,
	configurationIndex uint64, trans raft.Transport) (raft.SnapshotSink, error) {
	s.mu.Lock()
	s.nextID++
	id := strconv.Itoa(int(term)) + "-" + strconv.Itoa(int(index)) + "-" + strconv.Itoa(int(s.nextID))
	s.mu.Unlock()
	return &Sink{st: s, meta: raft.SnapshotMeta{Version: version, ID: id, Index: index, Term: term,
		Configuration: configuration, ConfigurationIndex: configurationIndex}}, nil
}

// List: the latest closed snapshot, if any
func (s *Store) List() ([]*raft.SnapshotMeta, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.has {
		return []*raft.SnapshotMeta{}, nil
	}
	m := s.meta
	return []*raft.SnapshotMeta{&m}, nil
}

// Open: the snapshot id, if it is still the latest
func (s *Store) Open(id string) (*raft.SnapshotMeta, io.ReadCloser, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.has || s.meta.ID != id {
		return nil, nil, ErrNoSnapshot
	}
	m := s.meta
	return &m, NewReader(s.data), nil
}

// Latest: the index of the latest closed snapshot (0 when there is none)
func (s *Store) Latest() uint64 {
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.has {
		return 0
	}
	return s.meta.Index
}

func (k *Sink) Write(p []byte) (int, error) {
	if k.closed {
		return 0, ErrClosed
	}
	k.data = append(k.data, p...)
	return len(p), nil
}

// Close: the snapshot becomes the store's latest unless the store has a newer one (FileSnapshotStore's order:
// by term, then index), which it keeps. Idempotent, as FileSnapshotSink's (an FSMSnapshot's Persist closes the
// sink, and raft closes it again)
func (k *Sink) Close() error {
	if k.closed {
		return nil
	}
	k.closed = true
	k.meta.Size = int64(len(k.data))
	s := k.st
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.has || k.meta.Term > s.meta.Term || (k.meta.Term == s.meta.Term && k.meta.Index >= s.meta.Index) {
		s.has = true
		s.meta = k.meta
		s.data = k.data
	}
	return nil
}

func (k *Sink) ID() string {
	return k.meta.ID
}

// Cancel: the snapshot is dropped (nothing once the sink is closed: idempotent, as FileSnapshotSink's)
func (k *Sink) Cancel() error {
	k.closed = true
	return nil
}
