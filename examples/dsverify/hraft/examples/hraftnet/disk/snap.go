package disk

import (
	"errors"
	"io"
	"strconv"
	"sync"

	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/snapstore"
	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
)

// Snaps is a raft.SnapshotStore with upstream's FileSnapshotStore's semantics for one retained
// snapshot, as examples/snapstore's, written to file: a snapshot becomes the latest (List, Open)
// when its sink is closed, and Close returns once it is durable in dir/snap (with the store's
// next snapshot ID, so that an ID is not reused across restarts); Cancel discards it; a newer
// closed snapshot replaces the older one. Open returns a reader over a copy of its bytes.
type Snaps struct {
	mu     *sync.Mutex
	file   string
	has    bool
	meta   raft.SnapshotMeta // the latest closed snapshot's (Peers not kept: raft no longer sets it)
	data   []byte
	nextID uint64
}

// ErrNoSnapshot is Open's error for a snapshot that is not the latest.
var ErrNoSnapshot = errors.New("disk: no such snapshot")

// ErrClosed is a closed sink's Write error.
var ErrClosed = errors.New("disk: sink closed")

func snapFile(dir string) string { return dir + "/snap" }

// FreshSnaps is an empty snapshot store in dir, written to dir/snap.
func FreshSnaps(dir string) *Snaps {
	s := &Snaps{mu: new(sync.Mutex), file: snapFile(dir)}
	s.persist()
	return s
}

// OpenSnaps is the snapshot store dir/snap holds, or an error if it is missing or does not decode.
func OpenSnaps(dir string) (*Snaps, error) {
	str, ok := durable.Read(snapFile(dir))
	if !ok {
		return nil, ErrMissing
	}
	s := &Snaps{mu: new(sync.Mutex), file: snapFile(dir)}
	if err := s.decode([]byte(str)); err != nil {
		return nil, err
	}
	return s, nil
}

func encodeConfiguration(b []byte, c raft.Configuration) []byte {
	b = putUint64(b, uint64(len(c.Servers)))
	for i := 0; i < len(c.Servers); i++ {
		b = putUint64(b, uint64(c.Servers[i].Suffrage))
		b = putBytes(b, []byte(c.Servers[i].ID))
		b = putBytes(b, []byte(c.Servers[i].Address))
	}
	return b
}

func decodeConfiguration(r *reader) raft.Configuration {
	var c raft.Configuration
	n := r.uint64()
	for i := uint64(0); i < n && !r.err; i++ {
		var s raft.Server
		s.Suffrage = raft.ServerSuffrage(r.uint64())
		s.ID = raft.ServerID(r.bytes())
		s.Address = raft.ServerAddress(r.bytes())
		c.Servers = append(c.Servers, s)
	}
	return c
}

// encode is the store's file contents: the next ID, then whether there is a snapshot and, if so,
// its metadata and bytes.
func (s *Snaps) encode() []byte {
	b := putUint64(nil, s.nextID)
	if !s.has {
		return putUint64(b, 0)
	}
	b = putUint64(b, 1)
	m := &s.meta
	b = putUint64(b, uint64(m.Version))
	b = putBytes(b, []byte(m.ID))
	b = putUint64(b, m.Index)
	b = putUint64(b, m.Term)
	b = encodeConfiguration(b, m.Configuration)
	b = putUint64(b, m.ConfigurationIndex)
	return putBytes(b, s.data)
}

func (s *Snaps) decode(b []byte) error {
	r := &reader{b: b}
	s.nextID = r.uint64()
	if r.uint64() == 1 {
		s.has = true
		s.meta.Version = raft.SnapshotVersion(r.uint64())
		s.meta.ID = string(r.bytes())
		s.meta.Index = r.uint64()
		s.meta.Term = r.uint64()
		s.meta.Configuration = decodeConfiguration(r)
		s.meta.ConfigurationIndex = r.uint64()
		s.data = r.bytes()
		s.meta.Size = int64(len(s.data))
	}
	return r.done()
}

func (s *Snaps) persist() {
	durable.Write(s.file, string(s.encode()))
}

// Sink is a snapshot being written.
type Sink struct {
	st     *Snaps
	meta   raft.SnapshotMeta
	data   []byte
	closed bool
}

// Create is a sink for a snapshot of the log up to index (in term); the latest once closed.
func (s *Snaps) Create(version raft.SnapshotVersion, index, term uint64, configuration raft.Configuration,
	configurationIndex uint64, trans raft.Transport) (raft.SnapshotSink, error) {
	s.mu.Lock()
	s.nextID++
	id := strconv.Itoa(int(term)) + "-" + strconv.Itoa(int(index)) + "-" + strconv.Itoa(int(s.nextID))
	s.mu.Unlock()
	return &Sink{st: s, meta: raft.SnapshotMeta{Version: version, ID: id, Index: index, Term: term,
		Configuration: configuration, ConfigurationIndex: configurationIndex}}, nil
}

// List is the latest closed snapshot, if any.
func (s *Snaps) List() ([]*raft.SnapshotMeta, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.has {
		return []*raft.SnapshotMeta{}, nil
	}
	m := s.meta
	return []*raft.SnapshotMeta{&m}, nil
}

// Open is the snapshot id, if it is still the latest.
func (s *Snaps) Open(id string) (*raft.SnapshotMeta, io.ReadCloser, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.has || s.meta.ID != id {
		return nil, nil, ErrNoSnapshot
	}
	m := s.meta
	return &m, snapstore.NewReader(s.data), nil
}

// Write appends p to the snapshot.
func (k *Sink) Write(p []byte) (int, error) {
	if k.closed {
		return 0, ErrClosed
	}
	k.data = append(k.data, p...)
	return len(p), nil
}

// Close makes the snapshot the store's latest, durably, unless the store has a newer one
// (FileSnapshotStore's order: by term, then index), which it keeps. Idempotent, as
// FileSnapshotSink's (an FSMSnapshot's Persist closes the sink, and raft closes it again).
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
		s.persist()
	}
	return nil
}

// ID is the snapshot's ID.
func (k *Sink) ID() string {
	return k.meta.ID
}

// Cancel drops the snapshot (nothing once the sink is closed).
func (k *Sink) Cancel() error {
	k.closed = true
	return nil
}
