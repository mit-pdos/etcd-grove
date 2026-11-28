// Package disk is a hraft kit server's durable state (notes/dsv-hraft.md, "hraft_robust"): its
// raft log store, stable store and commit index (Disk), and its snapshot store (Snaps), each kept
// in memory and written whole, on every change, to a file of the server's data directory through
// examples/lib/durable: dir/raft (the log's entries, the stable store's keys and the written commit
// index, in one file, so that every change is one atomic write) and dir/snap (the latest snapshot).
// A crash leaves each file as its last durable.Write left it; Open reads them back.
//
// The stores are synchronous, as hashicorp/raft requires of a LogStore and a StableStore: a
// write is durable when it returns (durable.Write returns once its file is renamed and the
// directory synced). Reads are served from memory. Every operation returns a nil error but
// GetLog of a missing entry (raft.ErrLogNotFound) and Get of a missing key ("not found", the text
// raft compares with).
//
// The log store is also a raft.CommitTrackingLogStore (raft's RestoreCommittedLogs mode): a
// staged commit index is written with the next StoreLogs, in the same write, and GetCommitIndex
// returns the last one written, at most the last index in the log.
//
// An entry's AppendedAt (metadata raft does not look at) is not kept: GetLog returns it zero.
package disk

import (
	"errors"
	"sync"

	"github.com/hashicorp/raft"
	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
)

// ErrNotFound is Get's error for a missing key (raft compares its text with "not found").
var ErrNotFound = errors.New("not found")

// ErrMissing is Open's error when a file is missing.
var ErrMissing = errors.New("disk: missing file")

// Disk is the log store, the stable store and the commit index, written to file.
type Disk struct {
	mu     *sync.Mutex
	file   string
	ents   []raft.Log // the log store's entries, by increasing index (a partial map: raft compacts a prefix)
	keys   [][]byte   // the stable store's byte-slice keys
	vals   [][]byte
	ikeys  [][]byte // its uint64 keys
	ivals  []uint64
	staged uint64 // the commit index staged for the next StoreLogs (not durable)
	commit uint64 // the commit index written with the last StoreLogs
}

func copyBytes(b []byte) []byte {
	if b == nil {
		return nil
	}
	c := make([]byte, len(b))
	copy(c, b)
	return c
}

func bytesEq(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func raftFile(dir string) string { return dir + "/raft" }

// Fresh is an empty Disk in dir, written to dir/raft (whatever that file held before: an earlier
// first start's, which a crash interrupted before its marker).
func Fresh(dir string) *Disk {
	d := &Disk{mu: new(sync.Mutex), file: raftFile(dir)}
	d.persist()
	return d
}

// Open is the Disk dir/raft holds, or an error if it is missing or does not decode.
func Open(dir string) (*Disk, error) {
	s, ok := durable.Read(raftFile(dir))
	if !ok {
		return nil, ErrMissing
	}
	d := &Disk{mu: new(sync.Mutex), file: raftFile(dir)}
	if err := d.decode([]byte(s)); err != nil {
		return nil, err
	}
	return d, nil
}

// encode is the Disk's file contents.
func (d *Disk) encode() []byte {
	b := putUint64(nil, uint64(len(d.ents)))
	for i := 0; i < len(d.ents); i++ {
		e := &d.ents[i]
		b = putUint64(b, e.Index)
		b = putUint64(b, e.Term)
		b = putUint64(b, uint64(e.Type))
		b = putBytes(b, e.Data)
		b = putBytes(b, e.Extensions)
	}
	b = putUint64(b, uint64(len(d.keys)))
	for i := 0; i < len(d.keys); i++ {
		b = putBytes(b, d.keys[i])
		b = putBytes(b, d.vals[i])
	}
	b = putUint64(b, uint64(len(d.ikeys)))
	for i := 0; i < len(d.ikeys); i++ {
		b = putBytes(b, d.ikeys[i])
		b = putUint64(b, d.ivals[i])
	}
	return putUint64(b, d.commit)
}

// decode sets the Disk's state from its file contents b.
func (d *Disk) decode(b []byte) error {
	r := &reader{b: b}
	n := r.uint64()
	for i := uint64(0); i < n && !r.err; i++ {
		var e raft.Log
		e.Index = r.uint64()
		e.Term = r.uint64()
		e.Type = raft.LogType(r.uint64())
		e.Data = r.bytes()
		e.Extensions = r.bytes()
		d.ents = append(d.ents, e)
	}
	n = r.uint64()
	for i := uint64(0); i < n && !r.err; i++ {
		d.keys = append(d.keys, r.bytes())
		d.vals = append(d.vals, r.bytes())
	}
	n = r.uint64()
	for i := uint64(0); i < n && !r.err; i++ {
		d.ikeys = append(d.ikeys, r.bytes())
		d.ivals = append(d.ivals, r.uint64())
	}
	d.commit = r.uint64()
	return r.done()
}

// persist writes the Disk's state to its file (d.mu held, or d not yet shared).
func (d *Disk) persist() {
	durable.Write(d.file, string(d.encode()))
}

// --- raft.LogStore and raft.CommitTrackingLogStore

// FirstIndex is the lowest index in the log, 0 if it is empty.
func (d *Disk) FirstIndex() (uint64, error) {
	d.mu.Lock()
	defer d.mu.Unlock()
	if len(d.ents) == 0 {
		return 0, nil
	}
	return d.ents[0].Index, nil
}

// LastIndex is the highest index in the log, 0 if it is empty.
func (d *Disk) LastIndex() (uint64, error) {
	d.mu.Lock()
	defer d.mu.Unlock()
	return d.lastIndex(), nil
}

func (d *Disk) lastIndex() uint64 {
	if len(d.ents) == 0 {
		return 0
	}
	return d.ents[len(d.ents)-1].Index
}

// GetLog copies the entry at index into *log, or returns raft.ErrLogNotFound.
func (d *Disk) GetLog(index uint64, log *raft.Log) error {
	d.mu.Lock()
	defer d.mu.Unlock()
	for i := 0; i < len(d.ents); i++ {
		if d.ents[i].Index == index {
			*log = d.ents[i]
			return nil
		}
	}
	return raft.ErrLogNotFound
}

// insert puts e in the log, replacing the entry at its index if there is one (d.mu held).
func (d *Disk) insert(e raft.Log) {
	i := 0
	for i < len(d.ents) && d.ents[i].Index < e.Index {
		i++
	}
	if i < len(d.ents) && d.ents[i].Index == e.Index {
		d.ents[i] = e
		return
	}
	ents := make([]raft.Log, 0, len(d.ents)+1)
	ents = append(ents, d.ents[:i]...)
	ents = append(ents, e)
	d.ents = append(ents, d.ents[i:]...)
}

// StoreLog stores one entry (and the staged commit index with it).
func (d *Disk) StoreLog(log *raft.Log) error {
	return d.StoreLogs([]*raft.Log{log})
}

// StoreLogs stores the entries, and the staged commit index with them, in one write.
func (d *Disk) StoreLogs(logs []*raft.Log) error {
	d.mu.Lock()
	defer d.mu.Unlock()
	for _, l := range logs {
		d.insert(raft.Log{Index: l.Index, Term: l.Term, Type: l.Type, Data: l.Data, Extensions: l.Extensions})
	}
	d.commit = d.staged
	d.persist()
	return nil
}

// DeleteRange deletes the entries at indexes min..max (none if max < min).
func (d *Disk) DeleteRange(min uint64, max uint64) error {
	d.mu.Lock()
	defer d.mu.Unlock()
	var ents []raft.Log
	for i := 0; i < len(d.ents); i++ {
		if d.ents[i].Index < min || max < d.ents[i].Index {
			ents = append(ents, d.ents[i])
		}
	}
	d.ents = ents
	d.persist()
	return nil
}

// StageCommitIndex stages idx, written with the next StoreLogs.
func (d *Disk) StageCommitIndex(idx uint64) error {
	d.mu.Lock()
	defer d.mu.Unlock()
	d.staged = idx
	return nil
}

// GetCommitIndex is the commit index written last, at most the last index in the log.
func (d *Disk) GetCommitIndex() (uint64, error) {
	d.mu.Lock()
	defer d.mu.Unlock()
	last := d.lastIndex()
	if d.commit > last {
		return last, nil
	}
	return d.commit, nil
}

// --- raft.StableStore (a missing key: Get's ErrNotFound, GetUint64's 0)

// Set sets key to a copy of val.
func (d *Disk) Set(key []byte, val []byte) error {
	d.mu.Lock()
	defer d.mu.Unlock()
	v := copyBytes(val)
	found := false
	for i := 0; i < len(d.keys); i++ {
		if bytesEq(d.keys[i], key) {
			d.vals[i] = v
			found = true
		}
	}
	if !found {
		d.keys = append(d.keys, copyBytes(key))
		d.vals = append(d.vals, v)
	}
	d.persist()
	return nil
}

// Get is a copy of key's value, or ErrNotFound.
func (d *Disk) Get(key []byte) ([]byte, error) {
	d.mu.Lock()
	defer d.mu.Unlock()
	for i := 0; i < len(d.keys); i++ {
		if bytesEq(d.keys[i], key) {
			return copyBytes(d.vals[i]), nil
		}
	}
	return nil, ErrNotFound
}

// SetUint64 sets key to val.
func (d *Disk) SetUint64(key []byte, val uint64) error {
	d.mu.Lock()
	defer d.mu.Unlock()
	found := false
	for i := 0; i < len(d.ikeys); i++ {
		if bytesEq(d.ikeys[i], key) {
			d.ivals[i] = val
			found = true
		}
	}
	if !found {
		d.ikeys = append(d.ikeys, copyBytes(key))
		d.ivals = append(d.ivals, val)
	}
	d.persist()
	return nil
}

// GetUint64 is key's value, or 0.
func (d *Disk) GetUint64(key []byte) (uint64, error) {
	d.mu.Lock()
	defer d.mu.Unlock()
	for i := 0; i < len(d.ikeys); i++ {
		if bytesEq(d.ikeys[i], key) {
			return d.ivals[i], nil
		}
	}
	return 0, nil
}
