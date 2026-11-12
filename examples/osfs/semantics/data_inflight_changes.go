//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// Changes in flight: a write, truncate or fallocate is two steps, and at most
// one change is in flight on a file (model decision; a stuck restriction).
//
// Decision: a change to a file's bytes or size starts (…Start: it announces the
// bytes it may change and their values, OsChange) and finishes (…Finish: it
// lands a prefix of exactly those values, OsFile.land). In between: a racing
// pread or fstat may see any value of a byte the change may touch; a crash may
// keep any of it, byte by byte (the start announced all of it); a load through
// a mapping of a byte the change may touch is stuck (a hole); a second change
// on the same file (a write, a truncate, a fallocate, an open with O_TRUNC) is
// stuck; and an empty pwrite is stuck. An mmap racing the change succeeds; only
// a load of a byte under the change is stuck.
//
// Lean: Impl.lean: OsChange, OsChange.ofWrite/ofResize, OsFile.announce,
// OsFile.land, ProcState.inflight, BusyAt, InflightAt, the PWriteStart/Finish,
// FtruncateStart/Finish, FallocStart/Finish steps, the Open step (O_TRUNC),
// osHole and HeapRendered (mappings), OsFile.synced (a sync leaves a byte under
// a change in flight as it was); the header's "Races" and "Mappings";
// Tests.lean: cacheOk_step (the page cache is always a crash candidate).
//
// Allowed: the reader below sees any byte values in the range being written
// (the model gives an in-flight byte any value); a crash during the write
// keeps any mix of old and new, byte by byte.
// Excluded (stuck, so no proved program does it): two changes in flight on one
// file at once; a mapped load of a byte being written; a store to a PROT_READ
// mapping (a fatal fault on Linux).
//
// Why: Linux copies a write into the page cache page by page under each page's
// lock, and moves the size as it goes (generic_perform_write), so a racing
// read sees part of it; writeback may take any of its pages before it
// finishes. Concurrent changes on one file are ordered by i_rwsem in an order
// the model would have to guess; every client (minibolt, one writer; walfs and
// crashlog, one thread; minibolt's readers only read) changes each file from
// one thread, so the model leaves concurrent changes stuck rather than model
// their interleaving: this removes the disjoint-range checks, and makes the
// announced values exactly what lands. Go's WriteAt and Write never issue an
// empty pwrite. A mapped load racing a write is a Go data race the proofs must
// exclude anyway.
func InflightChanges(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(8192, 'o'), 0)
	m, _ := syscall.Mmap(int(f.Fd()), 0, 8192, syscall.PROT_READ, syscall.MAP_SHARED)
	done := make(chan bool)
	go func() {
		f.WriteAt(fill(8192, 'n'), 0) // in flight while the reader runs
		done <- true
	}()
	buf := make([]byte, 8192)
	f.ReadAt(buf, 0) // allowed: any byte values in [0, 8192)
	<-done
	_ = m[0] // fine after the write finished; stuck if it raced the write
	syscall.Munmap(m)
}
