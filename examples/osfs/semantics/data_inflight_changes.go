//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// Changes in flight: a write, truncate or fallocate is two steps (model
// decision).
//
// Decision: a change to a file's bytes or size starts (…Start, the change in
// flight) and finishes (…Finish). In between: a racing pread or fstat may see
// any mix of the change's prefixes; a crash may find any prefix landed; a
// load through a mapping of a byte the change could touch is stuck (a hole);
// a second change overlapping it is stuck.
//
// Lean: Impl.lean: OsChange, ProcState.inflight, the PWriteStart/Finish,
// FtruncateStart/Finish, FallocStart/Finish steps, Affects, InflightAt,
// SecBusy, Landed, osHole and HeapRendered (mappings), SecCand's in-flight
// case; the header's "Races" and "Mappings".
//
// Allowed: the reader below sees, per byte range, old or new data; a crash
// during the write keeps any prefix of it (by sector).
// Excluded (stuck, so no proved program does it): two overlapping writes in
// flight at once; a mapped load of a byte being written; a store to a
// PROT_READ mapping (a fatal fault on Linux).
//
// Why: Linux copies a write into the page cache page by page under each page's
// lock, and moves the size as it goes (generic_perform_write), so a racing
// read sees part of it (filemap_read samples i_size per batch); writeback may
// take any of its pages before it finishes. Two overlapping writes are
// ordered by i_rwsem in some order the model would have to guess; the clients
// (bbolt, one writer; the WAL, one appender) never race writes, so the model
// leaves it stuck rather than model it. A mapped load racing a write is a Go
// data race the proofs must exclude anyway.
func InflightChanges(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(8192, 'o'), 0)
	done := make(chan bool)
	go func() {
		f.WriteAt(fill(8192, 'n'), 0) // in flight while the reader runs
		done <- true
	}()
	buf := make([]byte, 8192)
	f.ReadAt(buf, 0) // allowed: any mix of o and n
	m, _ := syscall.Mmap(int(f.Fd()), 0, 8192, syscall.PROT_READ, syscall.MAP_SHARED)
	<-done
	_ = m[0] // fine after the write finished; stuck if it raced the write
	syscall.Munmap(m)
}
