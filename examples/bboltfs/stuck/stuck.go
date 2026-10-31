// Package stuck holds the programs next to bboltfs's targets that the model
// of notes/osfs-ext-plan.md must NOT verify: for each test function here,
// {{ True }} testX(dir) {{ RET true }} (with dir+"/db" allowed and absent)
// must be unprovable, because the model is stuck on it on purpose. Go returns
// true for most of them (an error the program checks for, or a defined
// answer), or the program dies of a signal. ../README.md records each one's
// Go/Linux behaviour and why the model is stuck.
//
// One probe, testCASMapped, is not stuck in today's Perennial semantics: it
// is the plan's Perennial prerequisite, and stays provable (unsoundly) until
// that lands.
package stuck

import (
	"os"
	"sync"
	"sync/atomic"
	"syscall"
	"unsafe"

	"golang.org/x/sys/unix"
)

const pageSize = 4096

// newFile creates dir+"/db" with n pages, page i's bytes all byte(i+1),
// synced. The probes then do one thing the model is stuck on.
func newFile(dir string, n int) *os.File {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return nil
	}
	buf := make([]byte, n*pageSize)
	for i := range buf {
		buf[i] = byte(i/pageSize + 1)
	}
	if _, err := f.WriteAt(buf, 0); err != nil {
		return nil
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return nil
	}
	return f
}

// A store to a mapped byte: the mapping is PROT_READ. Linux: SIGSEGV (Go:
// "unexpected fault address", exit 2). Model: every mapped cell has a phantom
// reader, so every store is stuck.
func testStoreMapped(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	b[0] = 7
	return true
}

// A load past EOF, in a page of the mapping wholly past EOF (bbolt's 32 KiB
// mapping over a 16 KiB file). Linux: SIGBUS. Model: the cell is a hole.
func testLoadPastEOF(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 8*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	return b[5*pageSize] == 0
}

// A load past EOF but inside EOF's page. Linux: reads 0 (true). Model: a hole
// (deliberately incomplete: bbolt's files are whole pages).
func testLoadPastEOFSamePage(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return true
	}
	if _, err := f.WriteAt([]byte{1, 2, 3}, 0); err != nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	return b[2] == 3 && b[200] == 0
}

// A load through a mapping after Munmap (bbolt's remap with a stale page
// reference, which tx.root.dereference exists to prevent). Linux: SIGSEGV.
// Model: Munmap removes the cells.
func testLoadAfterMunmap(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	if err := unix.Munmap(b); err != nil {
		return true
	}
	return b[0] == 1
}

// A load after a Truncate shrank the file under the mapping. Linux: SIGBUS.
// Model: the cells past the new EOF are holes. (bbolt only grows.)
func testLoadAfterShrink(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	if err := f.Truncate(0); err != nil {
		return true
	}
	return b[0] == 1
}

// A load of a mapped word racing an overlapping WriteAt. Linux: the old word,
// the new one, or a mix (the kernel's copy is not one 8-byte store). Model:
// the word is a hole while the write is in flight, so the load is stuck.
func testLoadRacingWriteAt(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		_, _ = f.WriteAt([]byte{9, 9, 9, 9, 9, 9, 9, 9}, pageSize)
		wg.Done()
	}()
	v := *(*uint64)(unsafe.Pointer(&b[pageSize]))
	wg.Wait()
	return v == 0x0202020202020202 || v == 0x0909090909090909
}

// Mmap with PROT_WRITE. Linux: allowed on an O_RDWR fd, and a store through it
// is seen by ReadAt (true). Model: prot must be PROT_READ.
func testMmapWritable(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ|syscall.PROT_WRITE, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	b[0] = 42
	var buf [1]byte
	if _, err := f.ReadAt(buf[:], 0); err != nil {
		return true
	}
	return buf[0] == 42
}

// Mmap at a nonzero (page-aligned) offset. Linux: maps from page 1 (true).
// Model: the offset must be 0.
func testMmapOffset(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), pageSize, pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	return b[0] == 2
}

// Mmap of length 0. Linux: EINVAL (true). Model: the length must be positive.
func testMmapZeroLength(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	_, err := unix.Mmap(int(f.Fd()), 0, 0, syscall.PROT_READ, syscall.MAP_SHARED)
	return err != nil
}

// Munmap of a resliced mapping (len != cap, or a different base). Linux:
// x/sys/unix refuses with EINVAL and the mapping stays (true). Model: Munmap
// needs len = cap = the mapping's length at its base.
func testMunmapResliced(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	err1 := unix.Munmap(b[:pageSize])
	err2 := unix.Munmap(b[pageSize:])
	return err1 == syscall.EINVAL && err2 == syscall.EINVAL && b[0] == 1
}

// WriteAt after Close. Go: os.ErrClosed, no system call (true). Model: the
// File's fd is -1, and a call through a closed fd is stuck.
func testUseAfterClose(dir string) bool {
	f := newFile(dir, 1)
	if f == nil {
		return true
	}
	_ = f.Close()
	_, err := f.WriteAt([]byte{1}, 0)
	return err != nil
}

// fdatasync of a closed File's Fd(), which is ^uintptr(0), so fd -1. Linux:
// EBADF (true). Model: a call through an fd not in the table is stuck.
func testFdatasyncAfterClose(dir string) bool {
	f := newFile(dir, 1)
	if f == nil {
		return true
	}
	_ = f.Close()
	return syscall.Fdatasync(int(f.Fd())) == syscall.EBADF
}

// Flock on an fd that was never opened. Linux: EBADF (true). Model: stuck
// (plan D7), as every call through a forged fd.
func testNeverOpenedFd(dir string) bool {
	return syscall.Flock(1<<20, syscall.LOCK_UN) == syscall.EBADF
}

// Opening a path outside the allowed set (here outside dir). Linux: the file is
// created (true). Model: stuck.
func testOutsidePath(dir string) bool {
	f, err := os.OpenFile(dir+"/../outside", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return false
	}
	_ = f.Close()
	return true
}

// O_APPEND. Go: the open succeeds and WriteAt refuses ("invalid use of WriteAt
// on file opened with O_APPEND", true). Model: the flag is not allowed.
func testAppend(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE|os.O_APPEND, 0o666)
	if err != nil {
		return true
	}
	_, err = f.WriteAt([]byte{1}, 0)
	return err != nil
}

// WriteAt on an O_RDONLY file. Linux: EBADF (true). Model: misuse is stuck
// (plan D6).
func testWriteReadOnly(dir string) bool {
	f := newFile(dir, 1)
	if f == nil {
		return true
	}
	g, err := os.OpenFile(dir+"/db", os.O_RDONLY, 0)
	if err != nil {
		return true
	}
	_, err = g.WriteAt([]byte{1}, 0)
	return err != nil
}

// A CAS on a mapped word whose compare fails. Linux/amd64: LOCK CMPXCHG writes
// even when the compare fails, so it faults on the PROT_READ page: SIGSEGV.
// Model: NOT stuck in today's semantics, which lets CmpXchgBytesFailS read
// cells with readers and return false, so this probe is provable until the
// plan's Perennial prerequisite lands.
func testCASMapped(dir string) bool {
	f := newFile(dir, 4)
	if f == nil {
		return true
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 4*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return true
	}
	return !atomic.CompareAndSwapUint64((*uint64)(unsafe.Pointer(&b[0])), 0, 1)
}
