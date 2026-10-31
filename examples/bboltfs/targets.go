package bboltfs

import (
	"io"
	"os"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unsafe"

	"golang.org/x/sys/unix"
)

// The verification targets: each test function returns true in every
// execution, and its spec is exactly that ({{ True }} testX(dir) {{ RET true }},
// with the paths it names allowed and absent). README.md says which bbolt site
// each one mirrors and which part of the model it exercises.
//
// The model lets any operation fail with an arbitrary errno and no effect (an
// environmental failure). A target's claim is about the runs where nothing
// fails: on a failure it stops and returns true, through envFailure.

// pageSize is common.DefaultPageSize (os.Getpagesize() on linux/amd64).
const pageSize = 4096

// minMmapSize is db.mmapSize's smallest mapping, 32 KiB.
const minMmapSize = 1 << 15

const flockRetryTimeout = 50 * time.Millisecond

// envErrors counts the environmental failures the targets met. The model
// does not read it; the Go tests check that real Linux never fails here.
var envErrors uint64

func envFailure() bool {
	atomic.AddUint64(&envErrors, 1)
	return true
}

// initDB is db.go's init: the four pages written with one WriteAt at offset 0,
// then fdatasync (bolt_linux.go). The file grows from 0 to 16 KiB by the
// WriteAt, and the fdatasync makes its contents and size durable (plan D3).
func initDB(f *os.File) error {
	buf := make([]byte, pageSize*4)
	initPages(buf, pageSize)
	if _, err := f.WriteAt(buf, 0); err != nil {
		return err
	}
	return syscall.Fdatasync(int(f.Fd()))
}

// flock is bolt_unix.go's flock with Options.Timeout 0: LOCK_NB with LOCK_EX
// or LOCK_SH, retried while the lock is held elsewhere.
func flock(f *os.File, exclusive bool) error {
	fd := f.Fd()
	flag := syscall.LOCK_NB
	if exclusive {
		flag |= syscall.LOCK_EX
	} else {
		flag |= syscall.LOCK_SH
	}
	for {
		err := syscall.Flock(int(fd), flag)
		if err == nil {
			return nil
		} else if err != syscall.EWOULDBLOCK {
			return err
		}
		time.Sleep(flockRetryTimeout)
	}
}

// Open's OpenFile(path, O_RDWR|O_CREATE, mode) on a new file, Name (db.path),
// Stat().Size() (Open's "initialize if empty" test), and Close, after which Fd
// is ^uintptr(0) through every copy of the File. Without O_CREATE, opening the
// absent file fails.
func testOpenCreate(dir string) bool {
	path := dir + "/db"
	if _, err := os.OpenFile(path, os.O_RDWR, 0o666); err == nil {
		return false
	}
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if f.Name() != path {
		return false
	}
	info, err := f.Stat()
	if err != nil {
		return envFailure()
	}
	if info.Size() != 0 {
		return false
	}
	g := *f
	_ = f.Close() // the fd is freed whatever Close returns
	return f.Fd() == ^uintptr(0) && g.Fd() == ^uintptr(0)
}

// db.go's init on the new file: Stat says 0, the 4 pages go out with one
// WriteAt, fdatasync, and Stat says 16 KiB.
func testInit(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	info, err := f.Stat()
	if err != nil {
		return envFailure()
	}
	if info.Size() != 0 {
		return false
	}
	buf := make([]byte, pageSize*4)
	initPages(buf, pageSize)
	n, err := f.WriteAt(buf, 0)
	if err != nil {
		return envFailure()
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return envFailure()
	}
	info, err = f.Stat()
	if err != nil {
		return envFailure()
	}
	ok := n == len(buf) && info.Size() == int64(pageSize*4)
	_ = f.Close()
	return ok
}

// db.go's getPageSizeFromFirstMeta and getPageSizeFromSecondMeta on a file
// init wrote: a 4 KiB ReadAt at offset 0 holds a valid meta 0; trying page
// sizes from 1 KiB, the first valid meta found past page 0 is meta 1, at 4 KiB.
func testReadPageSize(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	var buf [0x1000]byte
	bw, err := f.ReadAt(buf[:], 0)
	if err != nil {
		return envFailure()
	}
	m := pageAt(buf[:], 0).meta()
	if bw != len(buf) || !m.validate() || m.pageSize != pageSize || m.txid != 0 {
		return false
	}
	info, err := f.Stat()
	if err != nil {
		return envFailure()
	}
	fileSize := info.Size()
	found := 0
	var txid uint64
	for i := 0; i <= 14; i++ {
		var buf2 [0x1000]byte
		var pos int64 = 1024 << uint(i)
		if pos >= fileSize-1024 {
			break
		}
		bw, err := f.ReadAt(buf2[:], pos)
		if err != nil && err != io.EOF {
			return envFailure()
		}
		if (err == nil && bw == len(buf2)) || (err == io.EOF && int64(bw) == (fileSize-pos)) {
			if m := pageAt(buf2[:], 0).meta(); m.validate() {
				found = int(m.pageSize)
				txid = m.txid
				break
			}
		}
	}
	_ = f.Close()
	return found == pageSize && txid == 1
}

// Short reads: a ReadAt across EOF returns the bytes up to EOF and io.EOF
// (getPageSizeFromSecondMeta accepts err == io.EOF && bw == fileSize-pos); one
// at or past EOF returns 0 and io.EOF.
func testShortReadAt(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	var buf [0x2000]byte
	bw, err := f.ReadAt(buf[:], 3*pageSize)
	if err != io.EOF {
		if err == nil {
			return false
		}
		return envFailure()
	}
	p := pageAt(buf[:], 0)
	if bw != pageSize || p.id != 3 || p.flags != leafPageFlag {
		return false
	}
	bw, err = f.ReadAt(buf[:], 4*pageSize)
	if err != io.EOF {
		if err == nil {
			return false
		}
		return envFailure()
	}
	if bw != 0 {
		return false
	}
	bw, err = f.ReadAt(buf[:], 100*pageSize)
	if err != io.EOF {
		if err == nil {
			return false
		}
		return envFailure()
	}
	_ = f.Close()
	return bw == 0
}

// db.go's mmap and bolt_unix.go's mmap: a PROT_READ, MAP_SHARED mapping of
// db.mmapSize's 32 KiB over the 16 KiB file, Madvise(MADV_RANDOM) with ENOSYS
// ignored, page headers and metas loaded through views of the mapped bytes
// (db.page, Page.Meta), both metas validated (FNV-64a over the mapped bytes),
// the current meta copied out (tx.init), and Munmap of the original slice.
func testMmapMeta(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	info, err := f.Stat()
	if err != nil {
		return envFailure()
	}
	if info.Size() < pageSize*2 { // db.fileSize's check
		return false
	}
	b, err := unix.Mmap(int(f.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	err = unix.Madvise(b, syscall.MADV_RANDOM)
	if err != nil && err != syscall.ENOSYS {
		return envFailure()
	}
	p0 := pageAt(b, 0)
	p1 := pageAt(b, pageSize)
	meta0 := p0.meta()
	meta1 := p1.meta()
	ok := len(b) == minMmapSize &&
		p0.id == 0 && p0.flags == metaPageFlag && p1.id == 1 && p1.flags == metaPageFlag &&
		meta0.validate() && meta1.validate() && meta0.txid == 0 && meta1.txid == 1 &&
		pageAt(b, 2*pageSize).flags == freelistPageFlag &&
		pageAt(b, 3*pageSize).flags == leafPageFlag && pageAt(b, 3*pageSize).count == 0
	if m := pickMeta(meta0, meta1); m == nil {
		ok = false
	} else {
		v := *m
		ok = ok && v.txid == 1 && v.root.root == 3 && v.pgid == 4
	}
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = f.Close()
	return ok
}

// MAP_SHARED coherence: a WriteAt is seen at once by loads through the
// mapping, without a sync (tx.write's pages, which later transactions read
// through db.page). An extending WriteAt (NoGrowSync) makes the mapped pages up
// to its end loadable: its own bytes and the zero gap before it.
func testWriteVisibleInMap(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	b, err := unix.Mmap(int(f.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	buf := make([]byte, pageSize)
	p := pageAt(buf, 0)
	p.id = 2
	p.flags = leafPageFlag
	p.count = 7
	if _, err := f.WriteAt(buf, 2*pageSize); err != nil {
		return envFailure()
	}
	ok := pageAt(b, 2*pageSize).flags == leafPageFlag && pageAt(b, 2*pageSize).count == 7
	p.id = 5
	if _, err := f.WriteAt(buf, 5*pageSize); err != nil {
		return envFailure()
	}
	ok = ok && pageAt(b, 5*pageSize).id == 5 && pageAt(b, 5*pageSize).count == 7 &&
		pageAt(b, 4*pageSize).id == 0 && b[6*pageSize-1] == 0
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = f.Close()
	return ok
}

// db.allocate's remap followed by db.grow, in Commit's order: the mapping
// grows first (Munmap, then Mmap at 64 KiB, past the 16 KiB file), then
// Truncate to 64 KiB and Sync (grow's "Truncate and fsync to ensure file size
// metadata is flushed"). The grown pages load as zero through the mapping, and
// the old pages read as before.
func testGrowRemap(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	b, err := unix.Mmap(int(f.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	ok := pageAt(b, 0).meta().validate()
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	b, err = unix.Mmap(int(f.Fd()), 0, 2*minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	if err := f.Truncate(int64(2 * minMmapSize)); err != nil {
		return envFailure()
	}
	if err := f.Sync(); err != nil {
		return envFailure()
	}
	info, err := f.Stat()
	if err != nil {
		return envFailure()
	}
	ok = ok && info.Size() == int64(2*minMmapSize) &&
		pageAt(b, 0).meta().validate() && pageAt(b, pageSize).meta().validate() &&
		pageAt(b, 3*pageSize).flags == leafPageFlag &&
		pageAt(b, 4*pageSize).id == 0 && pageAt(b, 15*pageSize).flags == 0 &&
		b[2*minMmapSize-1] == 0
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = f.Close()
	return ok
}

// CopyFile's OpenFile(path, O_RDWR|O_CREATE|O_TRUNC, mode) on an existing,
// non-empty file empties it.
func testOpenTrunc(dir string) bool {
	path := dir + "/copy"
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if _, err := f.WriteAt([]byte("old contents"), 0); err != nil {
		return envFailure()
	}
	_ = f.Close()
	g, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o666)
	if err != nil {
		return envFailure()
	}
	info, err := g.Stat()
	if err != nil {
		return envFailure()
	}
	var buf [1]byte
	n, err := g.ReadAt(buf[:], 0)
	if err != io.EOF {
		if err == nil {
			return false
		}
		return envFailure()
	}
	_ = g.Close()
	return info.Size() == 0 && n == 0
}

// A second, read-only fd on the database while the read-write one is open:
// WriteTo's reopen (O_RDONLY|WriteFlag, with WriteFlag 0 the only flag the
// model allows) and bbolt's Options.ReadOnly (O_RDONLY, then mmap). Through it,
// WriteTo's data copy (an io.SectionReader over pages 2 up to tx.Size(), which
// calls ReadAt) reads what the first fd wrote, and a PROT_READ mapping of it
// holds valid metas.
func testReadOnlyReopen(dir string) bool {
	path := dir + "/db"
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	g, err := os.OpenFile(path, os.O_RDONLY, 0)
	if err != nil {
		return envFailure()
	}
	dataOffset := int64(pageSize * 2)
	dataSize := int64(4*pageSize) - dataOffset // tx.Size() is meta.pgid * pageSize
	buf := make([]byte, dataSize)
	n, err := g.ReadAt(buf, dataOffset)
	if err != nil {
		return envFailure()
	}
	ok := int64(n) == dataSize && pageAt(buf, 0).id == 2 && pageAt(buf, 0).flags == freelistPageFlag &&
		pageAt(buf, pageSize).id == 3 && pageAt(buf, pageSize).flags == leafPageFlag
	b, err := unix.Mmap(int(g.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	ok = ok && pickMeta(pageAt(b, 0).meta(), pageAt(b, pageSize).meta()) != nil
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = g.Close()
	_ = f.Close()
	return ok
}

// flock and funlock (bolt_unix.go): Open's exclusive lock on the read-write
// fd, then LOCK_UN; a read-only open's shared lock, then LOCK_UN. In the
// model Flock succeeds or returns any errno (plan D7); EWOULDBLOCK retries.
func testFlock(dir string) bool {
	path := dir + "/db"
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := flock(f, true); err != nil {
		return envFailure()
	}
	if err := syscall.Flock(int(f.Fd()), syscall.LOCK_UN); err != nil {
		return envFailure()
	}
	g, err := os.OpenFile(path, os.O_RDONLY, 0)
	if err != nil {
		return envFailure()
	}
	if err := flock(g, false); err != nil {
		return envFailure()
	}
	if err := syscall.Flock(int(g.Fd()), syscall.LOCK_UN); err != nil {
		return envFailure()
	}
	_ = g.Close()
	_ = f.Close()
	return true
}

// The trivial calls: os.Getpagesize (common.DefaultPageSize), mmap's
// Madvise(MADV_RANDOM), and mlock/munlock (mlock_unix.go) on the mapping
// resliced to the file size, as db.mlock(fileSize) does.
func testTrivialCalls(dir string) bool {
	if os.Getpagesize() != pageSize {
		return false
	}
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	b, err := unix.Mmap(int(f.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED|syscall.MAP_POPULATE)
	if err != nil {
		return envFailure()
	}
	err = unix.Madvise(b, syscall.MADV_RANDOM)
	if err != nil && err != syscall.ENOSYS {
		return envFailure()
	}
	fileSize := 4 * pageSize
	sizeToLock := fileSize
	if sizeToLock > len(b) {
		sizeToLock = len(b)
	}
	if err := unix.Mlock(b[:sizeToLock]); err != nil {
		return envFailure()
	}
	if err := unix.Munlock(b[:sizeToLock]); err != nil {
		return envFailure()
	}
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = f.Close()
	return true
}

// A WriteAt of no bytes past EOF writes nothing: Go's WriteAt loops while
// bytes remain, so it makes no system call, and the file keeps its size.
// (bbolt never does this; the target pins down the model's zero-length write.)
func testWriteAtEmpty(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	n, err := f.WriteAt([]byte{}, 100)
	if err != nil {
		return envFailure()
	}
	info, err := f.Stat()
	if err != nil {
		return envFailure()
	}
	_ = f.Close()
	return n == 0 && info.Size() == 0
}

// Readers and the writer at once, as beginTx and tx.Commit run. Each reader
// takes metalock then mmaplock.RLock, copies the valid meta with the highest
// txid, releases metalock, and loads the pages its meta reaches (the freelist
// and the root leaf) through the mapping. The writer, holding no mmaplock,
// WriteAts pages 4-7 (free pages, which no reader's meta reaches), fdatasyncs,
// then WriteAts the meta for txid 2 (root page 4) to slot 0 under metalock and
// fdatasyncs (tx.write, tx.writeMeta). Every load is disjoint from every
// in-flight write, which is all the model asks.
func testConcurrentDisjoint(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	// db.grow first, so that the writer's pages are inside the file
	if err := f.Truncate(int64(8 * pageSize)); err != nil {
		return envFailure()
	}
	if err := f.Sync(); err != nil {
		return envFailure()
	}
	b, err := unix.Mmap(int(f.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	var metalock sync.Mutex
	var mmaplock sync.RWMutex
	var wg sync.WaitGroup
	const nReaders = 4
	seen := make([]uint64, nReaders)
	good := make([]bool, nReaders)
	for i := 0; i < nReaders; i++ {
		j := i
		wg.Add(1)
		go func() {
			metalock.Lock()
			mmaplock.RLock()
			m := pickMeta(pageAt(b, 0).meta(), pageAt(b, pageSize).meta())
			ok := m != nil
			var tm Meta
			if ok {
				tm = *m
			}
			metalock.Unlock()
			ok = ok && pageAt(b, int(tm.freelist)*pageSize).flags == freelistPageFlag &&
				pageAt(b, int(tm.root.root)*pageSize).flags == leafPageFlag
			mmaplock.RUnlock()
			seen[j] = tm.txid
			good[j] = ok
			wg.Done()
		}()
	}

	// beginRWTx: copy the current meta under metalock
	metalock.Lock()
	cur := pickMeta(pageAt(b, 0).meta(), pageAt(b, pageSize).meta())
	ok := cur != nil
	var m Meta
	if ok {
		m = *cur
	}
	metalock.Unlock()
	if !ok {
		wg.Wait()
		return false
	}
	failed := false
	buf := make([]byte, 4*pageSize)
	for k := 0; k < 4; k++ {
		p := pageAt(buf, k*pageSize)
		p.id = Pgid(4 + k)
		p.flags = leafPageFlag
	}
	if !failed {
		if _, err := f.WriteAt(buf, 4*pageSize); err != nil {
			failed = true
		}
	}
	if !failed {
		if err := syscall.Fdatasync(int(f.Fd())); err != nil {
			failed = true
		}
	}
	if !failed {
		m.txid++
		m.root.root = 4
		m.pgid = 8
		mbuf := make([]byte, pageSize)
		mp := pageAt(mbuf, 0)
		m.write(mp)
		metalock.Lock()
		if _, err := f.WriteAt(mbuf, int64(mp.id)*pageSize); err != nil {
			failed = true
		}
		metalock.Unlock()
	}
	if !failed {
		if err := syscall.Fdatasync(int(f.Fd())); err != nil {
			failed = true
		}
	}
	wg.Wait()
	if failed {
		return envFailure()
	}
	for i := 0; i < nReaders; i++ {
		ok = ok && good[i] && (seen[i] == 1 || seen[i] == 2)
	}
	last := pickMeta(pageAt(b, 0).meta(), pageAt(b, pageSize).meta())
	ok = ok && last != nil && last.txid == 2 && last.root.root == 4 &&
		pageAt(b, 4*pageSize).flags == leafPageFlag
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = f.Close()
	return ok
}

// Negative offsets. Go's ReadAt and WriteAt return "negative offset" without a
// system call, and Truncate(-1) gets EINVAL. The plan's trusted models return
// Go's error first (the primitives are stuck on a negative offset).
func testNegativeOffset(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	var buf [1]byte
	_, err1 := f.ReadAt(buf[:], -1)
	_, err2 := f.WriteAt(buf[:], -1)
	err3 := f.Truncate(-1)
	_ = f.Close()
	return err1 != nil && err2 != nil && err3 != nil
}

// Stat racing a WriteAt that extends the empty file by three pages: whatever
// it sees lies between the old and the new size (StatSees, plan D8). Linux may
// show an intermediate size, so "the old or the new size" is not a target
// (twoways.testStatRacingExtend).
func testStatRacingExtendBounded(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	var wg sync.WaitGroup
	wrote := false
	wg.Add(1)
	go func() {
		if _, err := f.WriteAt(make([]byte, 3*pageSize), 0); err == nil {
			wrote = true
		}
		wg.Done()
	}()
	info, err := f.Stat()
	wg.Wait()
	if err != nil || !wrote {
		return envFailure()
	}
	sz := info.Size()
	_ = f.Close()
	return 0 <= sz && sz <= 3*pageSize
}

// WriteTo (etcd's snapshot) against a concurrent writer. The read
// transaction copies its meta (beginTx), generates the two meta pages from it,
// and copies pages 2 up to tx.Size() with ReadAt on the read-write fd
// (WriteFlag 0: f = tx.db.file, through an io.SectionReader). The writer
// meanwhile reuses pages that are free in the reader's view (5 and 6, freed
// before the reader began), fdatasyncs, and commits txid 3 to slot 1. The copy
// of a free page may be any mix of old and new bytes (ReadSees); the claim is
// only about the pages the reader's meta reaches, its root and its freelist,
// which no in-flight write touches.
func testWriteTo(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return envFailure()
	}
	if err := initDB(f); err != nil {
		return envFailure()
	}
	if err := f.Truncate(int64(8 * pageSize)); err != nil {
		return envFailure()
	}
	if err := f.Sync(); err != nil {
		return envFailure()
	}
	// txid 2: root 3, a freelist at page 4 listing pages 2, 5, 6 and 7, pgid 8
	if _, err := f.WriteAt(freelistPage(4, []Pgid{2, 5, 6, 7}), 4*pageSize); err != nil {
		return envFailure()
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return envFailure()
	}
	m2 := Meta{magic: magic, version: version, pageSize: pageSize,
		root: InBucket{root: 3}, freelist: 4, pgid: 8, txid: 2}
	mbuf := make([]byte, pageSize)
	m2.write(pageAt(mbuf, 0))
	if _, err := f.WriteAt(mbuf, 0); err != nil {
		return envFailure()
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return envFailure()
	}
	b, err := unix.Mmap(int(f.Fd()), 0, minMmapSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return envFailure()
	}
	var metalock sync.Mutex
	var mmaplock sync.RWMutex
	var wg sync.WaitGroup
	readOk := false
	readFailed := false
	wg.Add(1)
	go func() {
		// beginTx
		metalock.Lock()
		mmaplock.RLock()
		cur := pickMeta(pageAt(b, 0).meta(), pageAt(b, pageSize).meta())
		ok := cur != nil
		var tm Meta
		if ok {
			tm = *cur
		}
		metalock.Unlock()
		if ok {
			// WriteTo: the two meta pages, generated from tm
			out := make([]byte, int(tm.pgid)*pageSize)
			page := pageAt(out, 0)
			page.flags = metaPageFlag
			*page.meta() = tm
			page.meta().checksum = page.meta().sum64()
			page1 := pageAt(out, pageSize)
			page1.id = 1
			page1.flags = metaPageFlag
			m1 := tm
			m1.txid--
			*page1.meta() = m1
			page1.meta().checksum = page1.meta().sum64()
			// the data pages, copied with ReadAt
			dataOffset := int64(pageSize * 2)
			n, err := f.ReadAt(out[dataOffset:], dataOffset)
			if err != nil {
				readFailed = true
			} else {
				root := pageAt(out, int(tm.root.root)*pageSize)
				fl := pageAt(out, int(tm.freelist)*pageSize)
				readOk = n == len(out)-int(dataOffset) &&
					page.meta().validate() && page1.meta().validate() &&
					root.id == tm.root.root && root.flags == leafPageFlag &&
					fl.id == tm.freelist && fl.flags == freelistPageFlag &&
					(tm.txid == 2 && fl.count == 4 || tm.txid == 3 && fl.count == 3)
			}
		}
		mmaplock.RUnlock()
		wg.Done()
	}()

	// the writer: beginRWTx, then free pages 5 (new root) and 6 (new freelist)
	metalock.Lock()
	cur := pickMeta(pageAt(b, 0).meta(), pageAt(b, pageSize).meta())
	ok := cur != nil
	var m Meta
	if ok {
		m = *cur
	}
	metalock.Unlock()
	failed := !ok
	if !failed {
		pages := make([]byte, 2*pageSize)
		root := pageAt(pages, 0)
		root.id = 5
		root.flags = leafPageFlag
		copy(pages[pageSize:], freelistPage(6, []Pgid{2, 4, 7}))
		if _, err := f.WriteAt(pages, 5*pageSize); err != nil {
			failed = true
		}
	}
	if !failed {
		if err := syscall.Fdatasync(int(f.Fd())); err != nil {
			failed = true
		}
	}
	if !failed {
		m.txid++
		m.root.root = 5
		m.freelist = 6
		wbuf := make([]byte, pageSize)
		mp := pageAt(wbuf, 0)
		m.write(mp)
		metalock.Lock()
		if _, err := f.WriteAt(wbuf, int64(mp.id)*pageSize); err != nil {
			failed = true
		}
		metalock.Unlock()
	}
	if !failed {
		if err := syscall.Fdatasync(int(f.Fd())); err != nil {
			failed = true
		}
	}
	wg.Wait()
	if !ok {
		return false
	}
	if failed || readFailed {
		return envFailure()
	}
	if err := unix.Munmap(b); err != nil {
		return envFailure()
	}
	_ = f.Close()
	return readOk
}

// freelistPage is a freelist page with id id listing ids (Freelist.Write, for
// fewer than 0xFFFF ids).
func freelistPage(id Pgid, ids []Pgid) []byte {
	buf := make([]byte, pageSize)
	p := pageAt(buf, 0)
	p.id = id
	p.flags = freelistPageFlag
	p.count = uint16(len(ids))
	for i, x := range ids {
		*(*Pgid)(unsafe.Pointer(&buf[int(pageHeaderSize)+8*i])) = x
	}
	return buf
}
