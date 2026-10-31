package bboltfs

import (
	"os"
	"sync"
	"syscall"
	"unsafe"

	"golang.org/x/sys/unix"
)

// minibolt is a two-meta-page store in bbolt's style, cut to one value: each
// commit appends a data page holding the value and points the meta at it.
//   - Open: flock, Stat, init if the file has no complete pair of metas, mmap,
//     validate both metas (FNV-64a), and read through the valid one with the
//     highest txid.
//   - Commit: remap if the new page is past the mapping, grow (Truncate and
//     Sync), write the data page and fdatasync, then write the meta to slot
//     txid % 2 and fdatasync.
//   - Get: a read transaction, through the mapping.
//
// It differs from bbolt in one place, init: bbolt writes the metas and the
// pages they point at with one WriteAt and one fdatasync, so a crash in between
// can leave a valid meta over a torn root page (README.md). minibolt syncs the
// pages first and the metas second, and redoes init when neither meta is valid,
// which (under the premise of README.md) only happens before init has synced
// the metas.

// DB is minibolt's database, with bbolt's three locks.
type DB struct {
	path    string
	file    *os.File
	dataref []byte // the mapping
	datasz  int
	filesz  int
	meta0   *Meta
	meta1   *Meta

	rwlock   sync.Mutex   // one writer at a time
	metalock sync.Mutex   // the meta pages
	mmaplock sync.RWMutex // the mapping, during remapping
}

// Open opens or creates the database at path.
func Open(path string) (*DB, error) {
	db := &DB{}
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return nil, err
	}
	db.file = f
	db.path = f.Name()
	if err := flock(f, true); err != nil {
		_ = f.Close()
		return nil, err
	}
	info, err := f.Stat()
	if err != nil {
		db.close()
		return nil, err
	}
	db.filesz = int(info.Size())
	if db.filesz < 4*pageSize {
		if err := db.init(); err != nil {
			db.close()
			return nil, err
		}
	}
	if err := db.mmap(0); err != nil {
		db.close()
		return nil, err
	}
	if !db.meta0.validate() && !db.meta1.validate() {
		if err := db.init(); err != nil {
			db.close()
			return nil, err
		}
	}
	return db, nil
}

// init writes db.go's four initial pages: the freelist and root pages, synced,
// then the two metas, synced.
func (db *DB) init() error {
	buf := make([]byte, 4*pageSize)
	initPages(buf, pageSize)
	if _, err := db.file.WriteAt(buf[2*pageSize:], 2*pageSize); err != nil {
		return err
	}
	if err := syscall.Fdatasync(int(db.file.Fd())); err != nil {
		return err
	}
	if _, err := db.file.WriteAt(buf[:2*pageSize], 0); err != nil {
		return err
	}
	if err := syscall.Fdatasync(int(db.file.Fd())); err != nil {
		return err
	}
	if db.filesz < 4*pageSize {
		db.filesz = 4 * pageSize
	}
	return nil
}

// mmapSize is db.mmapSize below 1 GiB: the smallest power of two from 32 KiB
// up that holds size.
func mmapSize(size int) int {
	sz := minMmapSize
	for sz < size {
		sz *= 2
	}
	return sz
}

// mmap is db.go's mmap: unmap, then map at least minsz and the file.
func (db *DB) mmap(minsz int) error {
	db.mmaplock.Lock()
	defer db.mmaplock.Unlock()
	size := db.filesz
	if size < minsz {
		size = minsz
	}
	size = mmapSize(size)
	if err := db.munmap(); err != nil {
		return err
	}
	b, err := unix.Mmap(int(db.file.Fd()), 0, size, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		return err
	}
	err = unix.Madvise(b, syscall.MADV_RANDOM)
	if err != nil && err != syscall.ENOSYS {
		_ = unix.Munmap(b)
		return err
	}
	db.dataref = b
	db.datasz = size
	db.meta0 = pageAt(b, 0).meta()
	db.meta1 = pageAt(b, pageSize).meta()
	return nil
}

// munmap is bolt_unix.go's munmap with db.invalidate.
func (db *DB) munmap() error {
	if db.dataref == nil {
		return nil
	}
	err := unix.Munmap(db.dataref)
	db.dataref = nil
	db.datasz = 0
	db.meta0 = nil
	db.meta1 = nil
	return err
}

// meta is db.go's meta, which panics when neither meta is valid. Its caller
// holds metalock.
func (db *DB) meta() *Meta {
	m := pickMeta(db.meta0, db.meta1)
	if m == nil {
		panic("minibolt: invalid meta pages")
	}
	return m
}

// Get is a read transaction (beginTx, then the root page through the mapping):
// the current txid, and the value if the root page holds one.
func (db *DB) Get() (uint64, uint64, bool) {
	db.metalock.Lock()
	db.mmaplock.RLock()
	m := *db.meta()
	db.metalock.Unlock()
	off := int(m.root.root) * pageSize
	has := pageAt(db.dataref, off).count == 1
	var v uint64
	if has {
		v = *(*uint64)(unsafe.Pointer(&db.dataref[off+int(pageHeaderSize)]))
	}
	db.mmaplock.RUnlock()
	return m.txid, v, has
}

// Commit is a write transaction storing v: a new root page at the high water
// mark, then the meta.
func (db *DB) Commit(v uint64) error {
	db.rwlock.Lock()
	defer db.rwlock.Unlock()
	db.metalock.Lock()
	m := *db.meta()
	db.metalock.Unlock()
	m.txid++
	pg := m.pgid
	m.pgid = pg + 1
	m.root.root = pg

	// db.allocate: remap if the high water mark passes the mapping
	minsz := int(m.pgid+1) * pageSize
	if minsz >= db.datasz {
		if err := db.mmap(minsz); err != nil {
			return err
		}
	}
	// db.grow: Truncate and Sync, so that the size is durable
	if minsz > db.filesz {
		sz := db.datasz
		if err := db.file.Truncate(int64(sz)); err != nil {
			return err
		}
		if err := db.file.Sync(); err != nil {
			return err
		}
		db.filesz = sz
	}
	// tx.write
	buf := make([]byte, pageSize)
	p := pageAt(buf, 0)
	p.id = pg
	p.flags = leafPageFlag
	p.count = 1
	*(*uint64)(unsafe.Pointer(&buf[int(pageHeaderSize)])) = v
	if _, err := db.file.WriteAt(buf, int64(pg)*pageSize); err != nil {
		return err
	}
	if err := syscall.Fdatasync(int(db.file.Fd())); err != nil {
		return err
	}
	// tx.writeMeta
	mbuf := make([]byte, pageSize)
	mp := pageAt(mbuf, 0)
	m.write(mp)
	db.metalock.Lock()
	if _, err := db.file.WriteAt(mbuf, int64(mp.id)*pageSize); err != nil {
		db.metalock.Unlock()
		return err
	}
	db.metalock.Unlock()
	return syscall.Fdatasync(int(db.file.Fd()))
}

// Close is db.go's Close: all three locks, unmap, funlock, close.
func (db *DB) Close() {
	db.rwlock.Lock()
	defer db.rwlock.Unlock()
	db.metalock.Lock()
	defer db.metalock.Unlock()
	db.mmaplock.Lock()
	defer db.mmaplock.Unlock()
	db.close()
}

func (db *DB) close() {
	_ = db.munmap()
	_ = syscall.Flock(int(db.file.Fd()), syscall.LOCK_UN)
	_ = db.file.Close()
}

// BootMinibolt is minibolt's boot program: it runs when the node starts and
// again after every crash. The value of the committed transaction txid is txid
// (init's two transactions have no value). Each boot checks that, commits the
// next transaction, and checks that it is visible. Its panics must never fire
// under the model's crash relation, however often the node crashes, given the
// premises of README.md. On an error it stops.
func BootMinibolt(dir string) {
	db, err := Open(dir + "/db")
	if err != nil {
		return
	}
	txid, v, has := db.Get()
	if txid <= 1 {
		if has {
			panic("minibolt: init's root page holds a value")
		}
	} else if !has || v != txid {
		panic("minibolt: the current meta's root page does not hold its value")
	}
	if err := db.Commit(txid + 1); err != nil {
		db.Close()
		return
	}
	txid2, v2, has2 := db.Get()
	if txid2 != txid+1 || !has2 || v2 != txid2 {
		panic("minibolt: a commit is not visible")
	}
	db.Close()
}
