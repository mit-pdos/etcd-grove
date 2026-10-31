// Package bboltfs holds the acceptance tests for the Linux file extension of
// notes/osfs-ext-plan.md (files, fsync and read-only mmap): Go programs that
// call the operating system exactly as go.etcd.io/bbolt does (bolt_unix.go,
// bolt_linux.go, db.go, tx.go, mlock_unix.go), with bbolt's flags.
//
//   - targets.go: programs that return true in Go, and must be provable in the
//     model ({{ True }} testX(dir) {{ RET true }}).
//   - minibolt.go: a two-meta-page store in bbolt's style, and its boot
//     program, whose assertions must never fire under the model's crash
//     relation.
//   - stuck/: programs the model is stuck on on purpose (unprovable).
//   - twoways/: boot programs for which both answers are model behaviours.
//
// README.md says what each one exercises and why. Every program takes the
// directory it works in as its parameter and opens only paths dir+"/"+name:
// the model's set of allowed paths is fixed, and each program's precondition
// says which of those names are allowed (and absent at the start).
//
// The page and meta layout below is internal/common's, as in Perennial's
// goose/testdata/examples/unsafememory (meta.go, page.go).
package bboltfs

import "unsafe"

type Pgid uint64

const (
	leafPageFlag     = 0x02
	metaPageFlag     = 0x04
	freelistPageFlag = 0x10
)

// Page is internal/common/page.go's Page.
type Page struct {
	id       Pgid
	flags    uint16
	count    uint16
	overflow uint32
}

const pageHeaderSize = unsafe.Sizeof(Page{})

// InBucket is internal/common/bucket.go's InBucket.
type InBucket struct {
	root     Pgid
	sequence uint64
}

// Meta is internal/common/meta.go's Meta (64 bytes, no padding).
type Meta struct {
	magic    uint32
	version  uint32
	pageSize uint32
	flags    uint32
	root     InBucket
	freelist Pgid
	pgid     Pgid
	txid     uint64
	checksum uint64
}

const (
	magic   uint32 = 0xED0CDAED
	version uint32 = 2
)

// pageAt is db.go's pageInBuffer and page: the page at byte offset off of b,
// which is a Go buffer or the mapping. bbolt views the mapping through
// db.data, a (*[MaxMapSize]byte); here, as in unsafememory's patched forms, the
// mapped slice is indexed directly.
func pageAt(b []byte, off int) *Page {
	return (*Page)(unsafe.Pointer(&b[off]))
}

// meta is Page.Meta: the Meta right after the page header.
func (p *Page) meta() *Meta {
	return (*Meta)(unsafe.Add(unsafe.Pointer(p), unsafe.Sizeof(*p)))
}

// sum64 is Meta.Sum64: FNV-64a over the bytes of m before its checksum field.
// bbolt calls hash/fnv; the loop is that hash, inlined.
func (m *Meta) sum64() uint64 {
	var h uint64 = 14695981039346656037
	for _, c := range (*[unsafe.Offsetof(Meta{}.checksum)]byte)(unsafe.Pointer(m))[:] {
		h ^= uint64(c)
		h *= 1099511628211
	}
	return h
}

// validate is Meta.Validate.
func (m *Meta) validate() bool {
	return m.magic == magic && m.version == version && m.checksum == m.sum64()
}

// write is Meta.Write: it sets m's checksum and copies m into the meta page p,
// through a local (the bbolt fork's Meta.Copy).
func (m *Meta) write(p *Page) {
	p.id = Pgid(m.txid % 2)
	p.flags = metaPageFlag
	m.checksum = m.sum64()
	v := *m
	*p.meta() = v
}

// initPages lays out db.go's init buffer over buf (4 pages of pageSize): meta
// pages 0 and 1 (txids 0 and 1), an empty freelist at page 2 and an empty leaf
// at page 3, the root.
func initPages(buf []byte, pageSize int) {
	for i := 0; i < 2; i++ {
		p := pageAt(buf, i*pageSize)
		p.id = Pgid(i)
		p.flags = metaPageFlag
		m := p.meta()
		m.magic = magic
		m.version = version
		m.pageSize = uint32(pageSize)
		m.freelist = 2
		m.root = InBucket{root: 3}
		m.pgid = 4
		m.txid = uint64(i)
		m.checksum = m.sum64()
	}
	p := pageAt(buf, 2*pageSize)
	p.id = 2
	p.flags = freelistPageFlag
	p.count = 0
	p = pageAt(buf, 3*pageSize)
	p.id = 3
	p.flags = leafPageFlag
	p.count = 0
}

// pickMeta is db.go's meta: the valid meta with the highest txid, or nil if
// neither is valid (where bbolt panics).
func pickMeta(meta0, meta1 *Meta) *Meta {
	metaA := meta0
	metaB := meta1
	if meta1.txid > meta0.txid {
		metaA = meta1
		metaB = meta0
	}
	if metaA.validate() {
		return metaA
	} else if metaB.validate() {
		return metaB
	}
	return nil
}
