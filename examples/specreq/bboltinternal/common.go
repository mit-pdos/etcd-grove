//go:build ignore

// Requirement snippets of bbolt's internal/common (batch 4d,
// Spec/go_etcd_io/bbolt/internal/common/): what bbolt (node.go, cursor.go, bucket.go, tx.go,
// db.go) relies on of its page, meta and bucket-header encodings, each reliance an explicit
// panic. The package is internal, so examples cannot import it: the snippets are written as if in
// it (package common), not built, gofmt-clean.
//
// Common assumptions: page buffers are byte slices (make, the page pool, the mmap) at least one
// page header long; nothing else shares them.
package common

import (
	"bytes"
	"sort"
	"unsafe"
)

// REQ bboltinternal/node-round-trip: a node written to a page buffer reads back: the header as
// set, the same number of items, the same keys, and a leaf's flags and values or a branch's
// children.
// Users: node.go:178-200 (node.write: SetFlags, SetCount, WriteInodeToPage into Tx.allocate's
// buffer), node.go:160-170 (node.read: Id, IsLeafPage, ReadInodeFromPage, Inode.Key), db.go:1246-1250
// (allocate: SetId, SetOverflow).
// Assumes: items have non-empty keys, fewer than 2^16 of them, a branch's children are not id;
// buf holds the header and the laid-out items (the size node.size() computes).
// Specs: Page.SetId, Page.SetFlags, Page.SetCount, Page.Id, Page.Count, Page.IsLeafPage,
// WriteInodeToPage, ReadInodeFromPage, Inode.Key/Value/Flags/Pgid; laws: hdr_withHdr,
// writeNode_read, pageKV_access.
func ReqNodeRoundTrip(leaf bool, id Pgid, items Inodes, buf []byte) {
	p := (*Page)(unsafe.Pointer(&buf[0]))
	p.SetId(id)
	if leaf {
		p.SetFlags(LeafPageFlag)
	} else {
		p.SetFlags(BranchPageFlag)
	}
	p.SetCount(uint16(len(items)))
	WriteInodeToPage(items, p)
	if p.Id() != id || int(p.Count()) != len(items) || p.IsLeafPage() != leaf {
		panic("node-round-trip: header changed")
	}
	got := ReadInodeFromPage(p)
	if len(got) != len(items) {
		panic("node-round-trip: count")
	}
	for i := range items {
		if !bytes.Equal(got[i].Key(), items[i].Key()) {
			panic("node-round-trip: key")
		}
		if leaf {
			if got[i].Flags() != items[i].Flags() || !bytes.Equal(got[i].Value(), items[i].Value()) {
				panic("node-round-trip: leaf item")
			}
		} else if got[i].Pgid() != items[i].Pgid() {
			panic("node-round-trip: child")
		}
	}
}

// REQ bboltinternal/element-reads: on a page laid out as WriteInodeToPage leaves it, the cursor's
// direct element reads (a binary search over the elements' keys, then an element's key, value and
// flags, or a branch element's child) see the page's items.
// Users: cursor.go:326-336 (searchPage), cursor.go:362-366 (nsearch), cursor.go:385-386
// (keyValue), cursor.go:182,203 (first, last), tx.go:665-668 (forEachPageInternal),
// bucket.go:638-639 (stats: Pos, Ksize, Vsize), tx_check.go:103-118.
// Assumes: p's bytes are a node page written with items (as in node-round-trip), read-only.
// Specs: Page.FastCheck, Page.IsLeafPage, Page.Count, Page.LeafPageElements,
// Page.BranchPageElements, Page.LeafPageElement, Page.BranchPageElement,
// leafPageElement.Key/Value/Flags, branchPageElement.Key/Pgid; laws: elemsSlice_index,
// writeNode_read, pageKV_access.
func ReqElementKeys(p *Page, id Pgid, items Inodes, k []byte) {
	p.FastCheck(id)
	n := int(p.Count())
	if p.IsLeafPage() {
		elems := p.LeafPageElements()
		i := sort.Search(n, func(i int) bool { return bytes.Compare(elems[i].Key(), k) != -1 })
		if i < n {
			e := p.LeafPageElement(uint16(i))
			if !bytes.Equal(e.Key(), items[i].Key()) || !bytes.Equal(e.Value(), items[i].Value()) ||
				e.Flags() != items[i].Flags() {
				panic("element-reads: leaf element")
			}
		}
		return
	}
	elems := p.BranchPageElements()
	i := sort.Search(n, func(i int) bool { return bytes.Compare(elems[i].Key(), k) == 1 })
	if i > 0 {
		e := p.BranchPageElement(uint16(i - 1))
		if e.Pgid() != items[i-1].Pgid() || !bytes.Equal(e.Key(), items[i-1].Key()) {
			panic("element-reads: branch element")
		}
	}
}

// REQ bboltinternal/meta-round-trip: a meta written to a page (Tx.writeMeta) is a meta page at
// slot txid % 2 that validates and reads back with the meta's fields; a meta built field by
// field and summed (DB.init) validates; a meta with a wrong magic does not, with a non-nil error.
// Users: tx.go:440-455 (writeMeta), tx.go:609 (Meta.Write), tx.go:52-64 (Tx.init: Copy,
// RootBucket, IncTxid), db.go:688-704 (init), db.go:396,436,585 (getPageSize, mmap: Validate),
// db.go:1214-1232 (meta()).
// Assumes: m is bbolt's magic and version, its root and freelist pages below its high-water mark
// (or no freelist); buf is one page (at least 80 bytes).
// Specs: Meta.Write, Page.Meta, Page.Id, Page.IsMetaPage, Meta.Validate, Meta.Copy, Meta.Txid,
// Meta.Pgid, Meta.Freelist, Meta.RootBucket, InBucket.RootPage, Meta.Set*, Meta.Sum64,
// NewInBucket; laws: meta_view, meta_withMeta, meta_withHdr, metaValid_summed.
func ReqMetaRoundTrip(m *Meta, buf []byte, pageSize uint32) {
	p := (*Page)(unsafe.Pointer(&buf[0]))
	m.Write(p)
	if p.Id() != Pgid(m.Txid()%2) || !p.IsMetaPage() {
		panic("meta-round-trip: header")
	}
	if err := p.Meta().Validate(); err != nil {
		panic("meta-round-trip: written meta invalid")
	}
	c := &Meta{}
	p.Meta().Copy(c)
	if c.Txid() != m.Txid() || c.Pgid() != m.Pgid() || c.Freelist() != m.Freelist() ||
		c.RootBucket().RootPage() != m.RootBucket().RootPage() {
		panic("meta-round-trip: fields")
	}

	q := (*Page)(unsafe.Pointer(&buf[0]))
	q.SetId(0)
	q.SetFlags(MetaPageFlag)
	n := q.Meta()
	n.SetMagic(Magic)
	n.SetVersion(Version)
	n.SetPageSize(pageSize)
	n.SetFreelist(2)
	n.SetRootBucket(NewInBucket(3, 0))
	n.SetPgid(4)
	n.SetTxid(0)
	n.SetChecksum(n.Sum64())
	if n.Validate() != nil || n.PageSize() != pageSize {
		panic("meta-round-trip: init meta")
	}
	n.SetMagic(0)
	if n.Validate() == nil {
		panic("meta-round-trip: bad magic validates")
	}
}

// REQ bboltinternal/inline-bucket: a bucket value holds the bucket header, then the inline
// page; both read back through the value's bytes.
// Users: bucket.go:838-851 (Bucket.write), bucket.go:117-142 (openBucket), bucket.go:760-767
// (spill: a header-only value), bucket.go:539-578 (Sequence, SetSequence, NextSequence).
// Assumes: n's keys non-empty, fewer than 2^16; size is the inline node's laid-out size.
// Specs: InBucket.RootPage/InSequence/SetInSequence/IncSequence, Page.SetFlags/SetCount/Count/
// IsLeafPage, WriteInodeToPage; laws: inBucket_view, writeNode_read.
func ReqInlineBucket(ib InBucket, n Inodes, size int) {
	value := make([]byte, BucketHeaderSize+size)
	b := (*InBucket)(unsafe.Pointer(&value[0]))
	*b = ib
	p := (*Page)(unsafe.Pointer(&value[BucketHeaderSize]))
	p.SetFlags(LeafPageFlag)
	p.SetCount(uint16(len(n)))
	WriteInodeToPage(n, p)

	got := *(*InBucket)(unsafe.Pointer(&value[0]))
	if got.RootPage() != ib.RootPage() || got.InSequence() != ib.InSequence() {
		panic("inline-bucket: header")
	}
	ip := (*Page)(unsafe.Pointer(&value[BucketHeaderSize]))
	if !ip.IsLeafPage() || int(ip.Count()) != len(n) {
		panic("inline-bucket: inline page")
	}
	got.IncSequence()
	if got.InSequence() != ib.InSequence()+1 {
		panic("inline-bucket: sequence")
	}
}

// REQ bboltinternal/merge-pgids: merging two sorted id lists gives a sorted list of all of them.
// Users: freelist array.go:94 (mergeSpans), shared.go:244 (Copyall).
// Assumes: a and b sorted, their total length below 2^63.
// Specs: Pgids.Merge, Mergepgids.
func ReqMergePgids(a, b Pgids) {
	m := a.Merge(b)
	if len(m) != len(a)+len(b) {
		panic("merge-pgids: length")
	}
	for i := 1; i < len(m); i++ {
		if m[i-1] > m[i] {
			panic("merge-pgids: unsorted")
		}
	}
}
