// Package walfs holds the smallest programs that use the file-system calls
// etcd's WAL (server/storage/wal, client/pkg/fileutil) makes beyond the ones
// minibolt makes: directories (open, read, fsync), rename, unlink and mkdir,
// and the sequential I/O of a segment (seek, write, fallocate, an OFD lock).
// They are the acceptance tests of the namespace of the Linux file extension
// (GooseLang/Ext/OsFs, notes/walfs-ext-plan.md).
//
// segdir.go: a segment committed by rename. The directory dir holds at most a
// committed segment "seg", whose 8 bytes are the data, and perhaps a leftover
// "seg.tmp" of an interrupted commit. The commit writes the data to seg.tmp,
// makes it durable, renames seg.tmp to seg and makes the directory durable, as
// the WAL's cut() does with a segment (file_pipeline.go's alloc, then cut's
// Rename and Fsync(w.dirFile)). Boot's panics never fire, however often the
// node crashes (Proof/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/).
package walfs

import (
	"os"
)

// newData is the fixed value of a committed segment.
func newData() []byte {
	return []byte{0xde, 0xad, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67}
}

// dataOk says that b is the 8 bytes of newData.
func dataOk(b []byte) bool {
	return len(b) == 8 && b[0] == 0xde && b[1] == 0xad && b[2] == 0xbe && b[3] == 0xef &&
		b[4] == 0x01 && b[5] == 0x23 && b[6] == 0x45 && b[7] == 0x67
}

// readNames lists the names in the directory dir, as fileutil.ReadDir does
// (without its sort).
func readNames(dir string) ([]string, bool) {
	d, err := os.Open(dir)
	if err != nil {
		return nil, false
	}
	names, err := d.Readdirnames(-1)
	d.Close()
	if err != nil {
		return nil, false
	}
	return names, true
}

// syncDir makes the entries of the directory dir durable, as fileutil.OpenDir
// and fileutil.Fsync do.
func syncDir(dir string) bool {
	d, err := os.Open(dir)
	if err != nil {
		return false
	}
	err = d.Sync()
	d.Close()
	return err == nil
}

// Boot removes a leftover seg.tmp, then checks the committed segment, or
// commits it if there is none. On any error it returns.
func Boot(dir string) {
	names, ok := readNames(dir)
	if !ok {
		return
	}
	have := false
	for _, n := range names {
		if n == "seg" {
			have = true
		}
		if n == "seg.tmp" {
			os.Remove(dir + "/seg.tmp")
		}
	}
	if have {
		check(dir)
		return
	}
	commit(dir)
}

// check is the committed case: the segment holds the data.
func check(dir string) {
	f, err := os.OpenFile(dir+"/seg", os.O_RDONLY, 0)
	if err != nil {
		return
	}
	buf := make([]byte, 8)
	_, err = f.ReadAt(buf, 0)
	f.Close()
	if err != nil {
		return
	}
	if !dataOk(buf) {
		panic("walfs: the segment is committed but does not hold the data")
	}
}

// commit writes the data to seg.tmp and makes it durable, then renames it to
// seg and makes the directory durable, and checks the result.
func commit(dir string) {
	f, err := os.OpenFile(dir+"/seg.tmp", os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o666)
	if err != nil {
		return
	}
	if _, err := f.WriteAt(newData(), 0); err != nil {
		f.Close()
		return
	}
	if err := f.Sync(); err != nil {
		f.Close()
		return
	}
	f.Close()
	if err := os.Rename(dir+"/seg.tmp", dir+"/seg"); err != nil {
		return
	}
	if !syncDir(dir) {
		return
	}
	check(dir)
}
