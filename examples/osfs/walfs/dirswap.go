package walfs

import (
	"os"
)

// dirswap.go: a directory made to appear atomically, as the WAL's Create makes
// its directory (wal.go: CreateDirAll of dirpath.tmp, the first segment created
// in it and synced, Rename(tmp, dirpath), then Fsync of the parent; the
// temporary directory itself is never synced). The directory dir/wal appears
// with its one file seg holding the data, or not at all.
//
// Whether BootDir's panic can fire depends on the crash model of directory
// entries. With each directory's entries durable only through that directory's
// fsync (POSIX), a crash after Create may keep the rename (the parent was
// synced) and lose seg's entry in the renamed directory (never synced): wal
// without seg. With the metadata operations durable in order, as ext4's and
// xfs's journals make them (the extension's model, notes/walfs-ext-plan.md,
// N1), syncing the parent after the rename makes the earlier create of seg
// durable too. etcd's WAL relies on the latter.

// Create makes dir/wal with dir/wal/seg holding the data. On any error it
// returns.
func Create(dir string) {
	tmp := dir + "/wal.tmp"
	os.Remove(tmp + "/seg")
	os.Remove(tmp)
	if err := os.Mkdir(tmp, 0o750); err != nil {
		return
	}
	f, err := os.OpenFile(tmp+"/seg", os.O_RDWR|os.O_CREATE, 0o666)
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
	if err := os.Rename(tmp, dir+"/wal"); err != nil {
		return
	}
	syncDir(dir)
}

// BootDir checks dir/wal if it exists, and creates it otherwise.
func BootDir(dir string) {
	names, ok := readNames(dir)
	if !ok {
		return
	}
	for _, n := range names {
		if n == "wal" {
			checkDir(dir + "/wal")
			return
		}
	}
	Create(dir)
}

// checkDir: the directory holds seg, with the data.
func checkDir(wal string) {
	names, ok := readNames(wal)
	if !ok {
		return
	}
	for _, n := range names {
		if n == "seg" {
			check(wal)
			return
		}
	}
	panic("walfs: the WAL directory exists without its segment")
}
