// Package crashlog is the smallest crash-safe program over the Linux file
// extension (GooseLang/Ext/OsFs): a commit flag that guards 8 bytes of data in
// one file. Its boot program's panics never fire, however often the node
// crashes (Proof/github_com/mit_pdos/etcd_grove/examples/crashlog/Results.lean).
//
// The layout is the data at offset 0 and the flag byte at offset 8, after the
// data. The flag cannot come first: the first write to an empty file extends it
// over offset 0, and until that write is synced a crash may leave any byte
// there (the unsynced bytes of an extended file are arbitrary, D1 of
// notes/osfs-ext-plan.md), a nonzero flag with no data. With the flag after the
// data, the flag byte does not exist until the data is durable: a crash before
// then leaves the file at most 8 bytes long.
package crashlog

import (
	"os"
	"syscall"
)

// newData is the fixed value the flag guards (a function, not a package
// variable, so that the package has no initialized state).
func newData() []byte {
	return []byte{0xde, 0xad, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67}
}

// dataOk says that b starts with the 8 bytes of newData.
func dataOk(b []byte) bool {
	return len(b) >= 8 && b[0] == 0xde && b[1] == 0xad && b[2] == 0xbe && b[3] == 0xef &&
		b[4] == 0x01 && b[5] == 0x23 && b[6] == 0x45 && b[7] == 0x67
}

// Boot recovers or commits: if the flag is set, the data must be there;
// otherwise it writes the data, makes it durable, then sets the flag and makes
// that durable. On any error it returns.
func Boot(dir string) {
	f, err := os.OpenFile(dir+"/log", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return
	}
	run(f)
	f.Close()
}

// run is Boot on the open file. The flag exists only if the file is longer
// than 8 bytes (Stat), so the flag's read never meets the end of the file.
func run(f *os.File) {
	fi, err := f.Stat()
	if err != nil {
		return
	}
	if fi.Size() > 8 {
		flag := make([]byte, 1)
		if _, err := f.ReadAt(flag, 8); err != nil {
			return
		}
		if flag[0] != 0 {
			check(f)
			return
		}
	}
	commit(f)
}

// check is the committed case: the data is durable.
func check(f *os.File) {
	buf := make([]byte, 8)
	if _, err := f.ReadAt(buf, 0); err != nil {
		return
	}
	if !dataOk(buf) {
		panic("crashlog: the flag is set but the data is not there")
	}
}

// commit writes the data, makes it durable, then sets the flag and makes that
// durable, and reads both back.
func commit(f *os.File) {
	if _, err := f.WriteAt(newData(), 0); err != nil {
		return
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return
	}
	if _, err := f.WriteAt([]byte{1}, 8); err != nil {
		return
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return
	}
	buf := make([]byte, 9)
	if _, err := f.ReadAt(buf, 0); err != nil {
		return
	}
	if !dataOk(buf) || buf[8] != 1 {
		panic("crashlog: the commit did not read back")
	}
}
