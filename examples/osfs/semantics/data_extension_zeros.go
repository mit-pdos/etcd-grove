//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// An extension reads zeros past the old size, stale bytes included (model
// decision; audit F3 refuted).
//
// Decision: ftruncate up, a write past the end (its gap) and fallocate make
// the bytes between the old size and the new one read as zeros, even when a
// crash left stale bytes on disk past the recovered size.
//
// Lean: Impl.lean: OsFile.resized, OsFile.written (`0` past `f.size`), used by
// OsChange.ofResize/ofWrite and OsFile.land.
//
// Allowed: after the extensions below, the bytes past the old size read 00.
// Excluded: the stale 07 showing through.
//
// Why: documented (POSIX ftruncate: "the extended area shall appear as if it
// were zero-filled") and measured: a crash on ext4 data=ordered left 00 07 on
// disk under size 1 (notes/axiom-review/fs-v2-f3/f3.sh); after recovery,
// ftruncate(2) read 00 00, pwrite(09, at 3) read 00 00 00 09, and fallocate(0,
// 4) read 00 00 00 00 (Linux 7.0). Audit F3 had proposed that extensions show
// the raw sector bytes; the experiment refuted it, and the model change was
// reverted.
func ExtensionZeros(dir string) {
	// after a crash: dir/f has size 1 (00), its block holding 00 07 on disk
	f, _ := os.OpenFile(dir+"/f", os.O_RDWR, 0)
	f.Truncate(2) // reads 00 00
	f.Truncate(1)
	f.WriteAt([]byte{0x09}, 3) // reads 00 00 00 09
	f.Truncate(1)
	syscall.Fallocate(int(f.Fd()), 0, 0, 4) // reads 00 00 00 00
}
