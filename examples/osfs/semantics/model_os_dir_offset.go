//go:build linux

package semantics

import (
	"io"
	"os"
)

// A directory *File's offset (f_pos) after Readdirnames, and Seek's SEEK_END
// of a directory, are not modelled (Go model of os, models/os/model.go;
// 2026-11-25, adversarial review of the os model).
//
// Decision: the model's Readdirnames is stuck unless the *File's offset (the
// model's file.off) is 0, and leaves it unknown (-1), so that a later
// Seek(_, io.SeekCurrent) is stuck; Seek(_, io.SeekEnd) of a directory's fd
// (the extension's FdKind not 0) is stuck.
//
// Lean: Code/os.lean (translated from models/os/model.go): File.Readdirnames,
// File.Seek; their specs Proof/os/NsS.lean (os.File.Readdirnames.wp_dirS
// takes os.ownOff f 0), Proof/os/Off.lean (wp_end).
//
// Excluded (the model has no outcome, Go has one): the three calls below.
//
// Why: measured (TestDirOffset on C: after Readdirnames(-1) to the end,
// Seek(0, io.SeekCurrent) returns 2^63-1 on ext4, where the model's off was
// still 0) and documented (Linux fs/ext4/dir.c, ext4_dir_llseek: an htree
// directory's offsets are hash cookies and its end is EXT4_HTREE_EOF_64BIT,
// 2^63-1; SEEK_END seeks from that end, not from i_size; getdents reads from
// f_pos, which a Seek sets). No program the proofs cover seeks a directory;
// fileutil.ReadDir and the WAL's directory reads open, Readdirnames(-1) once
// and close.
func DirOffset(dir string) {
	d, _ := os.Open(dir)
	_, _ = d.Readdirnames(-1)
	_, _ = d.Seek(0, io.SeekCurrent) // 2^63-1 on ext4: stuck in the model
	_, _ = d.Seek(0, io.SeekEnd)     // the htree's end, not the size: stuck
	_, _ = d.Seek(1, io.SeekStart)
	_, _ = d.Readdirnames(-1) // from offset 1: stuck in the model
	d.Close()
}
