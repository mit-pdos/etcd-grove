//go:build linux

package semantics

import (
	"io"
	"os"
)

// io.Copy between two files: copy_file_range(2) as a read and a write
// (model decision, 2026-11-14; pending the user's review).
//
// Decision: Go's path for io.Copy(dst, src) with two *os.File on Linux
// (Go 1.27.3) is translated (io.Copy's copyBuffer: io.go:407; File.WriteTo:
// file.go:265, whose writeTo, zero_copy_linux.go:18, finds no network
// connection behind dst's SyscallConn and is unhandled; genericWriteTo,
// file.go:294, calls io.Copy(dst, fileWithoutWriteTo{src}), which has no
// WriteTo; File.ReadFrom, file.go:175; readFrom, zero_copy_linux.go:42;
// copyFileRange, zero_copy_linux.go:89; poll.CopyFileRange,
// copy_file_range_unix.go:13, and handleCopyFileRangeErr,
// copy_file_range_linux.go:95; when unhandled, spliceToFile,
// zero_copy_linux.go:59, also unhandled for a file source, and
// genericReadFrom, file.go:204: io.Copy's read/write loop). Only the system
// call is modelled: one copy_file_range(src, NULL, dst, NULL, max, 0) is the
// extension's PRead of up to max bytes at the source's offset, then
// PWriteStart/PWriteFinish of what it read at the destination's offset (a
// write: its announcement, page cuts, crash candidates), and both offsets move
// by the count written; an errno with nothing written is returned; the end of
// the source gives 0. The kernel-version check (supportCopyFileRange, Linux >=
// 5.3) is true on C. readFrom, copyFileRange and spliceToFile are Go's bodies
// with the poll.FD (absent from the model's file layout) replaced: they are
// trusted.
//
// Lean: LinuxFs/TrustedCode/os.lean: model.copyFileRangeRound (the system
// call), model.pollCopyFileRange (poll.CopyFileRange's loop),
// File.copyFileRange.impl, File.spliceToFile.impl (splice(2) not modelled: a
// panic, unreachable from a *File), File.readFrom.impl (appendMode false),
// rawConn.{Control,Read,Write}.impl (panics, never called on this path);
// LinuxFs/Code/os.toml and internal/poll.toml (the translated rest).
//
// Allowed: the whole rest of the source copied in one round or in several
// (PRead's short counts), the count returned, both offsets advanced by it;
// at the source's end 0, after which Go falls back to the generic loop (which
// reads 0 bytes and returns); any errno with nothing copied (EINVAL, EXDEV,
// ... make Go fall back, others are returned as *os.SyscallError); a short
// count after an error part way. Excluded: a round copying bytes that are
// not the source's at its offset, or writing them elsewhere than the
// destination's offset; offsets moved by other than the count; a 0 count
// before the source's end (Linux >= 5.19 never reports one, the kernel commit
// handleCopyFileRangeErr cites; on C it would make Go's loop stop early).
//
// Why: measured on configuration C (models_test.go TestCopyFileRange, run by
// run-models-on-c.sh, 2026-11-14, kernel 7.0.0-38): copy_file_range of 12388
// bytes from offset 100 of a 12488-byte file to offset 50 of another returns
// 12388, the source's offset 12488 and the destination's 12438 after it, the
// bytes those of the source; at the source's end it returns 0; on one file
// with overlapping ranges, EINVAL with nothing changed; and strace of
// io.Copy(dst, src) (TestCopyFileRangeIoCopy) shows one copy_file_range
// returning the whole rest and one returning 0 (the loop's end), no read or
// write; from an empty source, one copy_file_range returning 0, then read(2)
// returning 0 (the generic loop). From the source (Linux 7.0): ext4 has no
// remap_file_range, so vfs_copy_file_range (fs/read_write.c) copies through
// splice_copy_file_range -> do_splice_direct, a page-cache read of the source
// and a generic_perform_write of the destination (pwrite's path), returning
// the bytes written and advancing both positions by them. Which client needs
// it: the WAL's Repair (io.Copy of the torn segment to its .broken file,
// notes/wal-fsext-plan.md, "io.Copy log").
func CopyFileRange(dir string) {
	src, _ := os.Create(dir + "/src")
	src.Write(fill(10000, 'a'))
	src.Seek(100, 0)
	dst, _ := os.Create(dir + "/dst")
	n, err := io.Copy(dst, src)
	// allowed: n == 9900, err == nil, dst holds src[100:], both offsets
	// advanced by 9900; or an error with a prefix of it copied
	// excluded: err == nil with less copied
	_, _ = n, err
	// crash here
	// allowed: dst's bytes as after a pwrite of them that was not synced
}
