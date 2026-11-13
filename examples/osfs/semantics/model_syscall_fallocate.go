//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// syscall.Fallocate is golang.org/x/sys/unix.Fallocate (trusted model; a
// draft pending review, 2026-11-13).
//
// Decision: syscall.Fallocate(fd, mode, off, len) is the same fallocate(2)
// stub as unix.Fallocate (one Syscall6(SYS_FALLOCATE, ...), errnoErr, EINTR
// not retried) and has the same model: mode 0 is FallocStart then
// FallocFinish (a resize to max(size, off+len) in flight; on failure any size
// between), mode 1 (FALLOC_FL_KEEP_SIZE) is FallocKeep (no change, any errno);
// a negative off or a len not above 0 is stuck (Linux: EINVAL, misuse); any
// other mode panics (not modelled).
//
// Lean: LinuxFs/TrustedCode/syscall.lean: Fallocate.impl (the body of
// LinuxFs/TrustedCode/golang_org/x/sys/unix.lean's Fallocate.impl, repeated:
// unix's file imports syscall's); Impl.lean: FallocStart, FallocFinish,
// FallocKeep (data_keep_size.go, data_resize_chunks.go).
//
// Allowed: below, size 4096 after the first call, unchanged by the second;
// any errno from either (then the first may have grown the file part way).
// Excluded: nothing beyond unix.Fallocate's model.
//
// Why: documented (go1.27.3 src/syscall/zsyscall_linux_amd64.go, Fallocate;
// golang.org/x/sys v0.48.0 unix/zsyscall_linux.go, Fallocate: the same
// system call with the same arguments) and measured (TestSyscallFallocate:
// mode 0 grows the size, mode 1 does not). etcd's fileutil.Preallocate
// (preallocate_unix.go) calls syscall's, not unix's: the WAL preallocates
// each segment with mode 0, ZeroToEnd with mode 1.
func SyscallFallocate(dir string) {
	f, _ := os.Create(dir + "/seg")
	syscall.Fallocate(int(f.Fd()), 0, 0, 4096) // size 4096
	syscall.Fallocate(int(f.Fd()), 1, 0, 8192) // size still 4096
	f.Close()
}
