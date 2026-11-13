//go:build linux

package semantics

import (
	"errors"
	"os"
	"syscall"
	"testing"

	"golang.org/x/sys/unix"
)

// Extra probes for the review.

// F_OFD_GETLK on a pipe fd and on a directory fd: Linux answers (nil, F_UNLCK).
func TestReviewGetlkPipeDir(t *testing.T) {
	r, w, _ := os.Pipe()
	defer r.Close()
	defer w.Close()
	lk := syscall.Flock_t{Type: syscall.F_RDLCK}
	err := syscall.FcntlFlock(r.Fd(), unix.F_OFD_GETLK, &lk)
	t.Logf("pipe: %v type %d", err, lk.Type)
	d, _ := os.Open(".")
	defer d.Close()
	lk = syscall.Flock_t{Type: syscall.F_RDLCK}
	err = syscall.FcntlFlock(d.Fd(), unix.F_OFD_GETLK, &lk)
	t.Logf("dir: %v type %d", err, lk.Type)
	lk = syscall.Flock_t{Type: syscall.F_RDLCK, Pid: 5}
	err = syscall.FcntlFlock(d.Fd(), unix.F_OFD_GETLK, &lk)
	t.Logf("dir, Pid 5: %v type %d", err, lk.Type)
}

// Empty write on a directory fd: EBADF (the model answers nil or any errno).
func TestReviewEmptyWriteDir(t *testing.T) {
	d, _ := os.Open(".")
	defer d.Close()
	n, err := d.Write(nil)
	t.Logf("dir: %d %v", n, err)
}

// fallocate on a read-only fd: EBADF (the model is stuck: misuse).
func TestReviewFallocRO(t *testing.T) {
	dd := extDir(t)
	f, _ := os.Create(dd + "/f")
	f.Close()
	r, _ := os.Open(dd + "/f")
	defer r.Close()
	t.Logf("ro mode0: %v", syscall.Fallocate(int(r.Fd()), 0, 0, 4096))
	t.Logf("ro mode1: %v", syscall.Fallocate(int(r.Fd()), 1, 0, 4096))
	w, _ := os.OpenFile(dd+"/f", os.O_RDWR, 0)
	defer w.Close()
	t.Logf("off+len overflow: %v", syscall.Fallocate(int(w.Fd()), 0, 1<<62, 1<<62))
}

// Stat of a mode-000 directory and file (open would fail EACCES for a non-root user).
func TestReviewStatNoPerm(t *testing.T) {
	dd := extDir(t)
	os.Mkdir(dd+"/d", 0)
	defer os.Chmod(dd+"/d", 0o700)
	fi, err := os.Stat(dd + "/d")
	t.Logf("stat mode-000 dir: %v %v", fi.Mode(), err)
	_, oerr := os.Open(dd + "/d")
	t.Logf("open mode-000 dir: %v (uid %d)", oerr, os.Getuid())
	if oerr != nil && !errors.Is(oerr, syscall.EACCES) {
		t.Fatal(oerr)
	}
}

// RemoveAll of a path whose last component is a file under a file.
func TestReviewRemoveAllUnderFile(t *testing.T) {
	dd := extDir(t)
	f, _ := os.Create(dd + "/f")
	f.Close()
	err := os.RemoveAll(dd + "/f/x")
	t.Logf("RemoveAll(f/x): %v", err)
	err = os.RemoveAll(dd + "/f/")
	t.Logf("RemoveAll(f/): %v", err)
	_, serr := os.Stat(dd + "/f")
	t.Logf("f after: %v", serr)
}
