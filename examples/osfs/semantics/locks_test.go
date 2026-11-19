//go:build linux

package semantics

// Measurements behind the lock semantics (locks_*.go), on configuration C (env_config.go):
// run-models-on-c.sh runs them with the other models' tests. Each test says the decision it
// backs.

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"os/signal"
	"syscall"
	"testing"
	"time"

	"golang.org/x/sys/unix"
)

func ofdLk(f *os.File, cmd int, typ int16) error {
	lk := syscall.Flock_t{Type: typ, Whence: 0, Start: 0, Len: 0}
	return syscall.FcntlFlock(f.Fd(), cmd, &lk)
}

func openRW(t *testing.T, name string) *os.File {
	t.Helper()
	f, err := os.OpenFile(name, os.O_RDWR|os.O_CREATE, 0o600)
	if err != nil {
		t.Fatal(err)
	}
	return f
}

// locks_ofd.go: OFD locks conflict between two open file descriptions of one process (two
// opens of one file), whole-file exclusive against exclusive and shared, shared against
// exclusive, not shared against shared; the errno of a conflict is EAGAIN (= EWOULDBLOCK);
// closing the holder's only fd releases its lock; F_UNLCK releases it, and succeeds on a
// description with no lock.
func TestLocksOFDConflict(t *testing.T) {
	if uintptr(syscall.EWOULDBLOCK) != 11 || uintptr(syscall.EAGAIN) != 11 {
		t.Fatalf("EAGAIN %d, EWOULDBLOCK %d", syscall.EAGAIN, syscall.EWOULDBLOCK)
	}
	name := extDir(t) + "/LOCK"
	a, b := openRW(t, name), openRW(t, name)
	defer b.Close()
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("a excl: %v", err)
	}
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_WRLCK); err != syscall.EAGAIN {
		t.Fatalf("b excl vs a excl: %v, want EAGAIN", err)
	}
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_RDLCK); err != syscall.EAGAIN {
		t.Fatalf("b shared vs a excl: %v, want EAGAIN", err)
	}
	if !errors.Is(ofdLk(b, unix.F_OFD_SETLK, syscall.F_WRLCK), syscall.EWOULDBLOCK) {
		t.Fatal("errors.Is(EAGAIN, EWOULDBLOCK) false")
	}
	a.Close() // releases a's lock
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("b excl after a closed: %v", err)
	}
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_UNLCK); err != nil {
		t.Fatalf("b unlock: %v", err)
	}
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_UNLCK); err != nil {
		t.Fatalf("b unlock again (no lock): %v", err)
	}
	c := openRW(t, name)
	defer c.Close()
	if err := ofdLk(c, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("c excl after b unlocked: %v", err)
	}
	if err := ofdLk(c, unix.F_OFD_SETLK, syscall.F_UNLCK); err != nil {
		t.Fatal(err)
	}
	// shared against shared: no conflict; exclusive against shared: conflict
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_RDLCK); err != nil {
		t.Fatalf("b shared: %v", err)
	}
	if err := ofdLk(c, unix.F_OFD_SETLK, syscall.F_RDLCK); err != nil {
		t.Fatalf("c shared vs b shared: %v", err)
	}
	d := openRW(t, name)
	defer d.Close()
	if err := ofdLk(d, unix.F_OFD_SETLK, syscall.F_WRLCK); err != syscall.EAGAIN {
		t.Fatalf("d excl vs shared: %v, want EAGAIN", err)
	}
}

// locks_ofd.go: a lock held through a description that is not the request's, with the fd
// closed only after the file's name is removed (the purger's order: Remove, then Close), is
// released by the close, and a new file at the same name is a new inode, unlocked.
func TestLocksOFDRemoveThenClose(t *testing.T) {
	name := extDir(t) + "/0.wal"
	a := openRW(t, name)
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatal(err)
	}
	if err := os.Remove(name); err != nil {
		t.Fatal(err)
	}
	b := openRW(t, name) // a new file
	defer b.Close()
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("new inode at the name: %v", err)
	}
	a.Close()
}

// locks_ofd.go: the same description re-locking: the same type succeeds (no change); a
// conversion succeeds too. (The model makes both stuck: etcd never re-locks a description.)
// A dup'd fd shares the description, so it does not conflict, and closing one of the two fds
// keeps the lock. (The model has no dup.)
func TestLocksOFDSameDescription(t *testing.T) {
	name := extDir(t) + "/LOCK"
	a := openRW(t, name)
	defer a.Close()
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatal(err)
	}
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("same type again: %v", err)
	}
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_RDLCK); err != nil {
		t.Fatalf("conversion: %v", err)
	}
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("conversion back: %v", err)
	}
	fd2, err := syscall.Dup(int(a.Fd()))
	if err != nil {
		t.Fatal(err)
	}
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	if err := syscall.FcntlFlock(uintptr(fd2), unix.F_OFD_SETLK, &lk); err != nil {
		t.Fatalf("dup'd fd: %v", err)
	}
	syscall.Close(fd2)
	b := openRW(t, name)
	defer b.Close()
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_WRLCK); err != syscall.EAGAIN {
		t.Fatalf("after closing the dup: %v, want EAGAIN (a still holds it)", err)
	}
}

// locks_ofd.go: what the model makes stuck is accepted by Linux or refused with EBADF/EINVAL:
// F_WRLCK on a read-only fd and F_RDLCK on a write-only fd: EBADF; l_pid not 0: EINVAL; a byte
// range: accepted (a range lock, not the whole file).
func TestLocksOFDMisuse(t *testing.T) {
	name := extDir(t) + "/LOCK"
	openRW(t, name).Close()
	r, _ := os.Open(name)
	defer r.Close()
	if err := ofdLk(r, unix.F_OFD_SETLK, syscall.F_WRLCK); err != syscall.EBADF {
		t.Fatalf("F_WRLCK on O_RDONLY: %v, want EBADF", err)
	}
	w, _ := os.OpenFile(name, os.O_WRONLY, 0)
	defer w.Close()
	if err := ofdLk(w, unix.F_OFD_SETLK, syscall.F_RDLCK); err != syscall.EBADF {
		t.Fatalf("F_RDLCK on O_WRONLY: %v, want EBADF", err)
	}
	lk := syscall.Flock_t{Type: syscall.F_WRLCK, Pid: 1}
	if err := syscall.FcntlFlock(w.Fd(), unix.F_OFD_SETLK, &lk); err != syscall.EINVAL {
		t.Fatalf("l_pid 1: %v, want EINVAL", err)
	}
	lk = syscall.Flock_t{Type: syscall.F_WRLCK, Start: 0, Len: 10}
	if err := syscall.FcntlFlock(w.Fd(), unix.F_OFD_SETLK, &lk); err != nil {
		t.Fatalf("range lock: %v", err)
	}
}

// locks_blocking.go: F_OFD_SETLKW waits while another description holds a conflicting lock and
// returns nil once that description's fd is closed (by another goroutine); signals delivered
// meanwhile (SIGURG preemption, and SIGUSR1 with a Go handler, which Go installs with
// SA_RESTART) do not make it return EINTR. The same for flock(LOCK_EX).
func TestLocksBlocking(t *testing.T) {
	sig := make(chan os.Signal, 64)
	signal.Notify(sig, syscall.SIGUSR1)
	defer signal.Stop(sig)
	for _, kind := range []string{"ofd", "flock"} {
		name := extDir(t) + "/LOCK"
		a, b := openRW(t, name), openRW(t, name)
		lockA := func(f *os.File, cmd int) error {
			if kind == "ofd" {
				return ofdLk(f, cmd, syscall.F_WRLCK)
			}
			how := syscall.LOCK_EX
			if cmd == unix.F_OFD_SETLK {
				how |= syscall.LOCK_NB
			}
			return syscall.Flock(int(f.Fd()), how)
		}
		if err := lockA(a, unix.F_OFD_SETLK); err != nil {
			t.Fatal(err)
		}
		done := make(chan error, 1)
		go func() { done <- lockA(b, unix.F_OFD_SETLKW) }()
		for i := 0; i < 20; i++ {
			syscall.Kill(syscall.Getpid(), syscall.SIGUSR1)
			time.Sleep(10 * time.Millisecond)
		}
		select {
		case err := <-done:
			t.Fatalf("%s: blocking lock returned %v while held", kind, err)
		default:
		}
		a.Close()
		select {
		case err := <-done:
			if err != nil {
				t.Fatalf("%s: blocking lock after release: %v", kind, err)
			}
		case <-time.After(5 * time.Second):
			t.Fatalf("%s: blocking lock still waiting after release", kind)
		}
		b.Close()
	}
}

// locks_flock.go: flock locks conflict between two descriptions of one process, LOCK_EX against
// LOCK_EX and LOCK_SH, LOCK_SH against LOCK_EX, not LOCK_SH against LOCK_SH; LOCK_NB's errno is
// EWOULDBLOCK; close of the holder's fd and LOCK_UN release; LOCK_UN with no lock succeeds;
// flock needs no access mode (a read-only fd takes LOCK_EX).
func TestLocksFlock(t *testing.T) {
	name := extDir(t) + "/LOCK"
	openRW(t, name).Close()
	a, _ := os.Open(name) // read-only
	b := openRW(t, name)
	defer b.Close()
	if err := syscall.Flock(int(a.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != nil {
		t.Fatalf("a LOCK_EX on O_RDONLY: %v", err)
	}
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != syscall.EWOULDBLOCK {
		t.Fatalf("b EX vs a EX: %v", err)
	}
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_SH|syscall.LOCK_NB); err != syscall.EWOULDBLOCK {
		t.Fatalf("b SH vs a EX: %v", err)
	}
	a.Close()
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != nil {
		t.Fatalf("b EX after a closed: %v", err)
	}
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_UN); err != nil {
		t.Fatal(err)
	}
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_UN); err != nil {
		t.Fatalf("LOCK_UN with no lock: %v", err)
	}
	c := openRW(t, name)
	defer c.Close()
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_SH|syscall.LOCK_NB); err != nil {
		t.Fatal(err)
	}
	if err := syscall.Flock(int(c.Fd()), syscall.LOCK_SH|syscall.LOCK_NB); err != nil {
		t.Fatalf("c SH vs b SH: %v", err)
	}
	d := openRW(t, name)
	defer d.Close()
	if err := syscall.Flock(int(d.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != syscall.EWOULDBLOCK {
		t.Fatalf("d EX vs SH: %v", err)
	}
	if err := syscall.Flock(int(d.Fd()), 0); err != syscall.EINVAL {
		t.Fatalf("how 0: %v, want EINVAL", err)
	}
}

// locks_flock_vs_ofd.go: flock locks and OFD locks are independent on C: an exclusive flock lock
// through one description and an exclusive OFD lock through another, on one file, both succeed;
// so do both kinds through one description.
func TestLocksFlockVsOFD(t *testing.T) {
	name := extDir(t) + "/LOCK"
	a, b := openRW(t, name), openRW(t, name)
	defer a.Close()
	defer b.Close()
	if err := syscall.Flock(int(a.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != nil {
		t.Fatal(err)
	}
	if err := ofdLk(b, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("OFD excl vs flock EX: %v", err)
	}
	if err := ofdLk(a, unix.F_OFD_SETLK, syscall.F_WRLCK); err != syscall.EAGAIN {
		t.Fatalf("a OFD vs b OFD: %v, want EAGAIN", err)
	}
	if err := syscall.Flock(int(b.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != syscall.EWOULDBLOCK {
		t.Fatalf("b flock vs a flock: %v, want EWOULDBLOCK", err)
	}
}

// locks_posix_not_modelled.go: classic POSIX record locks (F_SETLK) are per process: two opens
// in one process do not conflict, and closing any fd of the file releases the process's lock.
// So they are not the OFD semantics, and the model does not give them a meaning.
func TestLocksPosixPerProcess(t *testing.T) {
	name := extDir(t) + "/LOCK"
	a, b := openRW(t, name), openRW(t, name)
	defer b.Close()
	if err := ofdLk(a, syscall.F_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatal(err)
	}
	if err := ofdLk(b, syscall.F_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("F_SETLK in one process: %v, want nil", err)
	}
	// an OFD lock conflicts with the process's POSIX lock
	c := openRW(t, name)
	defer c.Close()
	if err := ofdLk(c, unix.F_OFD_SETLK, syscall.F_WRLCK); err != syscall.EAGAIN {
		t.Fatalf("OFD vs POSIX: %v, want EAGAIN", err)
	}
	a.Close() // releases the process's POSIX lock on the file, b's included
	if err := ofdLk(c, unix.F_OFD_SETLK, syscall.F_WRLCK); err != nil {
		t.Fatalf("OFD after closing a: %v, want nil", err)
	}
}

// locks_mmap_close.go: a live mapping keeps its description, and its OFD and flock locks, after
// the fd's close; the locks go with the last mapping made through it. For each kind: a locks
// exclusively, maps the file twice, closes; b's non-blocking exclusive request gets EAGAIN while a
// mapping is live (after one munmap too) and succeeds after the second. Without a mapping (the
// control), b's request succeeds right after the close.
func TestLocksMmapKeepsDescription(t *testing.T) {
	name := extDir(t) + "/f"
	if err := os.WriteFile(name, []byte("hello"), 0o600); err != nil {
		t.Fatal(err)
	}
	type kind struct {
		name   string
		lock   func(*os.File) error
		unlock func(*os.File) error
	}
	kinds := []kind{
		{"ofd", func(f *os.File) error { return ofdLk(f, unix.F_OFD_SETLK, syscall.F_WRLCK) },
			func(f *os.File) error { return ofdLk(f, unix.F_OFD_SETLK, syscall.F_UNLCK) }},
		{"flock", func(f *os.File) error { return syscall.Flock(int(f.Fd()), syscall.LOCK_EX|syscall.LOCK_NB) },
			func(f *os.File) error { return syscall.Flock(int(f.Fd()), syscall.LOCK_UN) }},
	}
	for _, k := range kinds {
		for _, nmaps := range []int{0, 1, 2} {
			a := openRW(t, name)
			if err := k.lock(a); err != nil {
				t.Fatalf("%s: a's lock: %v", k.name, err)
			}
			var ms [][]byte
			for i := 0; i < nmaps; i++ {
				m, err := syscall.Mmap(int(a.Fd()), 0, 5, syscall.PROT_READ, syscall.MAP_SHARED)
				if err != nil {
					t.Fatalf("%s: mmap: %v", k.name, err)
				}
				ms = append(ms, m)
			}
			if err := a.Close(); err != nil {
				t.Fatalf("%s: close: %v", k.name, err)
			}
			b := openRW(t, name)
			for i := 0; i < nmaps; i++ {
				if err := k.lock(b); err != syscall.EAGAIN {
					t.Fatalf("%s, %d maps, %d unmapped: b's lock: %v, want EAGAIN", k.name, nmaps, i, err)
				}
				if string(ms[i]) != "hello" {
					t.Fatalf("%s: mapping reads %q", k.name, ms[i])
				}
				if err := syscall.Munmap(ms[i]); err != nil {
					t.Fatalf("%s: munmap: %v", k.name, err)
				}
			}
			if err := k.lock(b); err != nil {
				t.Fatalf("%s, %d maps, all unmapped: b's lock: %v, want nil", k.name, nmaps, err)
			}
			if err := k.unlock(b); err != nil {
				t.Fatal(err)
			}
			b.Close()
		}
	}
}

// locks_spurious_eagain.go: a non-blocking request may get EAGAIN although the process holds no
// other fd or mapping of the file, while another process reads /proc/<pid>/fdinfo/<fd> of the fd
// it closed (the reader's reference keeps the description, and its lock, alive past close(2)).
// For each kind: a locks exclusively (non-blocking) and closes; b, a fresh open, asks for the same
// lock, non-blocking. With the reader (a child process: this test binary, as
// TestLocksProcReaderHelper), some round's b gets EAGAIN; at most 200000 rounds per kind. The
// control (no reader) is only logged: the claim is that EAGAIN happens, not how often.
func TestLocksProcReaderEagain(t *testing.T) {
	if os.Getenv("LOCKS_PROC_READER") != "" {
		t.Skip("helper's own run")
	}
	name := extDir(t) + "/f"
	if err := os.WriteFile(name, []byte("x"), 0o600); err != nil {
		t.Fatal(err)
	}
	type kind struct {
		name string
		lock func(int) error
	}
	kinds := []kind{
		{"ofd", func(fd int) error {
			lk := syscall.Flock_t{Type: syscall.F_WRLCK}
			return syscall.FcntlFlock(uintptr(fd), unix.F_OFD_SETLK, &lk)
		}},
		{"flock", func(fd int) error { return syscall.Flock(fd, syscall.LOCK_EX|syscall.LOCK_NB) }},
	}
	// rounds runs up to n rounds, stopping at the first EAGAIN when stop; it returns the count.
	rounds := func(k kind, n int, stop bool) (eagain, done int) {
		for i := 0; i < n; i++ {
			a, err := syscall.Open(name, syscall.O_RDWR|syscall.O_CLOEXEC, 0)
			if err != nil {
				t.Fatal(err)
			}
			if err := k.lock(a); err != nil {
				// the previous round's b, or a lingering description: try again
				syscall.Close(a)
				continue
			}
			if err := syscall.Close(a); err != nil {
				t.Fatal(err)
			}
			b, err := syscall.Open(name, syscall.O_RDWR|syscall.O_CLOEXEC, 0)
			if err != nil {
				t.Fatal(err)
			}
			err = k.lock(b)
			syscall.Close(b)
			done++
			switch err {
			case nil:
			case syscall.EAGAIN:
				eagain++
				if stop {
					return
				}
			default:
				t.Fatalf("%s: b's lock: %v", k.name, err)
			}
		}
		return
	}
	// the fd number a gets each round: the lowest free one
	fd0, err := syscall.Open(name, syscall.O_RDWR|syscall.O_CLOEXEC, 0)
	if err != nil {
		t.Fatal(err)
	}
	syscall.Close(fd0)
	for _, k := range kinds {
		e, n := rounds(k, 5000, false)
		t.Logf("%s, no reader: EAGAIN in %d of %d rounds", k.name, e, n)
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestLocksProcReaderHelper$", "-test.count=1")
	cmd.Env = append(os.Environ(), fmt.Sprintf("LOCKS_PROC_READER=/proc/%d/fdinfo/%d", os.Getpid(), fd0))
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	defer func() { cmd.Process.Kill(); cmd.Wait() }()
	time.Sleep(300 * time.Millisecond)
	for _, k := range kinds {
		e, n := rounds(k, 200000, true)
		if e == 0 {
			t.Fatalf("%s, with the reader: no EAGAIN in %d rounds", k.name, n)
		}
		t.Logf("%s, with the reader: EAGAIN after %d rounds (a closed, no mapping)", k.name, n)
	}
}

// The reader of TestLocksProcReaderEagain (runs only with LOCKS_PROC_READER set): 8 goroutines
// open, read and close the fdinfo file, forever.
func TestLocksProcReaderHelper(t *testing.T) {
	path := os.Getenv("LOCKS_PROC_READER")
	if path == "" {
		t.Skip("helper")
	}
	buf := make([]byte, 4096)
	for k := 0; k < 8; k++ {
		go func() {
			for {
				fd, err := syscall.Open(path, syscall.O_RDONLY, 0)
				if err != nil {
					continue
				}
				syscall.Read(fd, buf)
				syscall.Close(fd)
			}
		}()
	}
	select {}
}
