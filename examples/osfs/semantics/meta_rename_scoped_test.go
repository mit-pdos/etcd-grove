//go:build linux

package semantics

// Measurement behind the proposed scoping of the Rename step's stuck clause
// (WAL link L4, notes/wal-link-l4-fsext.md): a rename of a directory in one
// root's tree, racing path calls whose paths are in another root's tree, never
// changes what those calls see. Each worker of root B runs a fixed sequence of
// path calls on its own subdirectory (deep paths, file and directory renames,
// creates, removes, stats) and checks every result against the sequential
// outcome; meanwhile root A's thread renames directories as wal.Create does
// (mkdir a temporary directory, fill it, rename it over the target, fsync the
// parent) and moves directories between subdirectories of A, so that
// rename_lock and s_vfs_rename_mutex are taken all the time.

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"sync"
	"sync/atomic"
	"syscall"
	"testing"
)

func renameScopedRootA(t *testing.T, a string, stop *atomic.Bool, renames *atomic.Int64, errs chan<- error) {
	t.Helper()
	if err := os.MkdirAll(a+"/p/q", 0o755); err != nil {
		errs <- err
		return
	}
	if err := os.Mkdir(a+"/x", 0o755); err != nil {
		errs <- err
		return
	}
	for i := 0; !stop.Load(); i++ {
		tmp := fmt.Sprintf("%s/wal.tmp", a)
		dst := fmt.Sprintf("%s/wal", a)
		if err := os.Mkdir(tmp, 0o755); err != nil {
			errs <- err
			return
		}
		f, err := os.Create(tmp + "/0000000000000000-0000000000000000.wal")
		if err != nil {
			errs <- err
			return
		}
		f.Close()
		os.RemoveAll(dst)
		if err := os.Rename(tmp, dst); err != nil { // wal.Create's directory swap
			errs <- err
			return
		}
		if d, err := os.Open(a); err == nil {
			d.Sync()
			d.Close()
		}
		// a cross-directory move of a directory (s_vfs_rename_mutex, rename_lock)
		src, tgt := a+"/p/q", a+"/x/q"
		if i%2 == 1 {
			src, tgt = tgt, src
		}
		if err := os.Rename(src, tgt); err != nil {
			errs <- err
			return
		}
		renames.Add(2)
	}
}

func renameScopedWorker(b string, w int, iters int, errs chan<- error) {
	d := fmt.Sprintf("%s/w%d", b, w)
	fail := func(step string, err error) {
		errs <- fmt.Errorf("worker %d: %s: %v", w, step, err)
	}
	for i := 0; i < iters; i++ {
		deep := d + "/m/n/o"
		if err := os.MkdirAll(deep, 0o755); err != nil {
			fail("mkdirall", err)
			return
		}
		f, err := os.OpenFile(deep+"/f", os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0o644)
		if err != nil {
			fail("create", err)
			return
		}
		if _, err := f.Write([]byte("x")); err != nil {
			fail("write", err)
			return
		}
		f.Close()
		if st, err := os.Lstat(deep + "/f"); err != nil || st.Size() != 1 {
			fail("lstat", fmt.Errorf("%v %v", st, err))
			return
		}
		if err := os.Rename(deep+"/f", deep+"/g"); err != nil { // a file rename in B
			fail("rename file", err)
			return
		}
		if _, err := os.Lstat(deep + "/f"); !errors.Is(err, fs.ErrNotExist) {
			fail("lstat after rename", err)
			return
		}
		if err := os.Rename(d+"/m/n", d+"/m/k"); err != nil { // a directory rename in B itself
			fail("rename dir", err)
			return
		}
		g, err := os.Open(d + "/m/k/o/g")
		if err != nil {
			fail("open moved", err)
			return
		}
		g.Close()
		if err := os.Remove(d + "/m/k/o/g"); err != nil {
			fail("remove", err)
			return
		}
		if err := os.Remove(d + "/m/k/o"); err != nil {
			fail("rmdir o", err)
			return
		}
		if err := os.Remove(d + "/m/k"); err != nil {
			fail("rmdir k", err)
			return
		}
		if err := os.Mkdir(d+"/m", 0o755); !errors.Is(err, fs.ErrExist) {
			fail("mkdir existing", err)
			return
		}
		if err := os.Remove(d + "/m"); err != nil {
			fail("rmdir m", err)
			return
		}
		if _, err := os.Lstat(d + "/m"); !errors.Is(err, fs.ErrNotExist) {
			fail("lstat removed", err)
			return
		}
		if err := syscall.Rmdir(d + "/m"); err != syscall.ENOENT {
			fail("rmdir missing", err)
			return
		}
	}
}

// TestDirRenameScopedToRoot: no path call of root B's workers ever sees
// anything but its sequential outcome while root A's directories are renamed.
func TestDirRenameScopedToRoot(t *testing.T) {
	base := extDir(t)
	a, b := base+"/rootA", base+"/rootB"
	for _, r := range []string{a, b} {
		if err := os.Mkdir(r, 0o755); err != nil {
			t.Fatal(err)
		}
	}
	const workers, iters = 4, 3000
	errs := make(chan error, workers+1)
	var stop atomic.Bool
	var renames atomic.Int64
	var wa sync.WaitGroup
	wa.Add(1)
	go func() { defer wa.Done(); renameScopedRootA(t, a, &stop, &renames, errs) }()
	var wb sync.WaitGroup
	for w := 0; w < workers; w++ {
		wb.Add(1)
		go func(w int) { defer wb.Done(); renameScopedWorker(b, w, iters, errs) }(w)
	}
	wb.Wait()
	stop.Store(true)
	wa.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
	t.Logf("root A: %d directory renames; root B: %d workers x %d sequences (%d path calls each)",
		renames.Load(), workers, iters, 15)
	if renames.Load() < 100 {
		t.Fatalf("too few renames in root A (%d) to have raced root B", renames.Load())
	}
}
