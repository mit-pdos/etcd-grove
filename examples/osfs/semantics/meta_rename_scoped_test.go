//go:build linux

package semantics

// Measurement behind the proposed scoping of the Rename step's stuck clause
// (WAL link L4, notes/wal-link-l4-fsext.md; approved 2026-11-17): a rename of a directory in one
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
	"math/rand"
	"os"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"testing"
	"time"
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

func renameScopedWorker(b string, w int, cont func(i int) bool, seqs *atomic.Int64, errs chan<- error) {
	d := fmt.Sprintf("%s/w%d", b, w)
	fail := func(step string, err error) {
		errs <- fmt.Errorf("worker %d: %s: %v", w, step, err)
	}
	for i := 0; cont(i); i++ {
		seqs.Add(1)
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
	// Root B's workers run at least iters sequences each, and go on until root A has made
	// minRenames directory renames (root A fsyncs its directory each round, which on C's ext4 is
	// much slower than B's sequences: 2026-11-20's run on C saw 26 renames while B ran 3000
	// sequences), within a time budget.
	const workers, iters, minRenames = 4, 3000, 400
	const budget = 2 * time.Minute
	errs := make(chan error, workers+1)
	var stop atomic.Bool
	var renames, seqs atomic.Int64
	start := time.Now()
	cont := func(i int) bool {
		return i < iters || (renames.Load() < minRenames && time.Since(start) < budget)
	}
	var wa sync.WaitGroup
	wa.Add(1)
	go func() { defer wa.Done(); renameScopedRootA(t, a, &stop, &renames, errs) }()
	var wb sync.WaitGroup
	for w := 0; w < workers; w++ {
		wb.Add(1)
		go func(w int) { defer wb.Done(); renameScopedWorker(b, w, cont, &seqs, errs) }(w)
	}
	wb.Wait()
	stop.Store(true)
	wa.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
	t.Logf("root A: %d directory renames; root B: %d workers, %d sequences in all (%d path calls each), %v",
		renames.Load(), workers, seqs.Load(), 15, time.Since(start).Round(time.Millisecond))
	if renames.Load() < minRenames {
		t.Fatalf("too few renames in root A (%d, want %d within %v) to have raced root B",
			renames.Load(), minRenames, budget)
	}
}

// TestCrossRootRenameExcluded (the excluded case: meta_rename_cross_root.go;
// found by the independent attack on the L4 text, 2026-11-17): a rename whose
// source is in root C and whose target is in root A walks the target's path
// in A, so it races A's directory renames as a call of A would. Root A moves
// p away and moves q into it (A/p/<chain>/q never exists in any tree of the
// log); C's rename(C/f, A/p/<chain>/q/g) still succeeds sometimes, with g
// found at A/z/<chain>/q/g: an outcome no single tree gives. The proposed rule
// therefore makes Rename stuck unless its source and target are in one root's
// tree (SameRoot s t). The test reports the count; it fails only if the setup
// fails. The attack measured 296 of 20000 at depth 1900 on ext4.
// L4_CROSS_ITERS (default 2000) and L4_CROSS_DEPTH (default 1900) tune it;
// L4_CROSS_EXPECT=1 (the configuration-C run) asserts a positive count.
func TestCrossRootRenameExcluded(t *testing.T) {
	base := extDir(t)
	a, c := base+"/A", base+"/C"
	n, iters := 1900, 2000
	if v, err := strconv.Atoi(os.Getenv("L4_CROSS_DEPTH")); err == nil {
		n = v
	}
	if v, err := strconv.Atoi(os.Getenv("L4_CROSS_ITERS")); err == nil {
		iters = v
	}
	chain := strings.Repeat("/s", n)
	must := func(err error) {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
	}
	must(os.MkdirAll(a+"/p"+chain, 0o755))
	must(os.MkdirAll(a+"/w/q", 0o755))
	must(os.MkdirAll(c, 0o755))
	f, err := os.Create(c + "/f")
	must(err)
	f.Close()
	hits := 0
	for i := 0; i < iters; i++ {
		var wg sync.WaitGroup
		start := make(chan struct{})
		var r2 error
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-start
			r2 = syscall.Rename(c+"/f", a+"/p"+chain+"/q/g")
		}()
		close(start)
		for j, d := 0, rand.Intn(4000); j < d; j++ {
		}
		must(syscall.Rename(a+"/p", a+"/z"))
		must(syscall.Rename(a+"/w/q", a+"/z"+chain+"/q"))
		wg.Wait()
		if r2 == nil {
			hits++
			if _, err := os.Stat(a + "/z" + chain + "/q/g"); err != nil {
				t.Fatalf("success but g not at A/z/.../q/g: %v", err)
			}
			must(syscall.Rename(a+"/z"+chain+"/q/g", c+"/f"))
		}
		must(syscall.Rename(a+"/z"+chain+"/q", a+"/w/q"))
		must(syscall.Rename(a+"/z", a+"/p"))
	}
	t.Logf("cross-root rename racing root A's directory renames: %d of %d succeeded at a path no tree had (depth %d)",
		hits, iters, n)
	if os.Getenv("L4_CROSS_EXPECT") == "1" && hits == 0 {
		t.Errorf("L4_CROSS_EXPECT=1: no impossible success in %d iterations at depth %d", iters, n)
	}
}
