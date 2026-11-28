//go:build linux

package semantics

// Measurements behind the link(2) examples (meta_link_no_replace.go,
// meta_link_shared_inode.go): what os.Link does to an existing name, under a
// race of two links to one name, and to the inode it names. Run on C by
// run-models-on-c.sh ($SEMANTICS_C_DIR); the crash states (meta_link_crash.go)
// are measured by notes/axiom-review/fs-link/.

import (
	"bytes"
	"errors"
	"fmt"
	"os"
	"sync"
	"syscall"
	"testing"
)

func linkWriteSynced(t *testing.T, path string, b []byte) {
	t.Helper()
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE|os.O_EXCL, 0o666)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := f.Write(b); err != nil {
		t.Fatal(err)
	}
	if err := f.Sync(); err != nil {
		t.Fatal(err)
	}
	f.Close()
}

func linkIno(t *testing.T, path string) (ino uint64, nlink uint64) {
	t.Helper()
	var st syscall.Stat_t
	if err := syscall.Stat(path, &st); err != nil {
		t.Fatal(err)
	}
	return st.Ino, uint64(st.Nlink)
}

// meta_link_no_replace.go, sequential: a link onto an existing name fails with
// EEXIST (os.ErrExist) and leaves that name's file, its inode and its bytes.
func TestLinkNeverReplaces(t *testing.T) {
	d := extDir(t)
	linkWriteSynced(t, d+"/tmp1", []byte("new"))
	linkWriteSynced(t, d+"/0000000000000005.snap.db", []byte("old"))
	ino0, _ := linkIno(t, d+"/0000000000000005.snap.db")
	err := os.Link(d+"/tmp1", d+"/0000000000000005.snap.db")
	if !errors.Is(err, os.ErrExist) {
		t.Fatalf("Link onto an existing name: %v, want ErrExist", err)
	}
	var le *os.LinkError
	if !errors.As(err, &le) || le.Err != syscall.EEXIST {
		t.Fatalf("Link onto an existing name: %#v, want a *LinkError with EEXIST", err)
	}
	ino1, n := linkIno(t, d+"/0000000000000005.snap.db")
	got, _ := os.ReadFile(d + "/0000000000000005.snap.db")
	if ino1 != ino0 || n != 1 || !bytes.Equal(got, []byte("old")) {
		t.Fatalf("after the failed link: ino %d (was %d), nlink %d, %q", ino1, ino0, n, got)
	}
	if _, nt := linkIno(t, d+"/tmp1"); nt != 1 {
		t.Fatalf("the source's nlink after a failed link: %d", nt)
	}
}

// meta_link_no_replace.go, racing: two saves of one index link their own
// synced temporary files to the same name at once. In every round exactly one
// link succeeds, the other fails with EEXIST, and the name holds the winner's
// inode and bytes.
func TestLinkRaceOneWins(t *testing.T) {
	d := extDir(t)
	const rounds = 5000
	wins := [2]int{}
	for r := 0; r < rounds; r++ {
		fn := fmt.Sprintf("%s/%016x.snap.db", d, r)
		var tmp [2]string
		var ino [2]uint64
		for k := 0; k < 2; k++ {
			tmp[k] = fmt.Sprintf("%s/tmp%d-%d", d, r, k)
			f, err := os.OpenFile(tmp[k], os.O_RDWR|os.O_CREATE|os.O_EXCL, 0o666)
			if err != nil {
				t.Fatal(err)
			}
			f.Write([]byte{byte('a' + k)})
			f.Close() // no fsync: the race is about names, not durability
			ino[k], _ = linkIno(t, tmp[k])
		}
		var errs [2]error
		var start, wg sync.WaitGroup
		start.Add(1)
		for k := 0; k < 2; k++ {
			wg.Add(1)
			go func(k int) {
				defer wg.Done()
				start.Wait()
				errs[k] = os.Link(tmp[k], fn)
			}(k)
		}
		start.Done()
		wg.Wait()
		w := -1
		for k := 0; k < 2; k++ {
			switch {
			case errs[k] == nil:
				if w != -1 {
					t.Fatalf("round %d: both links succeeded", r)
				}
				w = k
			case !errors.Is(errs[k], os.ErrExist):
				t.Fatalf("round %d: link %d: %v", r, k, errs[k])
			}
		}
		if w == -1 {
			t.Fatalf("round %d: both links failed: %v, %v", r, errs[0], errs[1])
		}
		wins[w]++
		got, _ := os.ReadFile(fn)
		gi, n := linkIno(t, fn)
		if gi != ino[w] || n != 2 || !bytes.Equal(got, []byte{byte('a' + w)}) {
			t.Fatalf("round %d: %s is ino %d nlink %d %q; the winner's is ino %d", r, fn, gi, n, got, ino[w])
		}
		for k := 0; k < 2; k++ {
			os.Remove(tmp[k])
		}
		os.Remove(fn)
	}
	t.Logf("%d rounds: first link won %d, second %d; never both, never neither", rounds, wins[0], wins[1])
}

// meta_link_shared_inode.go, live: after the link both names are one inode
// (nlink 2) with the synced bytes; after the removal of the temporary name the
// file keeps them (nlink 1).
func TestLinkSharedInode(t *testing.T) {
	d := extDir(t)
	data := bytes.Repeat([]byte("snapshot"), 1024)
	linkWriteSynced(t, d+"/tmp7", data)
	fn := d + "/0000000000000007.snap.db"
	if err := os.Link(d+"/tmp7", fn); err != nil {
		t.Fatal(err)
	}
	i0, n0 := linkIno(t, d+"/tmp7")
	i1, n1 := linkIno(t, fn)
	if i0 != i1 || n0 != 2 || n1 != 2 {
		t.Fatalf("after link: tmp ino %d nlink %d, fn ino %d nlink %d", i0, n0, i1, n1)
	}
	if err := os.Remove(d + "/tmp7"); err != nil {
		t.Fatal(err)
	}
	i2, n2 := linkIno(t, fn)
	got, _ := os.ReadFile(fn)
	if i2 != i1 || n2 != 1 || !bytes.Equal(got, data) {
		t.Fatalf("after removing tmp: ino %d nlink %d, %d bytes", i2, n2, len(got))
	}
}
