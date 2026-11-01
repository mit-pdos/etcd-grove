package bboltfs

import (
	"os"
	"os/exec"
	"strings"
	"sync/atomic"
	"syscall"
	"testing"
	"unsafe"

	"golang.org/x/sys/unix"
)

// The Linux facts the model of notes/osfs-ext-plan.md rests on, where they are
// not obvious. The everyday ones (EBADF on a closed fd, EINVAL for a bad mmap)
// are not tested: the model is stuck on misuse whatever Linux answers.

// mappedFile is a 4-page file mapped over 8 pages: pages 4-7 are past EOF.
func mappedFile(dir string) []byte {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		panic(err)
	}
	if err := f.Truncate(4 * pageSize); err != nil {
		panic(err)
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 8*pageSize, syscall.PROT_READ, syscall.MAP_SHARED)
	if err != nil {
		panic(err)
	}
	return b
}

// The facts that kill the process, run in a re-executed child (TestMain).
var facts = map[string]func(string) bool{
	// A store to a PROT_READ mapping. The model lets it succeed: on Linux it is
	// fatal ("Mappings are not read-only in the model").
	"store": func(dir string) bool {
		b := mappedFile(dir)
		b[0] = 7
		return true
	},
	// A CAS whose compare fails, on a PROT_READ mapping: LOCK CMPXCHG writes
	// whether or not the compare succeeds, so it is fatal too.
	"cas": func(dir string) bool {
		b := mappedFile(dir)
		return !atomic.CompareAndSwapUint64((*uint64)(unsafe.Pointer(&b[0])), 1, 2)
	},
	// A load from a mapped page wholly past EOF. The model's cell is a hole
	// (the load is stuck).
	"pastEOF": func(dir string) bool {
		b := mappedFile(dir)
		return b[5*pageSize] == 0
	},
}

// Each fact dies of its signal, as a fatal error ("unexpected fault address"),
// not a panic: no recover can catch it.
func TestFatalFaults(t *testing.T) {
	for name, sig := range map[string]string{"store": "SIGSEGV", "cas": "SIGSEGV", "pastEOF": "SIGBUS"} {
		t.Run(name, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^$")
			cmd.Env = append(os.Environ(), "BBOLTFS_HELPER="+name, "BBOLTFS_DIR="+t.TempDir())
			out, err := cmd.CombinedOutput()
			if err == nil {
				t.Fatalf("%s did not die: %s", name, out)
			}
			// under -race the CAS faults inside the race runtime, whose report
			// is a garbled "SIGSEGV: segmentation violation"
			if !strings.Contains(string(out), sig) ||
				!strings.Contains(string(out), "fault") && !strings.Contains(string(out), "segmentation") {
				t.Fatalf("%s: want a fatal %s, got %v:\n%s", name, sig, err, out)
			}
			if strings.Contains(string(out), "panic:") {
				t.Fatalf("%s: a panic, not a fatal error:\n%s", name, out)
			}
		})
	}
}

// A WriteAt is visible at once through a MAP_SHARED mapping, without a sync:
// the mapping shows the page cache (the model's render).
func TestWriteVisibleInMapping(t *testing.T) {
	dir := t.TempDir()
	b := mappedFile(dir)
	defer unix.Munmap(b)
	f, err := os.OpenFile(dir+"/db", os.O_RDWR, 0)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	if _, err := f.WriteAt([]byte{9, 8, 7}, pageSize+1); err != nil {
		t.Fatal(err)
	}
	if b[pageSize+1] != 9 || b[pageSize+2] != 8 || b[pageSize+3] != 7 {
		t.Fatalf("mapping shows %v", b[pageSize+1:pageSize+4])
	}
}
