// Command snapdbcrash drives the received-snapshot save of etcd's fork (e94f33b50,
// server/etcdserver/api/snap/db.go SaveDBFrom: a temporary file written and fsynced, linked
// under <k>.snap.db, the temporary removed, the directory fsynced), followed by the raft loop's
// SaveSnap of k (a record appended to a WAL file in another directory and fdatasynced), and the
// release of old .snap.db files (os.Remove without a directory sync, as ReleaseSnapDBs), on
// configuration C. Each step is logged to LOG (outside the crashing device) so that a power
// loss's image can be checked (snapdb-crash.sh):
//
//   - every <k>.snap.db present holds exactly the bytes written for k (never torn or partial);
//   - every k whose directory sync returned (SYNCED), or whose WAL record is on disk, and that was
//     not released (REL) has its <k>.snap.db present.
//
//	snapdbcrash setup DIR
//	snapdbcrash run DIR LOG
//	snapdbcrash check DIR LOG
package main

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"math/rand"
	"os"
	"path/filepath"
	"strconv"
	"strings"
)

func must(err error) {
	if err != nil {
		panic(err)
	}
}

// content is the file saved for index k: a size and bytes from a PRNG seeded by k.
func content(k int) []byte {
	r := rand.New(rand.NewSource(int64(k)))
	n := 64<<10 + r.Intn(6<<20)
	b := make([]byte, n)
	r.Read(b)
	return b
}

func name(dir string, k int) string { return filepath.Join(dir, fmt.Sprintf("%016x.snap.db", k)) }

func fsyncDir(dir string) {
	d, err := os.Open(dir)
	must(err)
	must(d.Sync())
	must(d.Close())
}

func run(dir, logPath string) {
	snap := filepath.Join(dir, "snap")
	lf, err := os.OpenFile(logPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	must(err)
	logf := func(f string, a ...any) { fmt.Fprintf(lf, f+"\n", a...); lf.Sync() }
	wal, err := os.OpenFile(filepath.Join(dir, "wal", "w"), os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	must(err)
	for k := 1; ; k++ {
		// SaveDBFrom(k)
		f, err := os.CreateTemp(snap, "tmp")
		must(err)
		_, err = io.Copy(f, bytes.NewReader(content(k)))
		must(err)
		must(f.Sync())
		must(f.Close())
		logf("LINK %d", k)
		must(os.Link(f.Name(), name(snap, k)))
		must(os.Remove(f.Name()))
		fsyncDir(snap)
		logf("SYNCED %d", k)
		// the raft loop's SaveSnap(k): a WAL record, fdatasynced
		_, err = wal.Write([]byte(fmt.Sprintf("%08d\n", k)))
		must(err)
		must(wal.Sync())
		logf("WAL %d", k)
		// ReleaseSnapDBs: remove the files two or more below k, no directory sync
		if k > 2 {
			logf("REL %d", k-2)
			must(os.Remove(name(snap, k-2)))
		}
	}
}

func check(dir, logPath string) {
	snap := filepath.Join(dir, "snap")
	synced, rel := map[int]bool{}, map[int]bool{}
	lf, err := os.Open(logPath)
	must(err)
	sc := bufio.NewScanner(lf)
	last := 0
	for sc.Scan() {
		fs := strings.Fields(sc.Text())
		if len(fs) != 2 {
			continue
		}
		k, _ := strconv.Atoi(fs[1])
		switch fs[0] {
		case "SYNCED":
			synced[k] = true
		case "REL":
			rel[k] = true
		case "LINK":
			last = k
		}
	}
	walRecs := map[int]bool{}
	if b, err := os.ReadFile(filepath.Join(dir, "wal", "w")); err == nil {
		for _, l := range strings.Split(string(b), "\n") {
			if k, err := strconv.Atoi(strings.TrimLeft(l, "\x00")); err == nil && len(l) == 8 {
				walRecs[k] = true
			}
		}
	}
	ents, err := os.ReadDir(snap)
	must(err)
	bad := []string{}
	present := map[int]bool{}
	ntmp := 0
	for _, e := range ents {
		n := e.Name()
		if strings.HasPrefix(n, "tmp") {
			ntmp++
			continue
		}
		k64, err := strconv.ParseInt(strings.TrimSuffix(n, ".snap.db"), 16, 64)
		if err != nil {
			bad = append(bad, "unexpected "+n)
			continue
		}
		k := int(k64)
		present[k] = true
		b, err := os.ReadFile(filepath.Join(snap, n))
		must(err)
		if !bytes.Equal(b, content(k)) {
			bad = append(bad, fmt.Sprintf("torn %d (len %d want %d)", k, len(b), len(content(k))))
		}
	}
	for k := 1; k <= last; k++ {
		if (synced[k] || walRecs[k]) && !rel[k] && !present[k] {
			bad = append(bad, fmt.Sprintf("missing %d (synced %v wal %v)", k, synced[k], walRecs[k]))
		}
	}
	var ks []int
	for k := range present {
		ks = append(ks, k)
	}
	status := "ok"
	if len(bad) > 0 {
		status = "BAD " + strings.Join(bad, "; ")
	}
	fmt.Printf("%s last-link=%d present=%v tmp=%d wal-max=%d\n", status, last, sortInts(ks), ntmp, maxKey(walRecs))
}

func sortInts(a []int) []int {
	for i := range a {
		for j := i + 1; j < len(a); j++ {
			if a[j] < a[i] {
				a[i], a[j] = a[j], a[i]
			}
		}
	}
	return a
}

func maxKey(m map[int]bool) int {
	x := 0
	for k := range m {
		if k > x {
			x = k
		}
	}
	return x
}

func main() {
	switch os.Args[1] {
	case "setup":
		must(os.MkdirAll(filepath.Join(os.Args[2], "snap"), 0755))
		must(os.MkdirAll(filepath.Join(os.Args[2], "wal"), 0755))
	case "run":
		run(os.Args[2], os.Args[3])
	case "check":
		check(os.Args[2], os.Args[3])
	}
}
