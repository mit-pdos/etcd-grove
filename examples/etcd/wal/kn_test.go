package wal

// The K-N regression tests (W3b): a member killed between a directory operation and the fsync
// that makes it durable restarts without a reboot (the page cache kept), finds the operation done,
// acknowledges a synced Save, and loses power before anything else syncs the directory. Three
// sites (K-N1..K-N3):
//   - mkdir: the first start killed after TouchDirAll's mkdir of data/, before it syncs the parent;
//     the restart's TouchDirAll finds data/ and returns without the sync (fixed by F-N4 part 1);
//   - create: killed after Create's rename of wal.tmp to wal, before it syncs member/; the restart
//     opens the WAL (fixed by F-N4 part 2: ReadAll in write mode syncs the WAL directory's parent);
//   - cut: killed after a cut's rename of N.tmp to seq-index.wal, before it syncs the WAL
//     directory; the restart reads and appends to the new segment (F-N4 part 2: ReadAll syncs the
//     WAL directory).
//
// Each test fails if the restart after the power loss reads less than the restart on the page
// cache acknowledged (posix: every directory as of its last fsync; ordered: the journal).
//
//	go test ./etcd/wal -run TestKillThenPowerKN -v

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	etcdwal "go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3/raftpb"

	"github.com/mit-pdos/etcd-grove/examples/etcd/wal/crashtest/crashsim"
)

// knStart is bootstrap's WAL path: the restart read if the WAL exists, else the first start
// (TouchDirAll of data/ and member/, Create). It returns the open WAL and the last index read,
// or nil and a word for the outcome.
func knStart(lg *zap.Logger, root string) (*etcdwal.WAL, uint64, string) {
	dir := root + "/data/member/wal"
	if !etcdwal.Exist(dir) {
		if fileutil.TouchDirAll(lg, root+"/data") != nil || fileutil.TouchDirAll(lg, root+"/data/member") != nil {
			return nil, 0, "TOUCHDIR fail"
		}
		w, err := etcdwal.Create(lg, dir, []byte("m"))
		if err != nil {
			return nil, 0, "CREATE fail"
		}
		return w, 0, "created"
	}
	st, c, w := restartRead(lg, dir, nil)
	if st != readOK {
		return nil, 0, "READ fail"
	}
	last := c.baseIdx
	for _, e := range c.ents {
		last = e.index
	}
	return w, last, "read"
}

// knChild: step 1 is the first start, saving synced entries (site cut: 1000-byte entries in
// 4 KiB segments, so that it cuts); the driver kills it right after the site's directory
// operation. Step 2 restarts (or starts) on the kill image, saves one more synced entry and
// prints what it acknowledged; step 3 restarts after the power loss and prints what it read.
func knChild(root, site, step string) {
	lg := zap.NewNop()
	switch step {
	case "1":
		if site == "cut" {
			etcdwal.SegmentSizeBytes = 4096
		}
		w, _, how := knStart(lg, root)
		if w == nil {
			fmt.Println(how)
			return
		}
		for i := uint64(1); i <= 6; i++ {
			e := entry{index: i, term: 1, size: 1000, salt: i}
			if w.Save(toHS(hardState{term: 1, vote: 1, commit: i}), []*raftpb.Entry{toRaft(e)}) != nil {
				fmt.Println("SAVE fail")
				return
			}
		}
		w.Close()
	case "2":
		w, last, how := knStart(lg, root)
		if w == nil {
			fmt.Println(how)
			return
		}
		e := entry{index: last + 1, term: 1, size: 100, salt: 100 + last}
		if w.Save(toHS(hardState{term: 1, vote: 1, commit: last + 1}), []*raftpb.Entry{toRaft(e)}) != nil {
			fmt.Println("SAVE fail")
			return
		}
		fmt.Printf("ACK last=%d (%s)\n", last+1, how)
		// no Close: the power loss comes before anything else
	default:
		dir := root + "/data/member/wal"
		if !etcdwal.Exist(dir) {
			fmt.Println("NOWAL")
			return
		}
		st, c, _ := restartRead(lg, dir, nil)
		if st != readOK {
			fmt.Println("READ fail")
			return
		}
		last := c.baseIdx
		for _, e := range c.ents {
			last = e.index
		}
		fmt.Printf("READ last=%d\n", last)
	}
}

func knRun(t *testing.T, root, marker, site, step string) ([]crashsim.Event, string) {
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	cmd.Env = append(os.Environ(), "WALKN_CHILD="+step, "WALKN_ROOT="+root, "WALKN_SITE="+site)
	out := filepath.Join(filepath.Dir(root), "out-"+step)
	f, _ := os.Create(out)
	cmd.Stdout, cmd.Stderr = f, f
	evs, err := crashsim.Record(root, marker, cmd)
	f.Close()
	if err != nil {
		t.Fatal(err)
	}
	b, _ := os.ReadFile(out)
	return evs, strings.TrimSpace(string(b))
}

func knSite(site string, e crashsim.Event) bool {
	switch site {
	case "mkdir":
		return e.Kind == crashsim.KMkdir && e.Name == "data"
	case "create":
		return e.Kind == crashsim.KRename && e.Name == "wal.tmp"
	}
	return e.Kind == crashsim.KRename && walTmpName.MatchString(e.Name) && strings.HasSuffix(e.Name2, ".wal")
}

func knTest(t *testing.T, site string) {
	base, err := os.MkdirTemp(os.Getenv("TMPDIR"), "kn-"+site+"-")
	if err != nil {
		t.Fatal(err)
	}
	if os.Getenv("WALKN_KEEP") == "" {
		defer os.RemoveAll(base)
	}
	marker := filepath.Join(base, "markers")
	os.WriteFile(marker, nil, 0o600)
	r0 := filepath.Join(base, "r0")
	os.Mkdir(r0, 0o700)
	m1, err := crashsim.Scan(r0, false)
	if err != nil {
		t.Fatal(err)
	}
	ev1, out1 := knRun(t, r0, marker, site, "1")
	if out1 != "" {
		t.Fatalf("step 1: %q", out1)
	}
	m1.SetEvents(ev1)
	// the kill: right after the site's first directory operation (before its fsync)
	k := -1
	for i, e := range ev1 {
		if knSite(site, e) {
			k = i + 1
			break
		}
	}
	if k < 0 {
		t.Fatalf("step 1 has no %s operation", site)
	}
	r1 := filepath.Join(base, "r1")
	os.Mkdir(r1, 0o700)
	if err := m1.Build(crashsim.Spec{K: k, Model: crashsim.Kill}, r1); err != nil {
		t.Fatal(err)
	}
	inos, err := crashsim.KillInodes(m1, k, r1)
	if err != nil {
		t.Fatal(err)
	}
	ev2, ack := knRun(t, r1, marker, site, "2")
	var acked uint64
	if _, err := fmt.Sscanf(ack, "ACK last=%d", &acked); err != nil {
		t.Fatalf("the restart on the page cache: %q", ack)
	}
	cm, err := crashsim.Compose(m1, k, inos, ev2)
	if err != nil {
		t.Fatal(err)
	}
	// the power loss after step 2: every file and directory at its synced state only (Seed 0)
	for _, model := range []string{crashsim.Posix, crashsim.Ordered} {
		r2 := filepath.Join(base, "r2-"+model)
		os.Mkdir(r2, 0o700)
		if err := cm.Build(crashsim.Spec{K: len(cm.Events), Model: model}, r2); err != nil {
			t.Fatal(err)
		}
		_, read := knRun(t, r2, marker, site, "3")
		var got uint64
		ok := false
		if _, err := fmt.Sscanf(read, "READ last=%d", &got); err == nil {
			ok = got >= acked
		}
		t.Logf("%s, %s: the restart after the kill acknowledged %q; after the power loss %q", site, model, ack, read)
		if !ok {
			t.Errorf("%s, %s: the power loss took back what the restart on the page cache acknowledged (%q, then %q)", site, model, ack, read)
		}
	}
}

func TestKillThenPowerKN1(t *testing.T) { knTest(t, "mkdir") }
func TestKillThenPowerKN2(t *testing.T) { knTest(t, "create") }
func TestKillThenPowerKN3(t *testing.T) { knTest(t, "cut") }
