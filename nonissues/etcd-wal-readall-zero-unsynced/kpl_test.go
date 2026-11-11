package wal

// The kill-then-power-loss regression test (W3, for etcd-grove-81's rung-3 question): a member
// killed after a Save's write but before its fdatasync restarts without a reboot (the page cache
// kept), reads the unsynced record, and loses power before anything else syncs. Without F-Z the
// restart relied on a record the power loss takes back: the next restart reads less than the
// first one returned. With F-Z (ReadAll fdatasyncs the tail it zeroed) the read is durable.
//
//	go test ./etcd/wal -run TestKillThenPower -v     # W3_FZ_MODEL=1: model F-Z on the pin

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

// kplChild: step 1 creates the WAL and saves e1 (synced) then e2 with commit 2 (synced: killed
// before); step 2 (and 3) restarts and prints what it read.
func kplChild(root, step string) {
	lg := zap.NewNop()
	dir := root + "/data/member/wal"
	if step == "1" {
		fileutil.TouchDirAll(lg, root+"/data")
		fileutil.TouchDirAll(lg, root+"/data/member")
		w, err := etcdwal.Create(lg, dir, []byte("m"))
		if err != nil {
			panic(err)
		}
		e1 := entry{index: 1, term: 1, size: 100, salt: 1}
		e2 := entry{index: 2, term: 1, size: 100, salt: 2}
		w.Save(toHS(hardState{term: 1, vote: 1, commit: 1}), []*raftpb.Entry{toRaft(e1)})
		w.Save(toHS(hardState{term: 1, vote: 1, commit: 2}), []*raftpb.Entry{toRaft(e2)})
		return
	}
	st, c, w := restartRead(lg, dir)
	if st != readOK {
		fmt.Println("READ fail")
		return
	}
	fmt.Printf("READ commit=%d ents=%d\n", c.hs.commit, len(c.ents))
	_ = w // no Close: the power loss comes before anything else
}

func kplRun(t *testing.T, root, marker, step string) ([]crashsim.Event, string) {
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	cmd.Env = append(os.Environ(), "WALKPL_CHILD="+step, "WALKPL_ROOT="+root)
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

func TestKillThenPower(t *testing.T) {
	fz := os.Getenv("W3_FZ_MODEL") != ""
	base := t.TempDir()
	marker := filepath.Join(base, "markers")
	os.WriteFile(marker, nil, 0o600)
	r0 := filepath.Join(base, "r0")
	os.Mkdir(r0, 0o700)
	m1, _ := crashsim.Scan(r0, fz)
	m1.FN1, m1.FN2 = true, true
	ev1, _ := kplRun(t, r0, marker, "1")
	m1.SetEvents(ev1)
	// the kill: right after the last write to a WAL file (e2's records, before their fdatasync)
	k := -1
	for i, e := range ev1 {
		if e.Kind == crashsim.KWrite && strings.HasSuffix(e.Path, ".wal") {
			k = i + 1
		}
	}
	if k < 0 || k >= len(ev1) || ev1[k].Kind != crashsim.KSync {
		t.Fatalf("no write-then-fdatasync at the end of step 1 (k=%d)", k)
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
	ev2, read2 := kplRun(t, r1, marker, "2")
	if read2 != "READ commit=2 ents=2" {
		t.Fatalf("the restart on the page cache read %q, want the unsynced e2", read2)
	}
	cm, err := crashsim.Compose(m1, k, inos, ev2)
	if err != nil {
		t.Fatal(err)
	}
	// the power loss after step 2: every file at its synced content only (Spec.Seed 0)
	for _, model := range []string{crashsim.Posix, crashsim.Ordered} {
		r2 := filepath.Join(base, "r2-"+model)
		os.Mkdir(r2, 0o700)
		if err := cm.Build(crashsim.Spec{K: len(cm.Events), Model: model}, r2); err != nil {
			t.Fatal(err)
		}
		_, read3 := kplRun(t, r2, marker, "3")
		t.Logf("F-Z modelled %v, %s: restart after the kill read %q; after the power loss %q", fz, model, read2, read3)
		if read3 != read2 {
			t.Errorf("%s: the power loss took back what the restart on the page cache read (%q, then %q)", model, read2, read3)
		}
	}
}
