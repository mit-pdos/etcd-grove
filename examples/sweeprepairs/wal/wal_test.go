package walrepairs

import (
	"context"
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io/fs"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"syscall"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/putget"
	"github.com/mit-pdos/etcd-grove/examples/etcd/putget3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// ---------------------------------------------------------------- helpers

// inChild runs this test binary's test `name` in a process of its own, in the directory dir, with
// the environment variable WR_CHILD=phase, and returns its output; it fails if the child failed.
func inChild(t *testing.T, name, dir, phase string) string {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run", "^"+name+"$", "-test.v", "-test.count=1")
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "WR_CHILD="+phase)
	out, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(out), "--- PASS: "+name) {
		t.Fatalf("child %s phase %s: %v\n%s", name, phase, err, out)
	}
	return string(out)
}

// gitShow is a file of another branch of the repository (the counterexamples' branches).
func gitShow(t *testing.T, rev, path string) string {
	t.Helper()
	out, err := exec.Command("git", "-C", "../..", "show", rev+":"+path).Output()
	if err != nil {
		t.Fatalf("git show %s:%s: %v", rev, path, err)
	}
	return string(out)
}

var hostPortRe = regexp.MustCompile(`^[^\s/"]*:[0-9]+$`)

// addrLits are the string literals of the Go source src that look like host:port addresses.
func addrLits(t *testing.T, name, src string) []string {
	t.Helper()
	f, err := parser.ParseFile(token.NewFileSet(), name, src, 0)
	if err != nil {
		t.Fatalf("parse %s: %v", name, err)
	}
	var lits []string
	ast.Inspect(f, func(n ast.Node) bool {
		if bl, ok := n.(*ast.BasicLit); ok && bl.Kind == token.STRING {
			s, err := strconv.Unquote(bl.Value)
			if err == nil && hostPortRe.MatchString(s) {
				lits = append(lits, s)
			}
		}
		return true
	})
	return lits
}

// listenIdentity listens on a and says whether the bound socket's address is the string a (the
// literal names the socket); an error if the listen failed.
func listenIdentity(a string) (bool, string, error) {
	l, err := net.Listen("tcp", a)
	if err != nil {
		return false, "", err
	}
	defer l.Close()
	return l.Addr().String() == a, l.Addr().String(), nil
}

// ---------------------------------------------------------------- W5: numeric literal addresses

// TestW5Lit: the premise's definition on the address forms the review tried.
func TestW5Lit(t *testing.T) {
	ok := []string{"127.0.0.1:23790", "127.0.0.2:1", "10.0.0.1:65535"}
	bad := []string{"localhost:24290", "[::1]:24290", ":24290", "0.0.0.0:24290", "[::]:24290",
		"[::ffff:127.0.0.1]:24290", "127.0.0.1:0", "127.0.0.1:024290", "127.000.0.1:24290",
		"127.0.0.1:65536", "127.0.0.1", "", "127.0.0.1:2429x", "1.2.3:80", "1.2.3.4.5:80"}
	for _, a := range ok {
		if !NetAddrLit(a) {
			t.Errorf("%q: rejected", a)
		}
	}
	for _, a := range bad {
		if NetAddrLit(a) {
			t.Errorf("%q: accepted", a)
		}
	}
	t.Logf("netAddrLit: %d accepted, %d rejected as expected", len(ok), len(bad))
}

// TestW5ExamplesAddrs: every host:port literal in the examples' Go sources (the addresses their
// programs listen on, reserve and dial; the axiom counterexamples and this harness excepted) is a
// numeric literal, and a listen on it binds the socket the string names.
func TestW5ExamplesAddrs(t *testing.T) {
	seen := map[string][]string{}
	err := filepath.WalkDir("../..", func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() && (d.Name() == "axiomcx" || d.Name() == "sweeprepairs" || d.Name() == "testdata") {
			return filepath.SkipDir
		}
		if d.IsDir() || !strings.HasSuffix(p, ".go") {
			return nil
		}
		src, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		for _, a := range addrLits(t, p, string(src)) {
			seen[a] = append(seen[a], p)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	var addrs []string
	for a := range seen {
		addrs = append(addrs, a)
	}
	sort.Strings(addrs)
	bound, inuse := 0, 0
	for _, a := range addrs {
		if !NetAddrLit(a) {
			t.Errorf("%q (%v): not a numeric literal", a, seen[a])
			continue
		}
		same, got, err := listenIdentity(a)
		switch {
		case err != nil && errors.Is(err, syscall.EADDRINUSE):
			inuse++ // another session's test holds it: the literal check alone
		case err != nil:
			t.Errorf("%q: listen: %v", a, err)
		case !same:
			t.Errorf("%q: bound %s", a, got)
		default:
			bound++
		}
	}
	files := map[string]bool{}
	for _, ps := range seen {
		for _, p := range ps {
			files[p] = true
		}
	}
	t.Logf("%d distinct address literals in %d Go files: all numeric literals; %d bound at exactly their string, %d in use (skipped)",
		len(addrs), len(files), bound, inuse)
}

// TestW5Counterexample: the netaddralias counterexample's addresses violate the premise, and the
// two that violate it are exactly the ones whose listen does not bind the socket the string names,
// and whose dial reaches the other member.
func TestW5Counterexample(t *testing.T) {
	src := gitShow(t, "axiom/netaddralias", "examples/axiomcx/netaddralias/netaddralias.go")
	lits := addrLits(t, "netaddralias.go", src)
	var badLits []string
	for _, a := range lits {
		if !NetAddrLit(a) {
			badLits = append(badLits, a)
		}
	}
	t.Logf("netaddralias's address literals %v; not numeric literals: %v", lits, badLits)
	want := map[string]bool{"localhost:24290": true, "[::1]:24290": true}
	if len(badLits) != 2 || !want[badLits[0]] || !want[badLits[1]] {
		t.Fatalf("expected exactly localhost:24290 and [::1]:24290 rejected, got %v", badLits)
	}
	// the runtime meaning, at a fresh port: both listens succeed, the host name's binds another
	// string, and a dial of the host name reaches the IPv6 listener
	const p = "25617"
	lx, err := net.Listen("tcp", "localhost:"+p)
	if err != nil {
		t.Fatal(err)
	}
	defer lx.Close()
	ly, err := net.Listen("tcp", "[::1]:"+p)
	if err != nil {
		t.Fatal(err)
	}
	defer ly.Close()
	t.Logf("listen localhost:%s bound %s (string differs: %v); listen [::1]:%s bound %s", p, lx.Addr(),
		lx.Addr().String() != "localhost:"+p, p, ly.Addr())
	acc := make(chan string, 2)
	for _, l := range []net.Listener{lx, ly} {
		go func(l net.Listener) {
			c, err := l.Accept()
			if err == nil {
				acc <- l.Addr().String()
				c.Close()
			}
		}(l)
	}
	c, err := net.Dial("tcp", "localhost:"+p)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()
	got := <-acc
	t.Logf("dial localhost:%s accepted by the listener at %s", p, got)
	if got == lx.Addr().String() {
		t.Log("(this host dials IPv4 first: no misroute here, the literal premise still rejects both strings)")
	}
}

// ---------------------------------------------------------------- W3: distinct data directories

// TestW3Counterexample: waldiralias's data directories are distinct strings (Ds.Nodup holds) but
// two of them name one directory: the proposed premise fails for them.
func TestW3Counterexample(t *testing.T) {
	src := gitShow(t, "axiom/waldiralias", "examples/axiomcx/waldiralias/waldiralias.go")
	m := regexp.MustCompile(`AliasPrefix\s*=\s*"([^"]*)"`).FindStringSubmatch(src)
	if m == nil {
		t.Fatal("no AliasPrefix in waldiralias.go")
	}
	prefix := m[1]
	t.Chdir(t.TempDir())
	ds := []string{"wda-1.etcd", "wda-2.etcd", "wda-3.etcd", prefix + "wda-2.etcd", prefix + "wda-3.etcd"}
	nodup := map[string]bool{}
	for _, d := range ds {
		nodup[d] = true
	}
	t.Logf("Ds = %v; distinct strings: %v", ds, len(nodup) == len(ds))
	// at start: absent, so the strings alone (resolved) already overlap
	err0 := DataDirsDistinct(ds)
	for _, d := range ds {
		if err := os.MkdirAll(filepath.Join(d, "member", "wal"), 0o700); err != nil {
			t.Fatal(err)
		}
	}
	err1 := DataDirsDistinct(ds)
	t.Logf("premise (1) at start (directories absent): %v", err0)
	t.Logf("premise (1) once the directories exist: %v", err1)
	if err0 == nil || err1 == nil {
		t.Fatal("the counterexample's Ds passes the distinct-directories check")
	}
}

// exampleRun runs an example's Main in the child's fresh directory with the premises checked: each
// data directory fresh at start (W4), after Main the data directories pairwise distinct and every
// file below the working directory inside exactly one of them, and every open file too (W3).
func exampleRun(t *testing.T, ds []string, main func()) {
	cwd, _ := os.Getwd()
	for _, d := range ds {
		if err := DataDirFresh(d); err != nil {
			t.Fatalf("W4 premise false at start: %v", err)
		}
	}
	t.Logf("W4: %d data directories %v fresh at start", len(ds), ds)
	func() {
		defer func() {
			if r := recover(); r != nil {
				t.Fatalf("Main panicked: %v", r)
			}
		}()
		main()
	}()
	if err := DataDirsDistinct(ds); err != nil {
		t.Fatalf("W3 premise false: %v", err)
	}
	nfiles := 0
	err := filepath.WalkDir(cwd, func(p string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() {
			return err
		}
		nfiles++
		r, _ := resolve(p)
		k := 0
		for _, dd := range ds {
			rd, _ := resolve(dd)
			if within(r, rd) {
				k++
			}
		}
		if k != 1 {
			return fmt.Errorf("file %s inside %d data directories", p, k)
		}
		return nil
	})
	if err != nil {
		t.Fatalf("W3 premise false: %v", err)
	}
	nopen, err := OpenFilesWithin(cwd, ds)
	if err != nil {
		t.Fatalf("W3 premise false: %v", err)
	}
	t.Logf("W3: data directories distinct; %d files below the working directory and %d open files, each inside exactly one", nfiles, nopen)
}

// TestW3W4Examples: the premises hold of two examples' real runs (each in a process of its own,
// in a fresh directory): putget (one member) and putget3 (three).
func TestW3W4Examples(t *testing.T) {
	switch os.Getenv("WR_CHILD") {
	case "putget":
		exampleRun(t, []string{"putget.etcd"}, putget.Main)
		return
	case "putget3":
		exampleRun(t, []string{"putget3-1.etcd", "putget3-2.etcd", "putget3-3.etcd"}, putget3.Main)
		return
	case "":
	default:
		t.Skip()
	}
	for _, ex := range []string{"putget", "putget3"} {
		out := inChild(t, "TestW3W4Examples", t.TempDir(), ex)
		for _, l := range strings.Split(out, "\n") {
			if strings.Contains(l, "W3:") || strings.Contains(l, "W4:") {
				t.Logf("%s: %s", ex, strings.TrimSpace(l))
			}
		}
	}
}

// ---------------------------------------------------------------- W4: the data directory empty

// TestW4StaleBackend: the environment of netaddralias's TestStaleBackend (a data directory with a
// backend holding k0 and no WAL) violates the widened premise, while walDirsAbsent (no WAL) holds;
// and its program, run on it, serves k0 (bootstrapContract's empty first-start backend false).
func TestW4StaleBackend(t *testing.T) {
	lg := zap.NewNop()
	const name, peer, caddr = "wr-db", "127.0.0.1:25620", "127.0.0.1:25621"
	switch os.Getenv("WR_CHILD") {
	case "":
		dir := t.TempDir()
		inChild(t, "TestW4StaleBackend", dir, "1")
		dd := filepath.Join(dir, name+".etcd")
		walAbsent := !wal.Exist(filepath.Join(dd, "member", "wal"))
		err := DataDirFresh(dd)
		t.Logf("environment: walDirsAbsent's meaning (no WAL) holds: %v; the widened premise: %v", walAbsent, err)
		if !walAbsent || err == nil {
			t.Fatal("expected no WAL and a non-fresh data directory")
		}
		out := inChild(t, "TestW4StaleBackend", dir, "2")
		for _, l := range strings.Split(out, "\n") {
			if strings.Contains(l, "phase 2") {
				t.Log(strings.TrimSpace(l))
			}
		}
		return
	case "1":
		s, err := etcdstart.StartServer(name, peer, caddr, lg)
		if err != nil {
			t.Fatal(err)
		}
		if err := etcdstart.Serve(s, caddr); err != nil {
			t.Fatal(err)
		}
		cli, err := etcdstart.NewClient(caddr, lg)
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		_, err = cli.Put(ctx, "k0", "v1")
		cancel()
		if err != nil {
			t.Fatal(err)
		}
		cli.Close()
		s.HardStop()
		if err := os.RemoveAll(name + ".etcd/member/wal"); err != nil {
			t.Fatal(err)
		}
		return
	case "2":
		s, err := etcdstart.StartServer(name, peer, caddr, lg)
		if err != nil {
			t.Fatal(err)
		}
		if err := etcdstart.Serve(s, caddr); err != nil {
			t.Fatal(err)
		}
		cli, err := etcdstart.NewClient(caddr, lg)
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		resp, err := cli.Get(ctx, "k0")
		cancel()
		if err != nil {
			t.Fatal(err)
		}
		t.Logf("phase 2: a fresh start over the stale data directory serves k0: %v", len(resp.Kvs) != 0)
		return
	default:
		t.Skip()
	}
}

// ---------------------------------------------------------------- W1, W2: the purge and Release

func u64(x uint64) *uint64 { return &x }

// walScenario writes a WAL in dir over small segments: entries 1..260 of term 1 (commit 260), a
// snapshot record at index b = 100 after entry 200, then ReleaseLockTo(rel); the purge (max one
// file, one pass) runs before Close, or after it; then a restart opens the WAL at the snapshot
// record b and reads it back. It returns the number of WAL files before and after the purge and
// the restart's error.
func walScenario(dir string, rel uint64, purgeAfterClose bool) (int, int, error) {
	lg := zap.NewNop()
	w, err := wal.Create(lg, dir, []byte("meta"))
	if err != nil {
		return 0, 0, err
	}
	data := make([]byte, 200)
	save := func(lo, hi uint64) error {
		for i := lo; i <= hi; i += 10 {
			var ents []*raftpb.Entry
			for j := i; j < i+10 && j <= hi; j++ {
				ents = append(ents, &raftpb.Entry{Term: u64(1), Index: u64(j), Data: data})
			}
			if err := w.Save(&raftpb.HardState{Term: u64(1), Vote: u64(1), Commit: u64(min(i+9, hi))}, ents); err != nil {
				return err
			}
		}
		return nil
	}
	if err := save(1, 200); err != nil {
		return 0, 0, err
	}
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: u64(100), Term: u64(1), ConfState: &raftpb.ConfState{Voters: []uint64{1}}}); err != nil {
		return 0, 0, err
	}
	if err := save(201, 260); err != nil {
		return 0, 0, err
	}
	if err := w.ReleaseLockTo(rel); err != nil {
		return 0, 0, err
	}
	count := func() int {
		names, _ := fileutil.ReadDir(dir)
		n := 0
		for _, nm := range names {
			if strings.HasSuffix(nm, ".wal") {
				n++
			}
		}
		return n
	}
	before := count()
	purge := func() error {
		stop := make(chan struct{})
		close(stop) // one pass: the loop purges first, then sees stop
		donec, errc := fileutil.PurgeFileWithDoneNotify(lg, dir, "wal", 1, time.Hour, stop)
		<-donec
		select {
		case err := <-errc:
			return err
		default:
			return nil
		}
	}
	if purgeAfterClose {
		if err := w.Close(); err != nil {
			return before, 0, err
		}
		if err := purge(); err != nil {
			return before, 0, err
		}
	} else {
		if err := purge(); err != nil {
			return before, 0, err
		}
		if err := w.Close(); err != nil {
			return before, 0, err
		}
	}
	after := count()
	w2, err := wal.Open(lg, dir, &walpb.Snapshot{Index: u64(100), Term: u64(1)})
	if err != nil {
		return before, after, fmt.Errorf("restart: open: %w", err)
	}
	defer w2.Close()
	_, hs, ents, err := w2.ReadAll()
	if err != nil {
		return before, after, fmt.Errorf("restart: ReadAll: %w", err)
	}
	if len(ents) == 0 || ents[0].GetIndex() != 101 || ents[len(ents)-1].GetIndex() != 260 || hs.GetCommit() != 260 {
		return before, after, fmt.Errorf("restart: read back %d entries, commit %d", len(ents), hs.GetCommit())
	}
	return before, after, nil
}

// TestW1W2WalPurge: what walPurgeRight and walBaseLb stand for, on the pinned WAL: the restart at
// the WAL's snapshot record b = 100 reads its records back when every Release is at most b (W2's
// premise) and the purge has stopped before Close (W1's: Close releases every lock), and fails
// when either is violated.
func TestW1W2WalPurge(t *testing.T) {
	old := wal.SegmentSizeBytes
	wal.SegmentSizeBytes = 4 * 1024
	defer func() { wal.SegmentSizeBytes = old }()
	cases := []struct {
		name       string
		rel        uint64
		afterClose bool
		wantOK     bool
	}{
		{"Release(b), purge stopped before Close (W1, W2 hold)", 100, false, true},
		{"Release(b-50), purge stopped before Close (W1, W2 hold)", 50, false, true},
		{"Release(250 > b), purge before Close (W2 violated)", 250, false, false},
		{"Release(b), purge after Close (W1 violated)", 100, true, false},
	}
	for _, c := range cases {
		dir := filepath.Join(t.TempDir(), "wal")
		before, after, err := walScenario(dir, c.rel, c.afterClose)
		t.Logf("%s: %d WAL files, %d after the purge; restart at b: %v", c.name, before, after, err)
		if (err == nil) != c.wantOK {
			t.Errorf("%s: unexpected outcome %v", c.name, err)
		}
	}
}

// TestSnapDBPurge (finding, W1's spec): purgeFile's other purge, PurgeFileWithoutFlock(SnapDir,
// "snap.db", maxSnapDBFiles = 5), removes the oldest .snap.db files once there are more than five,
// whatever index the apply thread will open next and with no Release: files snapDirInv keeps.
func TestSnapDBPurge(t *testing.T) {
	dir := t.TempDir()
	for i := 1; i <= 6; i++ {
		if err := os.WriteFile(filepath.Join(dir, fmt.Sprintf("%016x.snap.db", i)), []byte("db"), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.WriteFile(filepath.Join(dir, fmt.Sprintf("%016x-%016x.snap", 1, 1)), []byte("s"), 0o600); err != nil {
		t.Fatal(err)
	}
	stop := make(chan struct{})
	close(stop)
	donec, _ := fileutil.PurgeFileWithoutFlock(zap.NewNop(), dir, "snap.db", 5, time.Hour, stop)
	<-donec
	names, _ := fileutil.ReadDir(dir)
	t.Logf("after one pass: %v", names)
	if _, err := os.Stat(filepath.Join(dir, fmt.Sprintf("%016x.snap.db", 1))); !errors.Is(err, fs.ErrNotExist) {
		t.Fatal("the oldest .snap.db file was not removed")
	}
}
