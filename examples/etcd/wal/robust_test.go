package wal

// The crash driver: runs Boot as a traced child process (crashtest/crashsim's ptrace recorder),
// builds a crash image of its file system at a chosen point under a chosen model (kill, posix,
// ordered; F-Z, F-N1, F-N2 optionally modelled), and runs the next incarnation on the image.
// A chain is one member: incarnations until -incarnations crashes or the member goes down; the
// last incarnation only restarts and checks.
//
// A crash point is named relative to the tester's own durable writes (the renames of its oracle
// file, one per WAL operation begun or synced): "the j-th event after the i-th oracle write",
// where j counts the events of the tester's goroutine (the WAL file pipeline's N.tmp events are
// left out of the count, but stay in the image), so that a seed names the same point in the
// tester's run across runs, up to the pipeline's interleaving.
//
//	go test ./etcd/wal -run TestRobust -chains 50 -model posix -fz -fn

import (
	"bytes"
	"flag"
	"fmt"
	etcdwal "go.etcd.io/etcd/server/v3/storage/wal"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/etcd/wal/crashtest/crashsim"
	"github.com/mit-pdos/etcd-grove/examples/etcd/wal/crashtest/walref"
)

var (
	flagChains  = flag.Int("chains", 10, "chains (members) to run")
	flagSeed    = flag.Int64("seed", 1, "first chain's seed")
	flagModel   = flag.String("model", "posix", "crash model: kill, posix, ordered")
	flagInc     = flag.Int("incarnations", 6, "crashes per chain")
	flagOps     = flag.Int("ops", 25, "operations per incarnation")
	flagFZ      = flag.Bool("fz", false, "model the fork fix F-Z (Fdatasync after ZeroToEnd)")
	flagFN      = flag.Bool("fn", false, "model the fork fixes F-N1 and F-N2 (directory fsyncs)")
	flagGarbage = flag.Float64("garbage", 0.05, "P4 garbage probability (posix, ordered; half the chains)")
	flagPurgeOK = flag.Bool("purgeok", false, "relax the check: a purged prefix of the history may be missing (PurgedPrefixOK)")
	flagScratch = flag.String("scratch", "", "scratch directory (default: TMPDIR)")
	flagTarget  = flag.Bool("target", false, "W3: bias toward received snapshots, purges and dormant-record crash points")
	flagKillPL  = flag.Float64("killpl", 0, "probability that a crash is a kill whose page cache the next incarnation runs on (no reboot), followed by a power loss during that incarnation (posix, ordered)")
	flagKillTgt = flag.Bool("killtarget", false, "with -killpl: kill right after a write to a WAL file, and lose power early in the next incarnation")
	flagWeakP4  = flag.Bool("weakp4", false, "garbage may garble synced bytes of a rewritten sector (the superseded weaker P4)")
	flagKillDir = flag.String("killdir", "", "W3b (K-N): with -killpl, kill right after a directory operation: mkdir (TouchDirAll's data/member), create (Create's wal.tmp rename), cut (a cut's N.tmp rename), or all; no kill if the run has none")
)

func TestMain(m *testing.M) {
	if st := os.Getenv("WALKN_CHILD"); st != "" {
		knChild(os.Getenv("WALKN_ROOT"), os.Getenv("WALKN_SITE"), st)
		os.Exit(0)
	}
	if st := os.Getenv("WALKPL_CHILD"); st != "" {
		kplChild(os.Getenv("WALKPL_ROOT"), st)
		os.Exit(0)
	}
	if os.Getenv("WALROBUST_CHILD") != "" {
		seed, _ := strconv.ParseUint(os.Getenv("WALROBUST_SEED"), 10, 64)
		ops, _ := strconv.ParseUint(os.Getenv("WALROBUST_OPS"), 10, 64)
		etcdwal.SegmentSizeBytes = segSizeFor(seed)
		st := Boot(os.Getenv("WALROBUST_ROOT"), seed, ops)
		fmt.Printf("STATUS %d\n", st)
		os.Exit(0)
	}
	os.Exit(m.Run())
}

var purgeHitsRe = regexp.MustCompile(`PURGEHITS (\d+)`)
var dormantRe = regexp.MustCompile(`DORMANT (\d+)`)

var walTmpName = regexp.MustCompile(`^[0-9]+\.tmp$`)

// counted lists the event times after t0 (exclusive) up to end (exclusive) that the crash-point
// offsets count: every event but those on the WAL pipeline's N.tmp files while so named.
func counted(evs []crashsim.Event, t0, end int) []int {
	names := map[uint64]string{}
	var out []int
	for i := 0; i < end; i++ {
		e := evs[i]
		switch e.Kind {
		case crashsim.KCreate:
			names[e.Ino] = e.Name
		case crashsim.KRename:
			names[e.Ino] = e.Name2
		}
		if i <= t0 || e.Kind == crashsim.KMarker {
			continue
		}
		if walTmpName.MatchString(names[e.Ino]) && !(e.Kind == crashsim.KRename) {
			continue
		}
		out = append(out, i)
	}
	return out
}

// oracleWrites are the times of the renames of the oracle file into place.
func oracleWrites(evs []crashsim.Event) []int {
	var out []int
	for i, e := range evs {
		if e.Kind == crashsim.KRename && e.Name2 == "state" {
			out = append(out, i)
		}
	}
	return out
}

type tally struct {
	chains, incs, firstStarts, restartsOK int
	downRestart, downNone, downDefined    int
	downOther                             int
	saves, saveOkMiss                     int
	violations                            []string
	purgeHits, hitChains, dormantCrashes  int
	killPL                                int
	killDir                               int
	infra                                 []string
}

// saveOkMisses counts the Saves begun since the last restart (in the oracle file under root)
// whose entries miss WalSaveOk against today's fold of the history before them, in some candidate.
func saveOkMisses(root string) (int, int) {
	s, ok := func() (string, bool) {
		b, err := os.ReadFile(filepath.Join(root, "oracle", "state"))
		return string(b), err == nil
	}()
	if !ok {
		return 0, 0
	}
	o, ok2 := decodeOracle(s)
	if !ok2 {
		return 0, 0
	}
	saves, misses := 0, 0
	for p := range o.since {
		if o.since[p].snap || len(o.since[p].ents) == 0 {
			continue
		}
		saves++
		for _, c := range o.cands {
			h := append(copyOps(c.h), o.since[:p]...)
			if !walSaveOk(walFold(h), o.since[p].ents) {
				misses++
				break
			}
		}
	}
	return saves, misses
}

func runChain(t *testing.T, seed int64, scratch string, tl *tally) {
	rng := rand.New(rand.NewSource(seed))
	base, err := os.MkdirTemp(scratch, fmt.Sprintf("chain%d-", seed))
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(base) // this run's own scratch
	root := filepath.Join(base, "r0")
	if err := os.MkdirAll(filepath.Join(root, "oracle"), 0o700); err != nil {
		t.Fatal(err)
	}
	marker := filepath.Join(base, "markers")
	garbage := 0.0
	if *flagModel != crashsim.Kill && rng.Intn(2) == 0 {
		garbage = *flagGarbage
	}
	tl.chains++
	trail := []string{}
	chainHit := false
	// a pending kill: the model of the killed run and the kill point; the incarnation now running
	// on the kill image ends in a power loss of the composed model
	var killM *crashsim.Model
	killK := 0
	var killInos map[uint64]uint64
	for inc := 0; inc <= *flagInc; inc++ {
		ops := *flagOps
		if inc == *flagInc {
			ops = 0
		}
		mdl, err := crashsim.Scan(root, *flagFZ)
		if err != nil {
			t.Fatal(err)
		}
		mdl.FN1, mdl.FN2 = *flagFN, *flagFN
		mdl.WeakP4 = *flagWeakP4
		if err := os.WriteFile(marker, nil, 0o600); err != nil {
			t.Fatal(err)
		}
		cseed := uint64(seed)*1000 + uint64(inc) + 1
		cmd := exec.Command(os.Args[0], "-test.run=^$")
		cmd.Env = append(os.Environ(), "WALROBUST_CHILD=1", "WALROBUST_ROOT="+root,
			fmt.Sprintf("WALROBUST_SEED=%d", cseed), fmt.Sprintf("WALROBUST_OPS=%d", ops))
		if *flagPurgeOK {
			cmd.Env = append(cmd.Env, "WALROBUST_PURGEOK=1")
		}
		if *flagTarget {
			cmd.Env = append(cmd.Env, fmt.Sprintf("WALROBUST_TARGET=%d", 1+inc%2))
		}
		// files, not buffers: Record reaps the child itself (no cmd.Wait), so a pipe's copying
		// goroutine might not have drained it yet
		outF, _ := os.Create(filepath.Join(base, "stdout"))
		errF, _ := os.Create(filepath.Join(base, "stderr"))
		cmd.Stdout, cmd.Stderr = outF, errF
		evs, rerr := crashsim.Record(root, marker, cmd)
		outF.Close()
		errF.Close()
		ob, _ := os.ReadFile(filepath.Join(base, "stdout"))
		eb, _ := os.ReadFile(filepath.Join(base, "stderr"))
		stdout, stderr := bytes.NewBuffer(ob), bytes.NewBuffer(eb)
		tl.incs++
		name := fmt.Sprintf("chain %d (%s fz=%v fn=%v purgeok=%v garbage=%v) incarnation %d after [%s]", seed, *flagModel, *flagFZ, *flagFN, *flagPurgeOK, garbage, inc, strings.Join(trail, "; "))
		if os.Getenv("W3TRACE") != "" {
			t.Logf("chain %d inc %d stderr:\n%s", seed, inc, stderr.String())
		}
		if m := purgeHitsRe.FindStringSubmatch(stderr.String()); m != nil {
			n, _ := strconv.Atoi(m[1])
			tl.purgeHits += n
			if n > 0 && !chainHit {
				chainHit = true
				tl.hitChains++
			}
		}
		if se := stderr.String(); strings.Contains(se, "panic:") {
			msg := se[strings.Index(se, "panic:"):]
			if i := strings.Index(msg, "\n"); i > 0 {
				msg = msg[:i]
			}
			keep := filepath.Join(scratch, fmt.Sprintf("violation-%d-%d", seed, inc))
			os.RemoveAll(keep)
			exec.Command("cp", "-a", root, keep).Run()
			tl.violations = append(tl.violations, name+": "+msg+" (image kept in "+keep+")")
			return
		}
		if rerr != nil {
			tl.infra = append(tl.infra, fmt.Sprintf("%s: record: %v", name, rerr))
			return
		}
		st := strings.TrimSpace(stdout.String())
		if st == fmt.Sprintf("STATUS %d", StatusDown) {
			if inc == 0 {
				tl.downOther++
				return
			}
			tl.downRestart++
			d := walref.DecodeDir(filepath.Join(root, "data", "member", "wal"))
			if _, ok := walref.WalRead(walref.Group(d.Recs)); ok && !d.Purged {
				tl.downDefined++
			} else {
				tl.downNone++
			}
			return
		}
		if st != fmt.Sprintf("STATUS %d", StatusRan) {
			t.Fatalf("%s: child said %q\n%s", name, st, stderr.String())
		}
		if inc == 0 {
			tl.firstStarts++
		} else {
			tl.restartsOK++
		}
		s, mi := saveOkMisses(root)
		tl.saves += s
		tl.saveOkMiss += mi
		if inc == *flagInc {
			return
		}
		if killM != nil {
			cm, err := crashsim.Compose(killM, killK, killInos, evs)
			if err != nil {
				t.Fatalf("%s: compose: %v", name, err)
			}
			if os.Getenv("W3COMPOSECHECK") != "" {
				chk := filepath.Join(base, fmt.Sprintf("chk%d", inc))
				os.Mkdir(chk, 0o700)
				if err := cm.Build(crashsim.Spec{K: killK + len(evs), Model: crashsim.Kill}, chk); err != nil {
					t.Fatalf("compose check build: %v", err)
				}
				out, _ := exec.Command("diff", "-r", "-q", root, chk).CombinedOutput()
				t.Logf("COMPOSECHECK %s inc %d: %q", name[:12], inc, string(out))
			}
			k2 := killK + rng.Intn(len(evs)+1)
			if *flagKillTgt && rng.Intn(2) == 0 {
				k2 = killK + rng.Intn(min(len(evs), 60)+1)
			}
			spec := crashsim.Spec{K: k2, Model: *flagModel, Seed: rng.Int63n(1<<30) + 1, Garbage: garbage}
			next := filepath.Join(base, fmt.Sprintf("r%d", inc+1))
			if err := os.Mkdir(next, 0o700); err != nil {
				t.Fatal(err)
			}
			if err := cm.Build(spec, next); err != nil {
				t.Fatalf("%s: build composed %v: %v", name, spec, err)
			}
			trail = append(trail, fmt.Sprintf("power loss after the kill at %d+%d seed=%d", killK, k2-killK, spec.Seed))
			tl.killPL++
			killM = nil
			root = next
			continue
		}
		mdl.SetEvents(evs)
		ws := oracleWrites(evs)
		k, where := len(evs), "end"
		if len(ws) > 0 && rng.Intn(8) != 0 {
			i := rng.Intn(len(ws))
			end := len(evs)
			if i+1 < len(ws) {
				end = ws[i+1]
			}
			cs := counted(evs, ws[i], end)
			j := rng.Intn(len(cs) + 1)
			k = ws[i] + 1
			if j > 0 {
				k = cs[j-1] + 1
			}
			where = fmt.Sprintf("write %d+%d", i, j)
		}
		if *flagTarget && inc%2 == 1 && rng.Intn(4) != 0 {
			k, where = len(evs), "end"
		}
		if *flagTarget && inc%2 == 0 && len(ws) > 0 && rng.Intn(4) != 0 {
			var ds []int
			for _, mm := range dormantRe.FindAllStringSubmatch(stderr.String(), -1) {
				n, _ := strconv.Atoi(mm[1])
				if n < len(ws) {
					ds = append(ds, n)
				}
			}
			if len(ds) > 0 {
				i := ds[rng.Intn(len(ds))]
				end := len(evs)
				if i+1 < len(ws) {
					end = ws[i+1]
				}
				cs := counted(evs, ws[i], end)
				j := 0
				if rng.Intn(2) == 0 {
					j = rng.Intn(len(cs) + 1)
				}
				k = ws[i] + 1
				if j > 0 {
					k = cs[j-1] + 1
				}
				where = fmt.Sprintf("dormant write %d+%d", i, j)
				tl.dormantCrashes++
			}
		}
		spec := crashsim.Spec{K: k, Model: *flagModel, Seed: rng.Int63n(1<<30) + 1, Garbage: garbage}
		if os.Getenv("W3BDUMP") != "" {
			t.Logf("EVS inc %d: %d events", inc, len(evs))
			for i, e := range evs {
				if e.Kind != crashsim.KWrite {
					t.Logf("EV inc %d %d: %v %s->%s ino=%d parent=%d", inc, i, e.Kind, e.Name, e.Name2, e.Ino, e.Parent)
				}
			}
		}
		var dirOps []int
		if *flagKillDir != "" {
			for i, e := range evs {
				mk := e.Kind == crashsim.KMkdir && (e.Name == "data" || e.Name == "member")
				cr := e.Kind == crashsim.KRename && e.Name == "wal.tmp"
				cu := e.Kind == crashsim.KRename && walTmpName.MatchString(e.Name) && strings.HasSuffix(e.Name2, ".wal")
				switch *flagKillDir {
				case "mkdir":
					cr, cu = false, false
				case "create":
					mk, cu = false, false
				case "cut":
					mk, cr = false, false
				}
				if mk || cr || cu {
					dirOps = append(dirOps, i)
				}
			}
		}
		if *flagKillPL > 0 && *flagModel != crashsim.Kill && inc+1 < *flagInc && (*flagKillDir == "" || len(dirOps) > 0) && rng.Float64() < *flagKillPL {
			if len(dirOps) > 0 {
				i := dirOps[rng.Intn(len(dirOps))]
				k = i + 1
				e := evs[i]
				where = fmt.Sprintf("after %v %s->%s at %d", e.Kind, e.Name, e.Name2, k)
				tl.killDir++
			} else if *flagKillTgt && rng.Intn(4) != 0 {
				var wr []int
				for i, e := range evs {
					if e.Kind == crashsim.KWrite && strings.HasSuffix(e.Path, ".wal") {
						wr = append(wr, i)
					}
				}
				if len(wr) > 0 {
					k = wr[rng.Intn(len(wr))] + 1
					where = fmt.Sprintf("after WAL write at %d", k)
				}
			}
			spec = crashsim.Spec{K: k, Model: crashsim.Kill}
			killM, killK = mdl, k
			where = "kill " + where
		}
		next := filepath.Join(base, fmt.Sprintf("r%d", inc+1))
		if err := os.Mkdir(next, 0o700); err != nil {
			t.Fatal(err)
		}
		if err := mdl.Build(spec, next); err != nil {
			t.Fatalf("%s: build %v: %v", name, spec, err)
		}
		if killM != nil {
			if killInos, err = crashsim.KillInodes(killM, killK, next); err != nil {
				t.Fatalf("%s: kill inodes: %v", name, err)
			}
		}
		trail = append(trail, fmt.Sprintf("%s seed=%d", where, spec.Seed))
		root = next
	}
}

func TestRobust(t *testing.T) {
	scratch := *flagScratch
	if scratch == "" {
		scratch = os.TempDir()
	}
	tl := &tally{}
	for c := 0; c < *flagChains; c++ {
		runChain(t, *flagSeed+int64(c), scratch, tl)
	}
	t.Logf("model=%s fz=%v fn=%v purgeok=%v: chains %d, incarnations %d (first starts %d, restarts checked ok %d), down at a restart %d (walRead of the image's records: none %d, defined %d), down at the first start %d; Saves with entries %d, WalSaveOk misses %d; harness errors %d, violations %d; target=%v: dormant-window crashes %d, restarts strict-rejected/relaxed-accepted %d in %d chains; kill-then-power-loss crashes %d (killdir=%q: kills after a directory op %d)",
		*flagModel, *flagFZ, *flagFN, *flagPurgeOK, tl.chains, tl.incs, tl.firstStarts, tl.restartsOK, tl.downRestart, tl.downNone, tl.downDefined, tl.downOther, tl.saves, tl.saveOkMiss, len(tl.infra), len(tl.violations), *flagTarget, tl.dormantCrashes, tl.purgeHits, tl.hitChains, tl.killPL, *flagKillDir, tl.killDir)
	for _, v := range tl.infra {
		t.Logf("HARNESS %s", v)
	}
	for _, v := range tl.violations {
		t.Logf("VIOLATION %s", v)
	}
	if len(tl.violations) > 0 {
		t.Errorf("%d violations", len(tl.violations))
	}
}

// segSizeFor picks the WAL's segment size for an incarnation (the driver's, WAL W4c T-1: Boot
// no longer writes the wal package's variable): the default, or small enough for cuts.
func segSizeFor(seed uint64) int64 {
	switch seed % 3 {
	case 0:
		return 64 * 1000 * 1000
	case 1:
		return 8 * 1024
	}
	return 4 * 1024
}

// walSaveOk is WalSaveOk (WalRecs.lean): the entries are consecutive, the first above the base
// and at most one past the last entry. Not checked by the tester (it is the Save law's premise);
// exported to the crash driver, which reports how often raft-like Saves after a restart miss it.
func walSaveOk(s contents, es []entry) bool {
	if len(es) == 0 {
		return true
	}
	e0 := es[0].index
	if e0 <= s.baseIdx || e0 > s.baseIdx+uint64(len(s.ents))+1 {
		return false
	}
	for j := 0; j < len(es); j++ {
		if es[j].index != e0+uint64(j) {
			return false
		}
	}
	return true
}
