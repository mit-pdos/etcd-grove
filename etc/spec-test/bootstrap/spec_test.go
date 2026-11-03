// Spec-guided tests of `bootstrap`'s trusted contracts (the whole-`bootOk` review, 2026-11-03;
// README.md says how to run them). This file is copied into the package `etcdserver` of etcd at the
// pinned revision (run.sh), so that it can call the unexported `bootstrap` and read the record it
// returns.
//
// Two kinds of run, each in both compaction modes (a compaction run or none) and both auth modes
// (auth enabled or not), at the examples' configuration (`examples/common/common.go`'s `newServer`,
// `cfgOk`):
//
//   - a fresh boot: `bootstrap` on an empty data directory; every conjunct of `bootOk`
//     (Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean) that Go can show is checked of its
//     result (the modes change nothing of a fresh directory; they are run to show it);
//   - a restart: a server is built and started (`NewServer`, `Start`), writes keys, compacts (the
//     compaction mode), enables auth (the auth mode), stops (`Stop`); then `bootstrap` runs on its
//     directory. The image's premises of `bootstrapRestartContract`
//     (Proof/.../etcdserver/InvRestart.lean, `srvDiskImage`) are checked of the stopped directory,
//     and `bootOkR`'s conjuncts of the result.
//
// The data `D` the contracts name is the bbolt file's contents at `bootstrap`'s return (read back
// after the record's `Close`, which commits): `bootOk`'s `newPost … D`, `HD`, `HDr`, `HmEmpty`,
// and, at a restart, also the file before `bootstrap` (`srvFiles … D`): the test checks the two
// are equal.
//
// Each check is named by the Lean conjunct it transcribes (keep the two in step). Some are known
// to be false of Go (`knownFalse`): the test fails if one of them holds (so the list stays honest)
// or if any other check fails. It prints the table of every check in every run.
package etcdserver

import (
	"context"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"
	"time"
	"unsafe"

	bolt "go.etcd.io/bbolt"
	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3"
)

// dbData is a bbolt file's contents: bucket name to its keys' values; a bucket absent is absent.
type dbData map[string]map[string]string

func readDB(t *testing.T, path string) dbData {
	db, err := bolt.Open(path, 0o600, &bolt.Options{ReadOnly: true, Timeout: 5 * time.Second})
	if err != nil {
		t.Fatalf("open %s: %v", path, err)
	}
	defer db.Close()
	d := dbData{}
	err = db.View(func(tx *bolt.Tx) error {
		return tx.ForEach(func(name []byte, b *bolt.Bucket) error {
			m := map[string]string{}
			d[string(name)] = m
			return b.ForEach(func(k, v []byte) error { m[string(k)] = string(v); return nil })
		})
	})
	if err != nil {
		t.Fatal(err)
	}
	return d
}

// emptyOrAbsent is `(D.lookup n).getD ∅ = ∅`.
func (d dbData) emptyOrAbsent(n string) bool { return len(d[n]) == 0 }

// presentEmpty is `D.lookup n = some ∅`.
func (d dbData) presentEmpty(n string) bool { b, ok := d[n]; return ok && len(b) == 0 }

func (d dbData) metaU64(k string) (uint64, bool) {
	v, ok := d["meta"][k]
	if !ok || len(v) != 8 {
		return 0, false
	}
	return binary.BigEndian.Uint64([]byte(v)), true
}

// restBuckets is `mvcc.restBuckets` (the buckets restore reads besides `key` and `meta`).
var restBuckets = []string{"lease", "auth", "authUsers", "authRoles", "members", "members_removed", "cluster", "alarm"}

// field reads an unexported field (the record's and other packages' private state).
func field(v any, name string) reflect.Value {
	rv := reflect.ValueOf(v)
	for rv.Kind() == reflect.Pointer || rv.Kind() == reflect.Interface {
		rv = rv.Elem()
	}
	f := rv.FieldByName(name)
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem()
}

type check struct {
	name  string
	holds bool
	why   string
}

type run struct {
	name   string
	checks []check
}

func (r *run) add(name string, holds bool, format string, args ...any) {
	r.checks = append(r.checks, check{name, holds, fmt.Sprintf(format, args...)})
}

// knownFalse: conjuncts found false of Go, by run kind (`restart`) and mode; the test fails if one
// of them holds. (The whole-`bootOk` review's A, T1-B, C and G were repaired on 2026-11-03: their
// checks below are the frozen statements'. What remains is H, out of the review's repairs: a restart's
// image certificate assumes auth disabled, `notes/STATUS.md`'s auth-on gap.)
func knownFalse(restart, cmp, auth bool, name string) bool {
	return restart && auth && name == "srvDiskImage.imageAt.bkRestAt(auth)"
}

func specConfig(t *testing.T, dir, name string) config.ServerConfig {
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:1"}}
	return config.ServerConfig{
		Name:                name,
		DataDir:             filepath.Join(dir, name+".etcd"),
		InitialPeerURLsMap:  types.URLsMap{name: peer},
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: "127.0.0.1:2"}},
		InitialClusterToken: name,
		NewCluster:          true,
		TickMs:              100,
		ElectionTicks:       10,
		// a WAL snapshot record within the run (σ.b > 0 at the restart)
		SnapshotCount:          8,
		SnapshotCatchUpEntries: 4,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate(name, lg),
	}
}

// openLimit is `storage.openLimit`.
func openLimit(cfg config.ServerConfig) int {
	if cfg.BackendBatchLimit == 0 {
		return 10000
	}
	return cfg.BackendBatchLimit
}

// checkRecord checks the conjuncts shared by `bootOk` and `bootOkR` of the record `b` (before its
// `Close`), and returns the raft node's id.
func checkRecord(r *run, cfg config.ServerConfig, b *bootstrappedServer) uint64 {
	_, ok := b.prt.(*http.Transport)
	r.add("Hprt", ok, "prt is %T", b.prt)
	r.add("HwalR/Hwalo", b.storage.wal.w != nil, "wal opened")
	r.add("Hss", b.ss != nil, "snapshotter")
	cv := b.raft.config
	r.add("Hraft(lg, heartbeat)", b.raft.lg != nil && b.raft.heartbeat != 0, "heartbeat %v", b.raft.heartbeat)
	r.add("Hraft(config fields)",
		cv.MaxInflightMsgs < 1<<62 && !cv.DisableProposalForwarding && cv.ReadOnlyOption == raft.ReadOnlySafe &&
			!cv.DisableConfChangeValidation && (cv.MaxCommittedSizePerReady != 0 || cv.MaxSizePerMsg != 0) &&
			!cv.AsyncStorageWrites && cv.Logger != nil && cv.CheckQuorum && cv.PreVote == cfg.PreVote,
		"%+v", *cv)
	r.add("Hraft(Applied = 0)", cv.Applied == 0, "Applied %d", cv.Applied)
	r.add("Hraft(Storage = b.raft.storage)", cv.Storage == raft.Storage(b.raft.storage), "")
	r.add("Hid", uint64(b.cluster.nodeID) == cv.ID, "nodeID %v, config ID %x", b.cluster.nodeID, cv.ID)
	r.add("Hclg", !field(b.cluster.cl, "lg").IsNil(), "cluster logger")
	r.add("Hrms0", len(b.cluster.remotes) == 0, "remotes %d", len(b.cluster.remotes))
	// `Members()` sorted by id, each member's peer URLs the directory's (`memberDirIs`)
	ms := b.cluster.cl.Members()
	ids := make([]uint64, len(ms))
	dirOk := true
	for i, m := range ms {
		ids[i] = uint64(m.ID)
		if want, ok := cfg.InitialPeerURLsMap[m.Name]; !ok || strings.Join(m.PeerURLs, ",") != want.String() {
			dirOk = false
		}
	}
	r.add("Hmembers(sorted, directory URLs)", sort.SliceIsSorted(ids, func(i, j int) bool { return ids[i] < ids[j] }) && dirOk,
		"members %v", ids)
	in := false
	for _, id := range ids {
		in = in || id == cv.ID
	}
	r.add("Hraft(ID ∈ ps, ps ≠ [], 0 ∉ ps)", in && len(ids) > 0 && ids[0] != 0, "ids %v", ids)
	// the consistent index: `bootstrapBackend`'s `cindex.NewConsistentIndex`, the applying index
	// at 0 (`Happ`)
	r.add("Hci", fmt.Sprintf("%T", b.storage.backend.ci) == "*cindex.consistentIndex", "%T", b.storage.backend.ci)
	ai, at := b.storage.backend.ci.ConsistentApplyingIndex()
	r.add("Happ", ai == 0 && at == 0, "applying (%d, %d)", ai, at)
	// the backend: `*backend.backend` with the server's hooks, at `openLimit cfg`
	be := b.storage.backend.be
	r.add("Hbe(type)", fmt.Sprintf("%T", be) == "*backend.backend", "%T", be)
	r.add("Hbe(limit = openLimit cfg)", int(field(be, "batchLimit").Int()) == openLimit(cfg),
		"batchLimit %d", field(be, "batchLimit").Int())
	h := field(be, "hooks").Interface()
	r.add("HhkAt/Hbh", h == any(b.storage.backend.beHooks) && b.storage.backend.beHooks != nil, "hooks %T", h)
	// `Hnew`'s `newPostK … (bootLeft N)`: `N + 7` write-back tokens left past the `bootWB`
	// `bootstrap`'s own sessions spent (each session's `Unlock` writes back once, raising the read
	// buffer's version, `txReadBuffer.bufVersion`, `InvBuffer.lean`'s `R.ver`; the batch lock's
	// invariant `bgOk`, `ver + n + k < 2 ^ 40`, with the contract's `N + 7 + bootWB ≤ wbInit`); the
	// `run` goroutine's commits are unpaid. (Until 2026-11-03 `newPost`'s every token, false: it
	// forced `bufVersion = 0`.) A clean read buffer (`bViewC … true`) has no buffered bucket.
	rbuf := field(field(be, "readTx").Interface(), "buf")
	ver := field(rbuf.Addr().Interface(), "bufVersion").Uint()
	cm := be.(interface{ Commits() int64 }).Commits()
	r.add("Hnew.bootLeft(bootstrap's write-backs ≤ bootWB = 4)", ver <= 4,
		"bufVersion %d, commits %d", ver, cm)
	nb := field(field(rbuf.Addr().Interface(), "txBuffer").Addr().Interface(), "buckets").Len()
	r.add("Hnew.newPostK(read buffer clean)", nb == 0, "read buffer buckets %d", nb)
	// the contracts' configuration premises (`bootCfgOk`), which the examples' configuration meets
	r.add("bootCfgOk", cfg.Logger != nil && cfg.QuotaBackendBytes == 0 && cfg.BackendBatchLimit == 0 &&
		cfg.BootstrapDefragThresholdMegabytes == 0 && cfg.ElectionTicks > 1 && cfg.TickMs != 0, "")
	return cv.ID
}

func checkFresh(t *testing.T, r *run, cmp, auth bool) {
	dir := t.TempDir()
	cfg := specConfig(t, dir, "m1")
	b, err := bootstrap(cfg)
	if err != nil {
		t.Fatal(err)
	}
	id := checkRecord(r, cfg, b)
	// the fresh storage (`Hlog0`, `Hend`, `Hsnone`, `Hmeta`, `Hfresh`)
	st := b.raft.storage
	fi, _ := st.FirstIndex()
	li, _ := st.LastIndex()
	hs, cs, _ := st.InitialState()
	sn, _ := st.Snapshot()
	r.add("Hlog0/Hend/Hmeta/Hfresh/Hsnone", fi == 1 && li == 0 && raft.IsEmptyHardState(hs) &&
		len(cs.GetVoters()) == 0 && sn.GetMetadata().GetIndex() == 0,
		"first %d last %d hs %v", fi, li, hs)
	// the peers (`Hraft`'s `ps = pv.map ID`, `Hctx`) and the members (`Hmem`: the contexts'
	// members, each with its peer's id)
	ps := make([]uint64, len(b.raft.peers))
	memOk := len(b.raft.peers) == len(b.cluster.cl.Members())
	for i, p := range b.raft.peers {
		ps[i] = p.ID
		var m membership.Member
		if json.Unmarshal(p.Context, &m) != nil || uint64(m.ID) != p.ID {
			memOk = false
			continue
		}
		cm := b.cluster.cl.Member(m.ID)
		j1, _ := json.Marshal(cm)
		j2, _ := json.Marshal(&m)
		memOk = memOk && cm != nil && string(j1) == string(j2)
	}
	r.add("Hraft(peers, nodup)", len(ps) > 0 && len(ps) == len(b.cluster.cl.Members()), "peers %v", ps)
	r.add("Hmem(memBoot of the contexts)", memOk, "")
	ci := b.storage.backend.ci.ConsistentIndex()
	r.add("Hm0(ci = m0.1 = 0)", ci == 0, "ci %d", ci)
	walDir := cfg.WALDir()
	r.add("Hclose", func() bool { b.Close(); return true }(), "")
	b.storage.wal.w.Close()
	_ = id
	_ = walDir
	d := readDB(t, cfg.BackendPath())
	r.add("HD(key empty)", d.emptyOrAbsent("key"), "key %d keys", len(d["key"]))
	r.add("HmEmpty(meta empty)", d.emptyOrAbsent("meta"), "meta %v", d["meta"])
	restOk := true
	for _, n := range restBuckets {
		restOk = restOk && d.emptyOrAbsent(n)
	}
	r.add("HDr(rest empty, membership present)", restOk && d.presentEmpty("members") &&
		d.presentEmpty("members_removed") && d.presentEmpty("cluster"), "buckets %v", bucketNames(d))
	_, sch := d["meta"]["scheduledCompactRev"]
	_, fin := d["meta"]["finishedCompactRev"]
	r.add("Hnew.lateWB(unregistered: key empty)", d.emptyOrAbsent("key"), "")
	r.add("Hnew.lateWB(unregistered: no compaction keys)", !sch && !fin, "")
	r.add("bootBackend_of_bootLeft.noCmpData", !sch && !fin, "")
	// the first-start contract's configuration premise (`bootCfgFresh`)
	r.add("bootCfgFresh", cfg.NewCluster && len(cfg.DiscoveryCfg.Endpoints) == 0, "")
}

func bucketNames(d dbData) []string {
	var ns []string
	for n := range d {
		ns = append(ns, fmt.Sprintf("%s:%d", n, len(d[n])))
	}
	sort.Strings(ns)
	return ns
}

// writeAndStop runs a server on cfg's directory: puts, a compaction (cmp), auth enabled (auth),
// a graceful stop.
func writeAndStop(t *testing.T, cfg config.ServerConfig, cmp, auth bool) {
	s, err := NewServer(cfg)
	if err != nil {
		t.Fatal(err)
	}
	s.Start()
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	for s.Leader() == 0 {
		select {
		case <-ctx.Done():
			t.Fatal("no leader")
		case <-time.After(10 * time.Millisecond):
		}
	}
	var rev int64
	for i := 0; i < 20; i++ {
		resp, err := s.Put(ctx, &pb.PutRequest{Key: []byte(fmt.Sprintf("k%d", i%5)), Value: []byte(fmt.Sprintf("v%d", i))})
		if err != nil {
			t.Fatal(err)
		}
		rev = resp.GetHeader().GetRevision()
	}
	if cmp {
		if _, err := s.Compact(ctx, &pb.CompactionRequest{Revision: rev - 3, Physical: true}); err != nil {
			t.Fatal(err)
		}
	}
	if auth {
		if _, err := s.UserAdd(ctx, &pb.AuthUserAddRequest{Name: "root", Options: &authpb.UserAddOptions{NoPassword: true}}); err != nil {
			t.Fatal(err)
		}
		if _, err := s.RoleAdd(ctx, &pb.AuthRoleAddRequest{Name: "root"}); err != nil {
			t.Fatal(err)
		}
		if _, err := s.UserGrantRole(ctx, &pb.AuthUserGrantRoleRequest{User: "root", Role: "root"}); err != nil {
			t.Fatal(err)
		}
		if _, err := s.AuthEnable(ctx, &pb.AuthEnableRequest{}); err != nil {
			t.Fatal(err)
		}
	}
	s.Stop()
}

func checkRestart(t *testing.T, r *run, cmp, auth bool) {
	dir := t.TempDir()
	cfg := specConfig(t, dir, "m1")
	writeAndStop(t, cfg, cmp, auth)
	// the stopped directory (`srvDiskImage`, `srvFiles dd id σ D`)
	d0 := readDB(t, cfg.BackendPath())
	snaps, err := wal.ValidSnapshotEntries(zap.NewNop(), cfg.WALDir())
	if err != nil {
		t.Fatal(err)
	}
	var sb uint64
	for _, s := range snaps {
		sb = max(sb, s.GetIndex())
	}
	w, err := wal.OpenForRead(zap.NewNop(), cfg.WALDir(), &walpb.Snapshot{})
	if err != nil {
		t.Fatal(err)
	}
	md, hs, _, err := w.ReadAll()
	w.Close()
	if err != nil {
		t.Fatal(err)
	}
	var meta pb.Metadata
	pbutil.MustUnmarshalMessage(&meta, md)
	i, iok := d0.metaU64("consistent_index")
	_, tok := d0.metaU64("term")
	r.add("srvDiskImage(σ.b ≤ i ≤ σ.commit)", iok && sb <= i && i <= hs.GetCommit(),
		"σ.b %d, i %d, commit %d", sb, i, hs.GetCommit())
	r.add("srvDiskImage.imageAt(ci and term stored)", iok && tok, "")
	r.add("srvDiskImage(bootLen ≤ i)", i >= 1, "i %d", i)
	// the image's other buckets at the model's (`bkRestAt`): the auth bucket the boot state
	// `authBoot` (revision 1, auth disabled), lease and alarm empty
	ar := d0["auth"]["authRevision"]
	_, en := d0["auth"]["authEnabled"]
	r.add("srvDiskImage.imageAt.bkRestAt(auth)", !en && len(d0["auth"]) == 1 && ar == string([]byte{0, 0, 0, 0, 0, 0, 0, 1}) &&
		len(d0["authUsers"]) == 0 && len(d0["authRoles"]) == 0, "auth %d keys, users %d", len(d0["auth"]), len(d0["authUsers"]))
	r.add("srvDiskImage.imageAt.bkRestAt(lease, alarm empty)", len(d0["lease"]) == 0 && len(d0["alarm"]) == 0, "")

	b, err := bootstrap(cfg)
	if err != nil {
		t.Fatal(err)
	}
	id := checkRecord(r, cfg, b)
	r.add("bootOkR.Hraft(pv = [])", len(b.raft.peers) == 0, "peers %d", len(b.raft.peers))
	r.add("bootOkR.Hraft(cv.ID = the WAL's member id)", id == meta.GetNodeID(), "id %x, wal %x", id, meta.GetNodeID())
	ci := b.storage.backend.ci.ConsistentIndex()
	r.add("bootOkR.Hm0(ci = m0.1 = i)", ci == i, "ci %d, i %d", ci, i)
	// the members recovered from the image's buckets (`Hmem`, `restModel … .mem`)
	memOk := len(b.cluster.cl.Members()) == len(d0["members"])
	for k, v := range d0["members"] {
		id, _ := types.IDFromString(k)
		m := b.cluster.cl.Member(id)
		var raw membership.RaftAttributes
		memOk = memOk && m != nil && json.Unmarshal([]byte(v), &raw) == nil &&
			strings.Join(raw.PeerURLs, ",") == strings.Join(m.PeerURLs, ",")
	}
	r.add("bootOkR.Hmem(members of the image's bucket)", memOk, "members %d", len(d0["members"]))
	// the restart contract's static-cluster premise (G): the image's members are the boot log's at
	// the same peer URLs (names and client URLs may differ: `publishV3`)
	gOk := len(d0["members"]) == len(cfg.InitialPeerURLsMap)
	for _, v := range d0["members"] {
		var raw membership.RaftAttributes
		found := false
		if json.Unmarshal([]byte(v), &raw) == nil {
			for _, u := range cfg.InitialPeerURLsMap {
				found = found || strings.Join(raw.PeerURLs, ",") == u.String()
			}
		}
		gOk = gOk && found
	}
	r.add("bootstrapRestartContract(G: the members' peer URLs the boot log's)", gOk, "")
	b.Close()
	b.storage.wal.w.Close()
	d1 := readDB(t, cfg.BackendPath())
	r.add("bootOkR(D at return = srvFiles' D)", reflect.DeepEqual(d0, d1), "before %v after %v", bucketNames(d0), bucketNames(d1))
	_, sch := d1["meta"]["scheduledCompactRev"]
	_, fin := d1["meta"]["finishedCompactRev"]
	// `bootOkR`'s `Hnew` holds `lateWBR` (its unregistered arm at the data's values, whatever they
	// are: until 2026-11-03 `lateWB`, an empty `Key` bucket and no compaction keys, false here); the
	// facts below are informational, the reason for `lateWBR`
	r.add("bootOkR.Hnew.lateWBR(informational: key non-empty)", !d1.emptyOrAbsent("key"), "key %d keys", len(d1["key"]))
	r.add("bootOkR.Hnew.lateWBR(informational: compaction keys iff cmp)", (sch || fin) == cmp,
		"scheduled %v finished %v", sch, fin)
	// the restart contract's configuration premises
	r.add("bootstrapRestartContract(bootCfgOk, ForceNewCluster = false, DedicatedWALDir = \"\")",
		cfg.Logger != nil && cfg.BootstrapDefragThresholdMegabytes == 0 && !cfg.ForceNewCluster &&
			cfg.DedicatedWALDir == "", "")
	r.add("restPresent(rest buckets present)", func() bool {
		for _, n := range restBuckets {
			if _, ok := d1[n]; !ok {
				return false
			}
		}
		return true
	}(), "buckets %v", bucketNames(d1))
}

func TestSpecBootstrap(t *testing.T) {
	var runs []run
	fails := 0
	for _, restart := range []bool{false, true} {
		for _, cmp := range []bool{false, true} {
			for _, auth := range []bool{false, true} {
				r := run{name: fmt.Sprintf("restart=%v cmp=%v auth=%v", restart, cmp, auth)}
				if restart {
					checkRestart(t, &r, cmp, auth)
				} else {
					checkFresh(t, &r, cmp, auth)
				}
				for _, c := range r.checks {
					kf := knownFalse(restart, cmp, auth, c.name)
					if c.holds == kf {
						fails++
						t.Errorf("%s: %s: holds=%v (known false: %v) %s", r.name, c.name, c.holds, kf, c.why)
					}
				}
				runs = append(runs, r)
			}
		}
	}
	var sb strings.Builder
	for _, r := range runs {
		fmt.Fprintf(&sb, "== %s\n", r.name)
		for _, c := range r.checks {
			mark := "ok   "
			if !c.holds {
				mark = "FALSE"
			}
			fmt.Fprintf(&sb, "  %s %-55s %s\n", mark, c.name, c.why)
		}
	}
	t.Log("\n" + sb.String())
	if os.Getenv("SPEC_TABLE") != "" {
		_ = os.WriteFile(os.Getenv("SPEC_TABLE"), []byte(sb.String()), 0o644)
	}
}

// panics reports whether f panics.
func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return false
}

// TestSpecBootstrapFalseCases shows Go's behavior behind the review's findings C and D: `bootstrap`
// with a nil logger panics (C: since 2026-11-03 excluded by the contracts' `bootCfgOk`), and the
// record's `Close` panics the second time (D: `#Hclose` still promises it persistently, false; its
// repair, one-shot with the backend's whole open token, waits for the store's closers to give their
// reader tokens back, `notes/STATUS.md`).
func TestSpecBootstrapFalseCases(t *testing.T) {
	cfg := specConfig(t, t.TempDir(), "m1")
	cfg.Logger = nil
	if !panics(func() { _, _ = bootstrap(cfg) }) {
		t.Error("C: bootstrap with a nil logger did not panic")
	}
	cfg = specConfig(t, t.TempDir(), "m1")
	b, err := bootstrap(cfg)
	if err != nil {
		t.Fatal(err)
	}
	b.Close()
	if !panics(func() { b.Close() }) {
		t.Error("D: a second Close did not panic")
	}
	b.storage.wal.w.Close()
}
