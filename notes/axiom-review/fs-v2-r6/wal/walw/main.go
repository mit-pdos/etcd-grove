// fs-v2-r6 wal: etcd's real WAL (go.etcd.io/etcd/server/v3/storage/wal) under the e2e harness.
//
//	walw run DIR SECS SEED MINB MAXB [DMNAME]
//	    wal.Create(DIR), then for SECS seconds w.Save(hs, ents) as etcd's raft loop does: each
//	    Save appends entries totalling MINB..MAXB bytes of data (1 to 8 entries, consecutive
//	    indexes, nonzero data determined by the index) with HardState{Term 1, Vote 1, Commit};
//	    one Save in four carries no entry and only a new Commit (raft.MustSync is false: etcd
//	    leaves it in the encoder's buffer). After every Save that synced, a dm-log-writes mark
//	    "s<SEED>:<last index>" on device DMNAME (if given), so a crash point knows which entries
//	    were acknowledged as durable. Stops early before the segment (256 MiB) is full.
//	    Env RESTART=N: every N synced Saves, Close and reopen (wal.Open + ReadAll, as bootstrap
//	    does; ReadAll's ZeroToEnd is not synced); RGAP=US: then a random wait up to US us.
//	walw tornsim DIR NSAVES MINB MAXB SEED
//	    the images a mechanism-A tear leaves, for every flush of such a WAL, checked as below.
//	walw sync SECS DIR...
//	    another process's writeback: sync_file_range(SYNC_FILE_RANGE_WRITE) of every *.wal file
//	    of the DIRs in a tight loop (starts writeback, does not wait), as e2e's tearw sync.
//	walw check DIR SYNCED
//	    etcd's bootstrap (openWALFromSnapshot): wal.Open + ReadAll; on io.ErrUnexpectedEOF
//	    wal.Repair once and again. Prints one line: clean / repaired / FAIL (the error that makes
//	    etcd Fatal), the last entry index read, and LOSS if it is below SYNCED (an entry whose
//	    synced Save returned is missing) or BAD if an entry's data is not what was written.
package main

import (
	"errors"
	"fmt"
	"io"
	"math/rand"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"time"
	"unsafe"

	"go.uber.org/zap"
	"golang.org/x/sys/unix"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// SegmentSizeBytes: one segment for a whole run (no cut), so that the scan follows one file.
const segBytes = 256 << 20

func entData(idx uint64, n int) []byte {
	b := make([]byte, n)
	for j := range b {
		b[j] = byte((idx*131+uint64(j)*7)%255) + 1
	}
	return b
}

func main() {
	wal.SegmentSizeBytes = segBytes
	switch os.Args[1] {
	case "run":
		run()
	case "sync":
		syncer()
	case "check":
		check()
	case "tornsim":
		tornsim()
	}
}

// dm-log-writes mark through the device-mapper ioctl (what `dmsetup message NAME 0 mark M` does).
type dmIoctl struct {
	Version     [3]uint32
	DataSize    uint32
	DataStart   uint32
	TargetCount uint32
	OpenCount   int32
	Flags       uint32
	EventNr     uint32
	Padding     uint32
	Dev         uint64
	Name        [128]byte
	UUID        [129]byte
	Data        [7]byte
}

type marker struct {
	fd  int
	buf []byte
}

func newMarker(name string) *marker {
	fd, err := unix.Open("/dev/mapper/control", unix.O_RDWR, 0)
	if err != nil {
		panic(err)
	}
	return &marker{fd: fd, buf: make([]byte, 1024)}
}

func (m *marker) mark(s string) {
	const hdr = int(unsafe.Sizeof(dmIoctl{}))
	for i := range m.buf {
		m.buf[i] = 0
	}
	d := (*dmIoctl)(unsafe.Pointer(&m.buf[0]))
	d.Version = [3]uint32{4, 0, 0}
	d.DataSize = uint32(len(m.buf))
	d.DataStart = uint32(hdr)
	copy(d.Name[:], dmName)
	msg := "mark " + s
	copy(m.buf[hdr+8:], msg) // struct dm_target_msg { u64 sector; char message[]; }
	const DM_TARGET_MSG = 0xc138fd0e
	if _, _, e := unix.Syscall(unix.SYS_IOCTL, uintptr(m.fd), DM_TARGET_MSG, uintptr(unsafe.Pointer(&m.buf[0]))); e != 0 {
		panic(fmt.Sprintf("dm mark: %v", e))
	}
}

var dmName string

func run() {
	dir := os.Args[2]
	secs, _ := strconv.Atoi(os.Args[3])
	seed, _ := strconv.Atoi(os.Args[4])
	minb, _ := strconv.Atoi(os.Args[5])
	maxb, _ := strconv.Atoi(os.Args[6])
	var mk *marker
	if len(os.Args) > 7 {
		dmName = os.Args[7]
		mk = newMarker(dmName)
	}
	lg := zap.NewNop()
	w, err := wal.Create(lg, dir, []byte("walw"))
	if err != nil {
		panic(err)
	}
	r := rand.New(rand.NewSource(int64(seed)))
	var idx, commit uint64
	saves, synced, bytes, restarts := 0, 0, 0, 0
	restart, _ := strconv.Atoi(os.Getenv("RESTART"))
	rgap, _ := strconv.Atoi(os.Getenv("RGAP")) // us: a random wait up to RGAP after each reopen
	end := time.Now().Add(time.Duration(secs) * time.Second)
	for time.Now().Before(end) && bytes < segBytes*8/10 { // stop before the segment is full (no cut)
		var ents []*raftpb.Entry
		if r.Intn(4) != 0 {
			total := minb + r.Intn(maxb-minb+1)
			k := 1 + r.Intn(8)
			for i := 0; i < k; i++ {
				idx++
				n := total / k
				ents = append(ents, &raftpb.Entry{Term: new(uint64(1)), Index: new(idx), Type: new(raftpb.EntryNormal), Data: entData(idx, n)})
				bytes += n
			}
		}
		if commit < idx {
			commit += uint64(1 + r.Intn(int(idx-commit)))
		}
		hs := &raftpb.HardState{Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(commit)}
		if err := w.Save(hs, ents); err != nil {
			panic(err)
		}
		saves++
		if len(ents) > 0 { // raft.MustSync: entries (or a new term/vote) make the Save sync
			synced++
			if mk != nil {
				mk.mark("s" + os.Args[4] + ":" + strconv.FormatUint(idx, 10))
			}
			if restart > 0 && synced%restart == 0 {
				// etcd's restart: Close, then bootstrap's wal.Open + ReadAll, which in write mode
				// zeroes the tail from the last record on (fileutil.ZeroToEnd: truncate +
				// preallocate, no sync); the next Save's flush rewrites that tail page.
				if err := w.Close(); err != nil {
					panic(err)
				}
				if w, err = wal.Open(lg, dir, &walpb.Snapshot{}); err != nil {
					panic(err)
				}
				_, _, ents, err := w.ReadAll()
				if err != nil {
					panic(err)
				}
				if len(ents) == 0 || ents[len(ents)-1].GetIndex() != idx {
					panic("reopen: wrong last index")
				}
				restarts++
				if rgap > 0 { // the bootstrap's work between ReadAll and the first Save
					t := time.Now().Add(time.Duration(r.Intn(rgap)) * time.Microsecond)
					for time.Now().Before(t) {
					}
				}
			}
		}
	}
	if err := w.Close(); err != nil {
		panic(err)
	}
	fmt.Printf("run %s: %d saves (%d synced), %d entries, %d data bytes, %d restarts\n", dir, saves, synced, idx, bytes, restarts)
}

func syncer() {
	secs, _ := strconv.Atoi(os.Args[2])
	dirs := os.Args[3:]
	end := time.Now().Add(time.Duration(secs) * time.Second)
	calls := 0
	fds := map[string]int{}
	for time.Now().Before(end) {
		for _, d := range dirs {
			ms, _ := filepath.Glob(filepath.Join(d, "*.wal"))
			for _, p := range ms {
				fd, ok := fds[p]
				if !ok {
					var err error
					if fd, err = unix.Open(p, unix.O_RDONLY, 0); err != nil {
						continue
					}
					fds[p] = fd
				}
				for i := 0; i < 64; i++ {
					unix.SyncFileRange(fd, 0, 0, unix.SYNC_FILE_RANGE_WRITE)
					calls++
				}
			}
		}
	}
	fmt.Printf("sync: %d sync_file_range calls\n", calls)
}

func check() {
	synced, _ := strconv.ParseUint(os.Args[3], 10, 64)
	line, code := checkDir(os.Args[2], synced)
	fmt.Println(line)
	os.Exit(code)
}

// checkDir is etcd's bootstrap of the WAL (openWALFromSnapshot) on dir: the line says what it
// did; the code is 0 (etcd starts), 2 (etcd exits: Fatal "failed to read WAL, cannot be
// repaired", or open/repair failed) or 3 (it starts, but a synced entry is missing or wrong).
func checkDir(dir string, synced uint64) (string, int) {
	lg := zap.NewNop()
	repaired := false
	var rerr error
	for {
		w, err := wal.Open(lg, dir, &walpb.Snapshot{})
		if err != nil {
			return fmt.Sprintf("FAIL open: %v", err), 2
		}
		_, st, ents, err := w.ReadAll()
		if err != nil {
			w.Close()
			if repaired || !errors.Is(err, io.ErrUnexpectedEOF) {
				return fmt.Sprintf("FAIL read (etcd: \"failed to read WAL, cannot be repaired\"): %v", err), 2
			}
			rerr = err
			if !wal.Repair(lg, dir) {
				return fmt.Sprintf("FAIL repair: %v", err), 2
			}
			repaired = true
			continue
		}
		w.Close()
		var last uint64
		bad := ""
		for i, e := range ents {
			if e.GetIndex() != uint64(i+1) {
				bad = fmt.Sprintf(" BAD index %d at %d", e.GetIndex(), i)
				break
			}
			if string(e.Data) != string(entData(e.GetIndex(), len(e.Data))) {
				bad = fmt.Sprintf(" BAD data of %d", e.GetIndex())
				break
			}
			last = e.GetIndex()
		}
		loss := ""
		if last < synced {
			loss = fmt.Sprintf(" LOSS (synced %d)", synced)
		}
		kind := "clean"
		if repaired {
			kind = "repaired (" + rerr.Error() + ")"
		}
		code := 0
		if loss != "" || bad != "" {
			code = 3
		}
		return fmt.Sprintf("%s: last %d, commit %d%s%s", kind, last, st.GetCommit(), loss, bad), code
	}
}

// tornsim DIR NSAVES MINB MAXB SEED: what a mechanism-A tear (a copy cut at a source page boundary
// of the encoder's page-aligned buffer) leaves, for every flush of a WAL. It writes a WAL as `run`
// does (NSAVES Saves, no marks), recording each synced Save's flush [a, b) (the file offsets before
// and after it, from /proc/self/fdinfo), then for every flush and every cut c = a + 4096*m < b (the
// buffer's page boundaries; m >= 1) builds the image an A tear leaves when the flush's earlier
// pages also reached the disk: the file's bytes up to c, zeros after (the preallocated segment),
// and runs checkDir on it (synced: the entries of the Saves before this one).
func tornsim() {
	dir := os.Args[2]
	nsaves, _ := strconv.Atoi(os.Args[3])
	minb, _ := strconv.Atoi(os.Args[4])
	maxb, _ := strconv.Atoi(os.Args[5])
	seed, _ := strconv.Atoi(os.Args[6])
	wal.SegmentSizeBytes = 64 << 20
	lg := zap.NewNop()
	os.RemoveAll(dir)
	w, err := wal.Create(lg, dir, []byte("walw"))
	if err != nil {
		panic(err)
	}
	ms, _ := filepath.Glob(filepath.Join(dir, "*.wal"))
	path := ms[0]
	pos := func() int64 { // the WAL tail's file offset, from the fd that has the segment open
		fds, _ := os.ReadDir("/proc/self/fd")
		for _, f := range fds {
			if l, _ := os.Readlink("/proc/self/fd/" + f.Name()); l == path {
				b, _ := os.ReadFile("/proc/self/fdinfo/" + f.Name())
				var p int64
				fmt.Sscanf(string(b), "pos:\t%d", &p)
				return p
			}
		}
		panic("no fd")
	}
	type flush struct {
		a, b   int64
		synced uint64
	}
	var fl []flush
	r := rand.New(rand.NewSource(int64(seed)))
	var idx, commit, lastSynced uint64
	prev := pos()
	for s := 0; s < nsaves; s++ {
		var ents []*raftpb.Entry
		if r.Intn(4) != 0 {
			total := minb + r.Intn(maxb-minb+1)
			k := 1 + r.Intn(8)
			for i := 0; i < k; i++ {
				idx++
				ents = append(ents, &raftpb.Entry{Term: new(uint64(1)), Index: new(idx), Type: new(raftpb.EntryNormal), Data: entData(idx, total/k)})
			}
		}
		if commit < idx {
			commit += uint64(1 + r.Intn(int(idx-commit)))
		}
		hs := &raftpb.HardState{Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(commit)}
		if err := w.Save(hs, ents); err != nil {
			panic(err)
		}
		if len(ents) > 0 {
			p := pos()
			fl = append(fl, flush{prev, p, lastSynced})
			prev, lastSynced = p, idx
		}
	}
	w.Close()
	F, _ := os.ReadFile(path)
	size := int64(len(F))
	img := dir + ".img"
	counts := map[string]int{}
	ncut, shown := 0, 0
	for _, f := range fl {
		for c := f.a + 4096; c < f.b; c += 4096 {
			if f.a%4096 == 0 {
				break // buffer and file aligned: the cut is at a file page boundary (no tear)
			}
			ncut++
			os.RemoveAll(img)
			os.MkdirAll(img, 0o700)
			g, _ := os.Create(filepath.Join(img, filepath.Base(path)))
			g.Write(F[:c])
			g.Truncate(size)
			g.Close()
			line, code := checkDir(img, f.synced)
			kind := line
			if i := strings.IndexAny(line, ":("); i >= 0 {
				kind = strings.TrimSpace(line[:i])
			}
			if code == 2 {
				kind = "FAIL"
			}
			kind += fmt.Sprintf(" (cut%%512 %s)", map[bool]string{true: "= 0", false: "!= 0"}[c%512 == 0])
			counts[kind]++
			if code != 0 && shown < 5 {
				shown++
				fmt.Printf("flush [%d, %d), cut %d (in-page %d): %s\n", f.a, f.b, c, c%4096, line)
			}
		}
	}
	os.RemoveAll(img)
	fmt.Printf("tornsim: %d saves, %d synced flushes, %d cuts at a source page boundary: %v\n", nsaves, len(fl), ncut, counts)
}
