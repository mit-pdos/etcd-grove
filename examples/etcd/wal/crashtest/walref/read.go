package walref

import (
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"
)

// Outcome kinds of a restart.
const (
	OK    = "ok"    // the restart read Contents
	Fresh = "fresh" // wal.Exist is false: bootstrap starts a fresh member
	Err   = "err"   // bootstrap returns an error (ValidSnapshotEntries failed)
	Fatal = "fatal" // bootstrap Fatals (Open, ReadAll, Repair failed)
	Panic = "panic" // a Go panic in the read path
)

// Outcome is the result of bootstrap's restart read path on a WAL directory.
type Outcome struct {
	Kind     string
	C        Contents
	Err      string
	Repaired bool
}

func (o Outcome) String() string {
	if o.Kind == OK {
		r := ""
		if o.Repaired {
			r = " (repaired)"
		}
		return "ok " + o.C.Key() + r
	}
	return o.Kind + ": " + o.Err
}

func u64(x uint64) *uint64 { return &x }

// FromEntry converts a raft entry.
func FromEntry(e *raftpb.Entry) Ent {
	return Ent{Index: e.GetIndex(), Term: e.GetTerm(), Data: string(e.GetData())}
}

// FromHS converts a hard state.
func FromHS(h *raftpb.HardState) HS {
	return HS{Term: h.GetTerm(), Vote: h.GetVote(), Commit: h.GetCommit()}
}

// RestartRead is bootstrap's restart (etcdserver/bootstrap.go: wal.Exist, recoverSnapshot's
// ValidSnapshotEntries and newestSnapshotEntry, openWALFromSnapshot's Open, ReadAll, Repair once).
// If keep, the WAL is returned open (ready to append); otherwise it is closed.
func RestartRead(lg *zap.Logger, walDir string, keep bool) (out Outcome, w *wal.WAL) {
	defer func() {
		if r := recover(); r != nil {
			out = Outcome{Kind: Panic, Err: fmt.Sprint(r)}
			w = nil
		}
	}()
	if !wal.Exist(walDir) {
		return Outcome{Kind: Fresh, Err: "wal.Exist false"}, nil
	}
	snaps, err := wal.ValidSnapshotEntries(lg, walDir)
	if err != nil {
		return Outcome{Kind: Err, Err: "ValidSnapshotEntries: " + err.Error()}, nil
	}
	walsnap := &walpb.Snapshot{Index: u64(0), Term: u64(0)}
	if len(snaps) > 0 {
		idx := 0
		for i, s := range snaps {
			if s.GetIndex() >= snaps[idx].GetIndex() {
				idx = i
			}
		}
		walsnap = &walpb.Snapshot{Index: u64(snaps[idx].GetIndex()), Term: u64(snaps[idx].GetTerm())}
	}
	repaired := false
	for {
		w, err := wal.Open(lg, walDir, walsnap)
		if err != nil {
			return Outcome{Kind: Fatal, Err: "Open: " + err.Error()}, nil
		}
		_, st, ents, err := w.ReadAll()
		if err != nil {
			w.Close()
			if repaired || !errors.Is(err, io.ErrUnexpectedEOF) {
				return Outcome{Kind: Fatal, Err: "ReadAll: " + err.Error(), Repaired: repaired}, nil
			}
			if !wal.Repair(lg, walDir) {
				return Outcome{Kind: Fatal, Err: "Repair failed: " + err.Error()}, nil
			}
			repaired = true
			continue
		}
		c := Contents{HS: FromHS(st), BaseIdx: walsnap.GetIndex(), BaseTerm: walsnap.GetTerm()}
		for _, e := range ents {
			c.Ents = append(c.Ents, FromEntry(e))
		}
		if !keep {
			w.Close()
			w = nil
		}
		return Outcome{Kind: OK, C: c, Repaired: repaired}, w
	}
}

// walNames is readWALNames: the valid WAL file names, sorted.
func walNames(dir string) []string {
	des, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	var out []string
	for _, de := range des {
		var seq, idx uint64
		if strings.HasSuffix(de.Name(), ".wal") {
			if _, err := fmt.Sscanf(de.Name(), "%016x-%016x.wal", &seq, &idx); err == nil {
				out = append(out, de.Name())
			}
		}
	}
	sort.Strings(out)
	return out
}

// Decoded is the records an image's WAL files decode to, as validSnapshotEntries reads them (from
// the first file, through the CRC chain), with the CRC and metadata records, the Create's
// snapshot record and each cut's repeated state record left out.
type Decoded struct {
	Recs   []Rec
	Purged bool   // the first file is not the WAL's first (seq > 0)
	End    string // how decoding ended
	Files  []string
}

// DecodeDir decodes the WAL directory's records.
func DecodeDir(walDir string) Decoded {
	names := walNames(walDir)
	d := Decoded{Files: names}
	if len(names) == 0 {
		d.End = "no wal files"
		return d
	}
	var seq0 uint64
	fmt.Sscanf(names[0], "%016x", &seq0)
	d.Purged = seq0 > 0
	var rs []fileutil.FileReader
	for _, n := range names {
		f, err := os.Open(filepath.Join(walDir, n))
		if err != nil {
			d.End = err.Error()
			return d
		}
		defer f.Close()
		rs = append(rs, fileutil.NewFileReader(f))
	}
	dec := wal.NewDecoder(rs...)
	rec := &walpb.Record{}
	var last HS
	pos := 0 // position in the current file (a CRC record starts a file)
	fileNo := -1
	for {
		err := dec.Decode(rec)
		if err != nil {
			d.End = err.Error()
			if errors.Is(err, io.EOF) {
				d.End = "EOF"
			}
			return d
		}
		switch rec.GetType() {
		case 4: // crc
			crc := dec.LastCRC()
			if crc != 0 && rec.Validate(crc) != nil {
				d.End = "crc mismatch at a file head"
				return d
			}
			dec.UpdateCRC(rec.GetCrc())
			pos = 0
			fileNo++
		case 1: // metadata
		case 2: // entry
			e := wal.MustUnmarshalEntry(rec.Data)
			d.Recs = append(d.Recs, Rec{Kind: 'e', E: FromEntry(e)})
		case 3: // state
			h := FromHS(wal.MustUnmarshalState(rec.Data))
			if pos == 2 && (fileNo > 0 || d.Purged) && h == last {
				break // a cut's repeated state
			}
			last = h
			d.Recs = append(d.Recs, Rec{Kind: 's', HS: h})
		case 5: // snapshot
			var s walpb.Snapshot
			if err := proto.Unmarshal(rec.Data, &s); err != nil {
				d.End = err.Error()
				return d
			}
			if pos == 2 && fileNo == 0 && !d.Purged && s.GetIndex() == 0 && s.GetTerm() == 0 {
				break // Create's record (walFresh)
			}
			d.Recs = append(d.Recs, Rec{Kind: 'n', Idx: s.GetIndex(), Term: s.GetTerm()})
		}
		pos++
	}
}
