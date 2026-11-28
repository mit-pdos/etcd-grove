package disk

import (
	"bytes"
	"io"
	"math/rand/v2"
	"testing"

	"github.com/hashicorp/raft"
)

// state is what a Disk's reads return (the log, the stable keys raft uses, the commit index).
func state(t *testing.T, d *Disk) string {
	var b bytes.Buffer
	first, _ := d.FirstIndex()
	last, _ := d.LastIndex()
	for i := first; first > 0 && i <= last; i++ {
		var l raft.Log
		if err := d.GetLog(i, &l); err == nil {
			b.WriteString(string(rune(l.Index)) + string(rune(l.Term)) + string(rune(l.Type)) + string(l.Data) + "|")
		}
	}
	for _, k := range []string{"CurrentTerm", "X"} {
		v, _ := d.GetUint64([]byte(k))
		b.WriteString(string(rune(v)))
	}
	if v, err := d.Get([]byte("LastVote")); err == nil {
		b.Write(v)
	} else {
		b.WriteString("none")
	}
	c, _ := d.GetCommitIndex()
	b.WriteString(string(rune(c)))
	return b.String()
}

// TestReopen: after random operations, Open of the directory reads back what the Disk serves.
func TestReopen(t *testing.T) {
	for seed := uint64(0); seed < 50; seed++ {
		rng := rand.New(rand.NewPCG(seed, 1))
		dir := t.TempDir()
		d := Fresh(dir)
		next := uint64(1)
		for op := 0; op < 60; op++ {
			switch rng.IntN(6) {
			case 0, 1:
				var ls []*raft.Log
				for k := rng.IntN(3); k >= 0; k-- {
					ls = append(ls, &raft.Log{Index: next, Term: uint64(rng.IntN(5)), Type: raft.LogCommand, Data: []byte{byte(rng.IntN(256))}})
					next++
				}
				d.StageCommitIndex(uint64(rng.IntN(int(next))))
				d.StoreLogs(ls)
			case 2:
				lo := uint64(rng.IntN(int(next) + 1))
				hi := lo + uint64(rng.IntN(4))
				d.DeleteRange(lo, hi)
				if last, _ := d.LastIndex(); last+1 < next && rng.IntN(2) == 0 {
					next = last + 1
				}
			case 3:
				d.SetUint64([]byte("CurrentTerm"), uint64(rng.IntN(100)))
			case 4:
				d.Set([]byte("LastVote"), []byte{byte(rng.IntN(256)), 'c'})
			case 5:
				d.SetUint64([]byte("X"), uint64(rng.IntN(100)))
			}
			d2, err := Open(dir)
			if err != nil {
				t.Fatal(err)
			}
			if a, b := state(t, d), state(t, d2); a != b {
				t.Fatalf("seed %d op %d: the Disk serves %q, its file %q", seed, op, a, b)
			}
		}
	}
}

// TestSnapsReopen: a closed snapshot is the latest after OpenSnaps, with its bytes; an older one
// closed later does not replace it; IDs are not reused across a reopen.
func TestSnapsReopen(t *testing.T) {
	dir := t.TempDir()
	s := FreshSnaps(dir)
	cfg := raft.Configuration{Servers: []raft.Server{{Suffrage: raft.Voter, ID: "1", Address: "1"}, {Suffrage: raft.Nonvoter, ID: "2", Address: "2"}}}
	k, _ := s.Create(1, 10, 3, cfg, 4, nil)
	k.Write([]byte("hello"))
	k.Close()
	old, _ := s.Create(1, 8, 3, cfg, 4, nil)
	old.Write([]byte("older"))
	old.Close()
	s2, err := OpenSnaps(dir)
	if err != nil {
		t.Fatal(err)
	}
	ms, _ := s2.List()
	if len(ms) != 1 || ms[0].Index != 10 || ms[0].Term != 3 || ms[0].ConfigurationIndex != 4 ||
		len(ms[0].Configuration.Servers) != 2 || ms[0].Configuration.Servers[1].Suffrage != raft.Nonvoter || ms[0].Size != 5 {
		t.Fatalf("List after reopen: %+v", ms)
	}
	_, rc, err := s2.Open(ms[0].ID)
	if err != nil {
		t.Fatal(err)
	}
	b, _ := io.ReadAll(rc)
	if string(b) != "hello" {
		t.Fatalf("snapshot bytes %q", b)
	}
	k3, _ := s2.Create(1, 12, 3, cfg, 4, nil)
	if k3.ID() == ms[0].ID || k3.ID() == old.ID() {
		t.Fatalf("ID %s reused", k3.ID())
	}
}
