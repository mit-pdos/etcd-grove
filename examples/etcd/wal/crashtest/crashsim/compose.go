package crashsim

import (
	"fmt"
	"os"
	"path/filepath"
	"syscall"
)

// Compose models a kill followed, without a reboot, by a second run and then a power loss.
// m is the model of the first run (SetEvents done); the first process was killed after event k
// (its page cache kept: the files are m's Kill image at k, built into root1), and a second
// process was traced on root1 (ev2: raw events, root1's inode numbers). The result is one model
// over m's initial durable state with m's events before k followed by ev2 (times shifted by k):
// any image of it is what a power loss at that time can leave (the first run's unsynced writes
// stay unsynced until something syncs them).
// KillInodes maps the raw inode numbers of root1, just built as m's Kill image at k (before the
// second run touches it), to m's ids of the same paths.
func KillInodes(m *Model, k int, root1 string) (map[uint64]uint64, error) {
	cur := map[uint64]uint64{}
	ns := m.nsAt(k)
	var walk func(d uint64, path string) error
	walk = func(d uint64, path string) error {
		var st syscall.Stat_t
		if err := syscall.Lstat(path, &st); err != nil {
			return err
		}
		cur[st.Ino] = d
		for n, id := range ns[d] {
			p := filepath.Join(path, n)
			if m.isDir[id] {
				if err := walk(id, p); err != nil {
					return err
				}
				continue
			}
			var fst syscall.Stat_t
			if err := syscall.Lstat(p, &fst); err != nil {
				return err
			}
			cur[fst.Ino] = id
		}
		return nil
	}
	return cur, walk(m.rootIno, root1)
}

func Compose(m *Model, k int, inos map[uint64]uint64, ev2 []Event) (*Model, error) {
	c := &Model{files: map[uint64]*fileHist{}, isDir: map[uint64]bool{}, initNS: m.initNS,
		dirSyncs: map[uint64][]int{}, cur: map[uint64]uint64{}, next: m.next, rootIno: m.rootIno,
		FZ: m.FZ, FN1: m.FN1, FN2: m.FN2, WeakP4: m.WeakP4}
	for d := range m.isDir {
		c.isDir[d] = true
	}
	// the initial (durable) files: their versions at time -1 only
	for id, f := range m.files {
		if f.birth != -1 {
			continue
		}
		g := &fileHist{ino: id, secs: map[int64][]secVer{}, birth: -1}
		for _, v := range f.sizes {
			if v.t == -1 {
				g.sizes = append(g.sizes, v)
			}
		}
		for s, vs := range f.secs {
			for _, v := range vs {
				if v.t == -1 {
					g.secs[s] = append(g.secs[s], v)
				}
			}
		}
		c.files[id] = g
	}
	for raw, id := range inos {
		c.cur[raw] = id
	}
	evs := append([]Event{}, m.Events[:k]...)
	for _, e := range ev2 {
		e.Parent = c.idOf(e.Parent)
		e.Parent2 = c.idOf(e.Parent2)
		e.Replaced = c.idOf(e.Replaced)
		if e.Kind == KCreate || e.Kind == KMkdir {
			c.next++
			c.cur[e.Ino] = c.next
		}
		e.Ino = c.idOf(e.Ino)
		evs = append(evs, e)
	}
	c.Events = evs
	if os.Getenv("W3COMPOSEDEBUG") != "" {
		ns2 := m.nsAt(k)
		for i, e := range evs[k:] {
			if e.Kind == KUnlink || e.Kind == KRename {
				fmt.Fprintf(os.Stderr, "COMPOSE ev %d %v ino=%d parent=%d name=%s ns-has=%d\n", i, e.Kind, e.Ino, e.Parent, e.Name, ns2[e.Parent][e.Name])
			}
		}
		fmt.Fprintf(os.Stderr, "COMPOSE cur=%v\n", c.cur)
	}
	c.index()
	return c, nil
}
