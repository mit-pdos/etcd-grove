package crashsim

import (
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"sort"
	"syscall"
)

const sector = 512

// Times: the initial state is at time -1 (durable); event i happens at time i. A crash "at K"
// keeps the effects of events 0..K-1 in the page cache.

type secVer struct {
	t int
	d []byte // sector content (len sector), nil = zeros
}

type ver64 struct {
	t int
	v int64
}

type fileHist struct {
	ino   uint64
	sizes []ver64
	secs  map[int64][]secVer
	syncs []int // times of fsync/fdatasync
	birth int
}

type nsOp struct {
	t   int
	ev  Event
	idx int // index among namespace ops
}

// Model is a recorded trace over an initial durable state.
type Model struct {
	Events   []Event
	rootIno  uint64
	files    map[uint64]*fileHist
	isDir    map[uint64]bool
	initNS   map[uint64]map[string]uint64 // dir ino -> entries, initial
	nsOps    []nsOp
	dirSyncs map[uint64][]int
	// journal commit points (for the ordered model): times of syncs that commit the journal
	jcommits []int
	cur      map[uint64]uint64
	next     uint64
	// FZ: treat ZeroToEnd (ftruncate then fallocate mode 0 of the same inode) as followed by
	// fdatasync (the fork fix F-Z).
	FZ bool
	// FN1: treat the rename of a directory named "wal.tmp" as preceded by an fsync of that
	// directory (the fork fix F-N1: wal.Create fsyncs wal.tmp before renaming it to wal).
	FN1 bool
	// FN2: treat every mkdir as followed by an fsync of its parent (the fork fix F-N2:
	// fileutil.TouchDirAll fsyncs the parent of each directory it creates).
	FN2 bool
	// WeakP4: garbage may garble every byte of a changed sector, its synced bytes included (the
	// superseded weaker P4). Default (the user's assumption, 2026-11-11): a garbled sector keeps
	// every byte that no write since the last sync changed; only rewritten bytes become random.
	WeakP4 bool
}

// Scan scans root (the initial state, taken as durable), before the traced run.
func Scan(root string, fz bool) (*Model, error) {
	m := &Model{files: map[uint64]*fileHist{}, isDir: map[uint64]bool{},
		initNS: map[uint64]map[string]uint64{}, dirSyncs: map[uint64][]int{}, FZ: fz}
	var st syscall.Stat_t
	if err := syscall.Lstat(root, &st); err != nil {
		return nil, err
	}
	m.cur = map[uint64]uint64{}
	m.rootIno = m.idOf(st.Ino)
	if err := m.scan(root, m.rootIno); err != nil {
		return nil, err
	}
	return m, nil
}

// SetEvents attaches the recorded events (once).
func (m *Model) SetEvents(events []Event) {
	m.Events = events
	m.renumber()
	m.index()
}

func (m *Model) scan(dir string, ino uint64) error {
	m.isDir[ino] = true
	ents := map[string]uint64{}
	m.initNS[ino] = ents
	des, err := os.ReadDir(dir)
	if err != nil {
		return err
	}
	for _, de := range des {
		p := filepath.Join(dir, de.Name())
		var st syscall.Stat_t
		if err := syscall.Lstat(p, &st); err != nil {
			return err
		}
		id := m.idOf(st.Ino)
		ents[de.Name()] = id
		if de.IsDir() {
			if err := m.scan(p, id); err != nil {
				return err
			}
			continue
		}
		data, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		f := &fileHist{ino: id, secs: map[int64][]secVer{}, birth: -1}
		f.sizes = []ver64{{-1, int64(len(data))}}
		for off := int64(0); off < int64(len(data)); off += sector {
			end := min(off+sector, int64(len(data)))
			d := make([]byte, sector)
			copy(d, data[off:end])
			if !allZero(d) {
				f.secs[off/sector] = []secVer{{-1, d}}
			}
		}
		m.files[id] = f
	}
	return nil
}

// idOf maps an inode number to the model's id of the file it currently names (inode numbers are
// reused after an unlink: each create or mkdir gets a fresh id).
func (m *Model) idOf(ino uint64) uint64 {
	if ino == 0 {
		return 0
	}
	if id, ok := m.cur[ino]; ok {
		return id
	}
	m.next++
	m.cur[ino] = m.next
	return m.next
}

func (m *Model) renumber() {
	evs := make([]Event, len(m.Events))
	for i, e := range m.Events {
		e.Parent = m.idOf(e.Parent)
		e.Parent2 = m.idOf(e.Parent2)
		e.Replaced = m.idOf(e.Replaced)
		if e.Kind == KCreate || e.Kind == KMkdir {
			m.next++
			m.cur[e.Ino] = m.next
		}
		e.Ino = m.idOf(e.Ino)
		evs[i] = e
	}
	m.Events = evs
}

func allZero(b []byte) bool {
	for _, x := range b {
		if x != 0 {
			return false
		}
	}
	return true
}

func (f *fileHist) size() int64 { return f.sizes[len(f.sizes)-1].v }

func (f *fileHist) setSize(t int, s int64) {
	if f.size() != s {
		f.sizes = append(f.sizes, ver64{t, s})
	}
}

func (f *fileHist) cur(s int64) []byte {
	vs := f.secs[s]
	if len(vs) == 0 {
		return nil
	}
	return vs[len(vs)-1].d
}

func (f *fileHist) put(t int, s int64, d []byte) {
	if d != nil && allZero(d) {
		d = nil
	}
	old := f.cur(s)
	if old == nil && d == nil {
		return
	}
	f.secs[s] = append(f.secs[s], secVer{t, d})
}

func (m *Model) file(ino uint64, t int) *fileHist {
	f := m.files[ino]
	if f == nil {
		f = &fileHist{ino: ino, sizes: []ver64{{t, 0}}, secs: map[int64][]secVer{}, birth: t}
		m.files[ino] = f
	}
	return f
}

func (m *Model) index() {
	sizeAtSync := map[uint64]int64{}
	created := map[uint64]bool{}
	lastTrunc := map[uint64]int{}
	lastOn := map[uint64]int{} // the last event on each inode (another goroutine's may come between)
	for i, e := range m.Events {
		switch e.Kind {
		case KWrite:
			f := m.file(e.Ino, i)
			for off := e.Off; off < e.Off+int64(len(e.Data)); {
				s := off / sector
				so := off % sector
				n := min(int64(sector)-so, e.Off+int64(len(e.Data))-off)
				d := make([]byte, sector)
				if c := f.cur(s); c != nil {
					copy(d, c)
				}
				copy(d[so:so+n], e.Data[off-e.Off:off-e.Off+n])
				f.put(i, s, d)
				off += n
			}
			f.setSize(i, max(f.size(), e.Off+int64(len(e.Data))))
		case KTrunc:
			f := m.file(e.Ino, i)
			keys := make([]int64, 0)
			for s := range f.secs {
				if s*sector+sector > e.Size {
					keys = append(keys, s)
				}
			}
			for _, s := range keys {
				c := f.cur(s)
				if c == nil {
					continue
				}
				d := make([]byte, sector)
				if s*sector < e.Size {
					copy(d, c[:e.Size-s*sector])
				}
				f.put(i, s, d)
			}
			f.setSize(i, e.Size)
			lastTrunc[e.Ino] = i
		case KFalloc:
			f := m.file(e.Ino, i)
			if e.Mode == 0 {
				f.setSize(i, max(f.size(), e.Size))
			}
			if m.FZ && e.Mode == 0 {
				if lt, ok := lastTrunc[e.Ino]; ok && lastOn[e.Ino] == lt {
					// F-Z: ZeroToEnd is followed by Fdatasync
					f.syncs = append(f.syncs, i)
				}
			}
		case KSync:
			if e.Dir {
				m.dirSyncs[e.Ino] = append(m.dirSyncs[e.Ino], i)
				m.jcommits = append(m.jcommits, i)
			} else {
				f := m.file(e.Ino, i)
				f.syncs = append(f.syncs, i)
				// the journal commits on fsync, or on fdatasync of a file whose size changed
				// (or that was created) since its last sync
				if !e.DataOnly || created[e.Ino] || sizeAtSync[e.Ino] != f.size() {
					m.jcommits = append(m.jcommits, i)
				}
				sizeAtSync[e.Ino] = f.size()
				created[e.Ino] = false
			}
		case KCreate:
			m.file(e.Ino, i)
			created[e.Ino] = true
			m.nsOps = append(m.nsOps, nsOp{i, e, len(m.nsOps)})
		case KMkdir:
			m.isDir[e.Ino] = true
			m.nsOps = append(m.nsOps, nsOp{i, e, len(m.nsOps)})
			if m.FN2 {
				// a directory sync at the mkdir's own time covers it (nsAt(t+1))
				m.dirSyncs[e.Parent] = append(m.dirSyncs[e.Parent], i)
				m.jcommits = append(m.jcommits, i)
			}
		case KUnlink, KRename:
			if e.Kind == KRename && m.FN1 && e.Name == "wal.tmp" {
				// the renamed directory's own entries, durable before the rename
				m.dirSyncs[e.Ino] = append(m.dirSyncs[e.Ino], i)
				m.jcommits = append(m.jcommits, i)
			}
			m.nsOps = append(m.nsOps, nsOp{i, e, len(m.nsOps)})
		}
		if e.Kind != KMarker {
			lastOn[e.Ino] = i
		}
	}
}

// Model kinds.
const (
	Kill    = "kill"
	Posix   = "posix"
	Ordered = "ordered"
)

// Spec names one crash image.
type Spec struct {
	K     int    // crash after events 0..K-1
	Model string // Kill, Posix, Ordered
	Seed  int64  // 0: the deterministic "all synced only" image for Posix/Ordered
	// Garbage: probability that an unsynced changed sector comes back as random bytes (P4)
	Garbage float64
}

func (s Spec) String() string { return fmt.Sprintf("%s@K=%d/seed=%d", s.Model, s.K, s.Seed) }

func lastLE(ts []int, k int) int {
	r := -1
	for _, t := range ts {
		if t < k {
			r = t
		}
	}
	return r
}

func applyNS(ns map[uint64]map[string]uint64, e Event) {
	get := func(d uint64) map[string]uint64 {
		if ns[d] == nil {
			ns[d] = map[string]uint64{}
		}
		return ns[d]
	}
	switch e.Kind {
	case KCreate, KMkdir:
		get(e.Parent)[e.Name] = e.Ino
		if e.Kind == KMkdir {
			get(e.Ino)
		}
	case KUnlink:
		if get(e.Parent)[e.Name] == e.Ino {
			delete(get(e.Parent), e.Name)
		}
	case KRename:
		if get(e.Parent)[e.Name] == e.Ino {
			delete(get(e.Parent), e.Name)
		}
		get(e.Parent2)[e.Name2] = e.Ino
	}
}

func cloneNS(ns map[uint64]map[string]uint64) map[uint64]map[string]uint64 {
	out := map[uint64]map[string]uint64{}
	for d, es := range ns {
		c := map[string]uint64{}
		for k, v := range es {
			c[k] = v
		}
		out[d] = c
	}
	return out
}

// nsAt is the namespace after the namespace ops with time < k.
func (m *Model) nsAt(k int) map[uint64]map[string]uint64 {
	ns := cloneNS(m.initNS)
	for _, o := range m.nsOps {
		if o.t >= k {
			break
		}
		applyNS(ns, o.ev)
	}
	return ns
}

func touches(o nsOp, d uint64) bool {
	return o.ev.Parent == d || (o.ev.Kind == KRename && o.ev.Parent2 == d)
}

// namespace picks the image's namespace.
func (m *Model) namespace(s Spec, rng *rand.Rand) map[uint64]map[string]uint64 {
	switch s.Model {
	case Kill:
		return m.nsAt(s.K)
	case Ordered:
		// a prefix of the namespace ops, at least up to the last journal commit before K
		jc := lastLE(m.jcommits, s.K)
		lo, hi := 0, 0
		for _, o := range m.nsOps {
			if o.t < jc {
				lo++
			}
			if o.t < s.K {
				hi++
			}
		}
		c := lo
		if rng != nil && hi > lo {
			c = lo + rng.Intn(hi-lo+1)
		}
		ns := cloneNS(m.initNS)
		for _, o := range m.nsOps[:c] {
			applyNS(ns, o.ev)
		}
		return ns
	case Posix:
		// per directory: its entries as of its last fsync before K, then an order-preserving
		// subsequence of its later namespace ops (a rename within one directory is atomic)
		ns := map[uint64]map[string]uint64{}
		dirs := make([]uint64, 0, len(m.isDir))
		for d := range m.isDir {
			dirs = append(dirs, d)
		}
		sort.Slice(dirs, func(i, j int) bool { return dirs[i] < dirs[j] })
		for _, d := range dirs {
			ls := lastLE(m.dirSyncs[d], s.K)
			full := m.nsAt(ls + 1)
			ents := map[string]uint64{}
			for k, v := range full[d] {
				ents[k] = v
			}
			one := map[uint64]map[string]uint64{d: ents}
			for _, o := range m.nsOps {
				if o.t <= ls || o.t >= s.K || !touches(o, d) {
					continue
				}
				if rng == nil || rng.Intn(2) == 0 {
					continue
				}
				e := o.ev
				// apply only this directory's half of the op
				switch {
				case e.Kind == KRename && e.Parent != e.Parent2:
					if e.Parent == d && ents[e.Name] == e.Ino {
						delete(ents, e.Name)
					}
					if e.Parent2 == d {
						ents[e.Name2] = e.Ino
					}
				default:
					applyNS(one, e)
				}
			}
			ns[d] = one[d]
		}
		return ns
	}
	panic("model " + s.Model)
}

// fileImage picks one file's content.
func (m *Model) fileImage(f *fileHist, s Spec, rng *rand.Rand) (int64, map[int64][]byte) {
	out := map[int64][]byte{}
	if f.birth >= s.K {
		return 0, out
	}
	lo := -1
	if s.Model != Kill {
		lo = lastLE(f.syncs, s.K)
	}
	verAt := func(vs []secVer, t int) []byte {
		var d []byte
		for _, v := range vs {
			if v.t <= t {
				d = v.d
			}
		}
		return d
	}
	sizeAt := func(t int) int64 {
		var z int64
		for _, v := range f.sizes {
			if v.t <= t {
				z = v.v
			}
		}
		return z
	}
	hiT := s.K - 1
	var size int64
	mode := 0 // 0 new, 1 old, 2 random per sector, 3 prefix tear
	var tear int64
	if s.Model == Kill {
		size = sizeAt(hiT)
	} else {
		if rng == nil {
			mode = 1
		} else {
			mode = rng.Intn(4)
		}
		cands := []int64{sizeAt(lo)}
		for _, v := range f.sizes {
			if v.t > lo && v.t <= hiT {
				cands = append(cands, v.v)
			}
		}
		switch mode {
		case 0:
			size = cands[len(cands)-1]
		case 1:
			size = cands[0]
		default:
			size = cands[rng.Intn(len(cands))]
		}
		if mode == 3 {
			var maxs int64
			for sec := range f.secs {
				maxs = max(maxs, sec)
			}
			tear = rng.Int63n(maxs + 2)
		}
	}
	keys := make([]int64, 0, len(f.secs))
	for k := range f.secs {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool { return keys[i] < keys[j] })
	for _, sec := range keys {
		if sec*sector >= size {
			continue
		}
		vs := f.secs[sec]
		var d []byte
		if s.Model == Kill {
			d = verAt(vs, hiT)
		} else {
			cands := [][]byte{verAt(vs, lo)}
			for _, v := range vs {
				if v.t > lo && v.t <= hiT {
					cands = append(cands, v.d)
				}
			}
			switch mode {
			case 0:
				d = cands[len(cands)-1]
			case 1:
				d = cands[0]
			case 2:
				d = cands[rng.Intn(len(cands))]
			case 3:
				if sec < tear {
					d = cands[len(cands)-1]
				} else {
					d = cands[0]
				}
			}
			if len(cands) > 1 && s.Garbage > 0 && rng != nil && rng.Float64() < s.Garbage {
				g := make([]byte, sector)
				rng.Read(g)
				if !m.WeakP4 {
					for b := 0; b < sector; b++ {
						same := true
						for _, c := range cands[1:] {
							if byteAt(c, b) != byteAt(cands[0], b) {
								same = false
							}
						}
						if same {
							g[b] = byteAt(cands[0], b)
						}
					}
				}
				d = g
			}
		}
		if d != nil {
			out[sec] = d
		}
	}
	return size, out
}

// Build materializes the image s into the (empty, existing) directory dst, which stands for the
// recorded root.
func (m *Model) Build(s Spec, dst string) error {
	var rng *rand.Rand
	if s.Seed != 0 {
		rng = rand.New(rand.NewSource(s.Seed))
	}
	ns := m.namespace(s, rng)
	seen := map[uint64]bool{}
	var walk func(d uint64, path string) error
	walk = func(d uint64, path string) error {
		if seen[d] {
			return nil
		}
		seen[d] = true
		names := make([]string, 0)
		for n := range ns[d] {
			names = append(names, n)
		}
		sort.Strings(names)
		for _, n := range names {
			ino := ns[d][n]
			p := filepath.Join(path, n)
			if m.isDir[ino] {
				if err := os.Mkdir(p, 0o700); err != nil {
					return err
				}
				if err := walk(ino, p); err != nil {
					return err
				}
				continue
			}
			fh := m.files[ino]
			out, err := os.OpenFile(p, os.O_CREATE|os.O_WRONLY|os.O_EXCL, 0o600)
			if err != nil {
				return err
			}
			if fh != nil {
				size, secs := m.fileImage(fh, s, rng)
				if err := out.Truncate(size); err != nil {
					return err
				}
				for sec, d := range secs {
					n := min(int64(sector), size-sec*sector)
					if _, err := out.WriteAt(d[:n], sec*sector); err != nil {
						return err
					}
				}
			}
			if err := out.Close(); err != nil {
				return err
			}
		}
		return nil
	}
	return walk(m.rootIno, dst)
}

// Markers returns the markers with their event times.
func (m *Model) Markers() []MarkerAt {
	var out []MarkerAt
	for i, e := range m.Events {
		if e.Kind == KMarker {
			out = append(out, MarkerAt{i, e.Marker})
		}
	}
	return out
}

// MarkerAt is a marker and its time.
type MarkerAt struct {
	T int
	S string
}

// byteAt is a sector version's byte b (absent bytes read as 0).
func byteAt(d []byte, b int) byte {
	if b < len(d) {
		return d[b]
	}
	return 0
}
