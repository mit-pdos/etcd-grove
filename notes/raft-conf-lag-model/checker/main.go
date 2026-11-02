// Explicit-state BFS checker for the membership model of ../model.py.
// See README.md.
package main

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"flag"
	"fmt"
	"hash/maphash"
	"io"
	"os"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// ---- symmetry: permutations of {1..init} and of {init+1..N} ----

var perms [][MaxN + 1]int // perms[p][old id] = new id (p[0] = 0)
var useSym bool

func permute(xs []int) [][]int {
	if len(xs) <= 1 {
		return [][]int{append([]int(nil), xs...)}
	}
	var out [][]int
	for k := range xs {
		rest := append(append([]int(nil), xs[:k]...), xs[k+1:]...)
		for _, r := range permute(rest) {
			out = append(out, append([]int{xs[k]}, r...))
		}
	}
	return out
}

func initPerms() {
	// classes: initial voter or not, lagging or not; ids are permuted within a class
	var classes [4][]int
	for i := 1; i <= N; i++ {
		c := 0
		if i > NInit {
			c = 2
		}
		if LagMask&bit(i) != 0 {
			c++
		}
		classes[c] = append(classes[c], i)
	}
	perms = [][MaxN + 1]int{{}}
	for _, cl := range classes {
		ps := permute(cl)
		if !useSym {
			ps = [][]int{cl}
		}
		var out [][MaxN + 1]int
		for _, p := range perms {
			for _, x := range ps {
				q := p
				for k, v := range cl {
					q[v] = x[k]
				}
				out = append(out, q)
			}
		}
		perms = out
	}
}

func permEnt(e uint16, p *[MaxN + 1]int) uint16 {
	if eKind(e) != KC {
		return e
	}
	switch eOp(e) {
	case OpAdd, OpRem:
		return e&0xff00 | uint16(p[eArg(e)])
	case OpEnter:
		var m int
		for j := 1; j <= N; j++ {
			if eArg(e)&(1<<(j-1)) != 0 {
				m |= 1 << (p[j] - 1)
			}
		}
		return e&0xff00 | uint16(m)
	}
	return e
}

// encode appends the encoding of s with node ids renamed by p.
func encode(buf []byte, s *State, p *[MaxN + 1]int) []byte {
	var inv [MaxN + 1]int
	for i := 1; i <= N; i++ {
		inv[p[i]] = i
	}
	for ni := 1; ni <= N; ni++ {
		n := &s.Nodes[inv[ni]-1]
		buf = append(buf, n.Term, n.Role, n.Len, n.Commit, n.Applied, n.CfgIdx, n.Pending, n.PCommit)
		for k := 1; k <= N; k++ {
			buf = append(buf, n.Match[inv[k]-1])
		}
		for _, e := range n.Log[:n.Len] {
			e = permEnt(e, p)
			buf = append(buf, byte(e>>8), byte(e))
		}
	}
	return append(buf, s.NC, s.NV, s.Won, byte(p[s.RdNode]), s.RdTerm, s.RdIdx, s.RdMax)
}

var seed = maphash.MakeSeed()

// fingerprint of the canonical (lexicographically least) encoding over the group.
func fingerprint(s *State, b1, b2 []byte) uint64 {
	best := encode(b1[:0], s, &perms[0])
	for k := 1; k < len(perms); k++ {
		c := encode(b2[:0], s, &perms[k])
		if bytes.Compare(c, best) < 0 {
			best, c = c, best
			b1, b2 = b2, b1
		}
	}
	h := maphash.Bytes(seed, best)
	if h == 0 {
		h = 1
	}
	return h
}

// ---- visited set: open addressing on fingerprints, with the parent's slot ----

type Table struct {
	fps     []uint64
	parents []uint32
	mask    uint64
	count   atomic.Int64
}

const noParent = ^uint32(0)

var noParents bool

func newTable(logSize uint) *Table {
	n := uint64(1) << logSize
	t := &Table{fps: make([]uint64, n), mask: n - 1}
	if !noParents {
		t.parents = make([]uint32, n)
	}
	return t
}

// insert returns the slot and whether fp was new.
func (t *Table) insert(fp uint64, parent uint32) (uint32, bool) {
	i := fp & t.mask
	for {
		cur := atomic.LoadUint64(&t.fps[i])
		if cur == fp {
			return uint32(i), false
		}
		if cur == 0 {
			if atomic.CompareAndSwapUint64(&t.fps[i], 0, fp) {
				if t.parents != nil {
					t.parents[i] = parent
				}
				t.count.Add(1)
				return uint32(i), true
			}
			continue
		}
		i = (i + 1) & t.mask
	}
}

func (t *Table) lookup(fp uint64) (uint32, bool) {
	i := fp & t.mask
	for {
		cur := t.fps[i]
		if cur == fp {
			return uint32(i), true
		}
		if cur == 0 {
			return 0, false
		}
		i = (i + 1) & t.mask
	}
}

// Frontier states are stored packed (4 bits per field, 16 per log entry) after
// their slot in the visited table.
type Chunk struct {
	data []byte
	n    int
}

const chunkBytes = 1 << 16

var spillDir string

// Level is one BFS level's states: chunks in memory, or (-spill) one file per worker
// of length-prefixed chunks.
type Level struct {
	mu    sync.Mutex
	mem   []*Chunk
	files []string
	n     int
	k     int // next chunk (memory) or file (spilled)
	f     *os.File
	rd    *bufio.Reader
}

func (l *Level) next() *Chunk {
	l.mu.Lock()
	defer l.mu.Unlock()
	if l.files == nil {
		if l.k >= len(l.mem) {
			return nil
		}
		c := l.mem[l.k]
		l.mem[l.k] = nil // free as we go
		l.k++
		return c
	}
	for {
		if l.rd == nil {
			if l.k >= len(l.files) {
				return nil
			}
			f, err := os.Open(l.files[l.k])
			if err != nil {
				panic(err)
			}
			l.f, l.rd = f, bufio.NewReaderSize(f, 1<<20)
			l.k++
		}
		var hdr [8]byte
		if _, err := io.ReadFull(l.rd, hdr[:]); err != nil {
			l.f.Close()
			os.Remove(l.f.Name())
			l.f, l.rd = nil, nil
			continue
		}
		ln := binary.LittleEndian.Uint32(hdr[:4])
		c := &Chunk{data: make([]byte, ln), n: int(binary.LittleEndian.Uint32(hdr[4:]))}
		if _, err := io.ReadFull(l.rd, c.data); err != nil {
			panic(err)
		}
		return c
	}
}

func (l *Level) release() {
	l.mem = nil
	for _, f := range l.files {
		os.Remove(f)
	}
}

type levelWriter struct {
	lv  *Level
	cur *Chunk
	f   *os.File
	bw  *bufio.Writer
}

func newLevelWriter(lv *Level, depth, w int) *levelWriter {
	lw := &levelWriter{lv: lv, cur: &Chunk{data: make([]byte, 0, chunkBytes+256)}}
	if spillDir != "" {
		name := fmt.Sprintf("%s/level%d-w%d", spillDir, depth, w)
		f, err := os.Create(name)
		if err != nil {
			panic(err)
		}
		lw.f, lw.bw = f, bufio.NewWriterSize(f, 1<<20)
		lv.mu.Lock()
		lv.files = append(lv.files, name)
		lv.mu.Unlock()
	}
	return lw
}

func (lw *levelWriter) flush() {
	if lw.cur.n == 0 {
		return
	}
	lw.lv.mu.Lock()
	lw.lv.n += lw.cur.n
	if lw.bw == nil {
		lw.lv.mem = append(lw.lv.mem, lw.cur)
	}
	lw.lv.mu.Unlock()
	if lw.bw != nil {
		var hdr [8]byte
		binary.LittleEndian.PutUint32(hdr[:4], uint32(len(lw.cur.data)))
		binary.LittleEndian.PutUint32(hdr[4:], uint32(lw.cur.n))
		lw.bw.Write(hdr[:])
		lw.bw.Write(lw.cur.data)
		lw.cur.data, lw.cur.n = lw.cur.data[:0], 0
	} else {
		lw.cur = &Chunk{data: make([]byte, 0, chunkBytes+256)}
	}
}

func (lw *levelWriter) add(slot uint32, ns *State) {
	if len(lw.cur.data) > chunkBytes {
		lw.flush()
	}
	lw.cur.data = pack(lw.cur.data, slot, ns)
	lw.cur.n++
}

func (lw *levelWriter) close() {
	lw.flush()
	if lw.bw != nil {
		if err := lw.bw.Flush(); err != nil {
			panic(err)
		}
		lw.f.Close()
	}
}

type nib struct {
	b    []byte
	half bool
}

func (w *nib) put(x uint8) {
	if w.half {
		w.b[len(w.b)-1] |= x << 4
	} else {
		w.b = append(w.b, x&15)
	}
	w.half = !w.half
}

func pack(buf []byte, slot uint32, s *State) []byte {
	buf = append(buf, byte(slot), byte(slot>>8), byte(slot>>16), byte(slot>>24))
	w := nib{b: buf}
	for i := 0; i < N; i++ {
		n := &s.Nodes[i]
		for _, x := range [...]uint8{n.Term, n.Role, n.Len, n.Commit, n.Applied, n.CfgIdx, n.Pending, n.PCommit} {
			w.put(x)
		}
		for k := 0; k < N; k++ {
			w.put(n.Match[k])
		}
		for _, e := range n.Log[:n.Len] {
			w.put(uint8(e >> 12))
			w.put(uint8(e>>8) & 15)
			w.put(uint8(e>>4) & 15)
			w.put(uint8(e) & 15)
		}
	}
	for _, x := range [...]uint8{s.NC, s.NV, s.Won & 15, s.Won >> 4, s.RdNode, s.RdTerm, s.RdIdx, s.RdMax} {
		w.put(x)
	}
	return w.b
}

func unpack(b []byte, off int, s *State) (uint32, int) {
	slot := uint32(b[off]) | uint32(b[off+1])<<8 | uint32(b[off+2])<<16 | uint32(b[off+3])<<24
	pos := (off + 4) * 2
	get := func() uint8 {
		x := b[pos/2]
		if pos%2 == 1 {
			x >>= 4
		}
		pos++
		return x & 15
	}
	*s = State{}
	for i := 0; i < N; i++ {
		n := &s.Nodes[i]
		n.Term, n.Role, n.Len, n.Commit, n.Applied, n.CfgIdx, n.Pending, n.PCommit = get(), get(), get(), get(), get(), get(), get(), get()
		for k := 0; k < N; k++ {
			n.Match[k] = get()
		}
		for j := 0; j < int(n.Len); j++ {
			a, b2, c, d := get(), get(), get(), get()
			n.Log[j] = uint16(a)<<12 | uint16(b2)<<8 | uint16(c)<<4 | uint16(d)
		}
	}
	s.NC, s.NV = get(), get()
	lo, hi := get(), get()
	s.Won = lo | hi<<4
	s.RdNode, s.RdTerm, s.RdIdx, s.RdMax = get(), get(), get(), get()
	return slot, (pos + 1) / 2
}

type Found struct {
	parent State
	pslot  uint32
	action Action
	kind   int
	depth  int
	succ   State
}

func initState() State {
	var s State
	return s
}

func main() {
	flag.IntVar(&N, "n", 4, "nodes")
	flag.IntVar(&NInit, "init", 3, "initial voters 1..init")
	flag.StringVar(&Mode, "mode", "faithful", "faithful | lag | crash | fix")
	flag.IntVar(&MAXT, "maxt", 3, "max term")
	flag.IntVar(&MAXLOG, "maxlog", 5, "max log length")
	flag.IntVar(&MAXCONF, "maxconf", 2, "max conf changes proposed (auto-leave not counted)")
	flag.IntVar(&MAXVAL, "maxval", 2, "max values proposed")
	flag.BoolVar(&JOINT, "joint", false, "joint consensus (enter/leave) instead of simple changes")
	flag.BoolVar(&REDUCED, "reduced", false, "app sends at most one new entry (model.py's REDUCED)")
	flag.BoolVar(&GhostES, "es", true, "election safety ghost (bit per term won); off for model.py-compatible counts")
	flag.BoolVar(&ReadIdx, "read", false, "read-index requests (one pending at a time; ghost of the commit at arrival)")
	flag.BoolVar(&ReadNoTermCheck, "read-no-term-check", false, "validation: read index without the committed-entry-in-term check (a known bug; must be found)")
	flag.BoolVar(&ReadSingletonBug, "read-singleton-bug", false, "read index as the pinned raft: a single-voter leader skips the committed-entry-in-term check")
	flag.BoolVar(&RemSelf, "remself", false, "a leader may propose its own removal (model.py excludes it; with -joint also joint changes without it)")
	flag.BoolVar(&NoStepDown, "nostepdown", false, "StepDownOnRemoval off (raft's default): a removed leader stays leader; model.py always steps down")
	flag.BoolVar(&useSym, "sym", true, "symmetry reduction (permutations of the initial voters, of the addable nodes)")
	lagNodes := flag.String("lagnodes", "", "lagging modes: the nodes whose application may lag, e.g. 1 or 1,3 (default all)")
	inv := flag.String("inv", "sms,lm,es,lc,read", "invariants checked: sms (state machine safety), lm (log matching), es (election safety), lc (leader completeness), read (read index)")
	replay := flag.String("replay", "", "replay a model.py trace file instead of searching")
	maxDepth := flag.Int("maxdepth", 1000, "stop after this BFS depth")
	tableLog := flag.Uint("tablelog", 28, "visited table size 2^k slots (12 bytes each, 8 with -noparents)")
	flag.StringVar(&spillDir, "spill", "", "keep the BFS frontier in files under this directory instead of memory")
	flag.BoolVar(&noParents, "noparents", false, "do not record parents (no counterexample trace, only its last two states)")
	workers := flag.Int("workers", runtime.NumCPU()/2, "worker goroutines")
	keepGoing := flag.Bool("all", false, "report every violation kind found, keep searching to the end of the depth")
	flag.Parse()
	if N > MaxN || MAXLOG > MaxLog || MAXT > 7 {
		fmt.Fprintln(os.Stderr, "bounds exceed MaxN/MaxLog/term 7")
		os.Exit(2)
	}
	for i := 1; i <= NInit; i++ {
		INIT |= bit(i)
	}
	switch Mode {
	case "faithful", "crash":
	case "lag":
		lagging = true
	case "fix":
		lagging, guardCfg = true, true
	default:
		fmt.Fprintln(os.Stderr, "unknown mode")
		os.Exit(2)
	}
	LagMask = 1<<N - 1
	if *lagNodes != "" {
		LagMask = 0
		for _, f := range strings.Split(*lagNodes, ",") {
			var k int
			fmt.Sscan(f, &k)
			LagMask |= bit(k)
		}
	}
	for _, f := range strings.Split(*inv, ",") {
		k := map[string]int{"sms": VSMS, "lm": VLogMatch, "es": VElection, "lc": VLeaderCompl, "read": VRead}[f]
		if k == 0 {
			fmt.Fprintln(os.Stderr, "unknown invariant", f)
			os.Exit(2)
		}
		InvMask |= 1 << k
	}
	initPerms()
	fmt.Printf("params: n=%d init=%d mode=%s maxt=%d maxlog=%d maxconf=%d maxval=%d joint=%v reduced=%v es=%v read=%v sym=%v (%d perms) lagnodes=%s inv=%s workers=%d\n",
		N, NInit, Mode, MAXT, MAXLOG, MAXCONF, MAXVAL, JOINT, REDUCED, GhostES, ReadIdx, useSym, len(perms), tupleOfMask(LagMask), *inv, *workers)
	if *replay != "" {
		os.Exit(doReplay(*replay))
	}
	os.Exit(search(*maxDepth, *tableLog, *workers, *keepGoing))
}

func doReplay(path string) int {
	f, err := os.Open(path)
	if err != nil {
		fmt.Println(err)
		return 2
	}
	defer f.Close()
	s := initState()
	sc := bufio.NewScanner(f)
	step := 0
	for sc.Scan() {
		want := strings.TrimSpace(sc.Text())
		if want == "" {
			continue
		}
		step++
		var got *State
		gv := VNone
		succ(&s, func(a Action, ns *State, v int) {
			if got == nil && a.String() == want {
				c := *ns
				got, gv = &c, v
			}
		})
		if got == nil {
			fmt.Printf("action not enabled: %s\n", want)
			fmt.Print(s.Dump())
			return 2
		}
		s = *got
		st := checkState(&s)
		fmt.Printf("ok %2d %s %s", step, want, map[bool]string{true: "safe", false: "UNSAFE"}[st != VSMS])
		if gv != VNone {
			fmt.Printf(" [transition: %s violated]", vName[gv])
		}
		if st != VNone {
			fmt.Printf(" [state: %s violated]", vName[st])
		}
		fmt.Println()
	}
	fmt.Print(s.Dump())
	return 0
}

func search(maxDepth int, tableLog uint, workers int, keepGoing bool) int {
	start := time.Now()
	tab := newTable(tableLog)
	limit := int64(float64(uint64(1)<<tableLog) * 0.85)
	s0 := initState()
	b1, b2 := make([]byte, 0, 256), make([]byte, 0, 256)
	slot0, _ := tab.insert(fingerprint(&s0, b1, b2), noParent)
	frontier := &Level{mem: []*Chunk{{data: pack(nil, slot0, &s0), n: 1}}, n: 1}
	var found []Found
	var foundMu sync.Mutex
	var seenKinds [16]bool
	var stop atomic.Bool
	var transitions atomic.Int64
	depth := 0
	cum := int64(1)
	fmt.Printf("depth 0: 1 states\n")
	full := false
	for depth < maxDepth {
		if frontier.n == 0 {
			break
		}
		cur := frontier
		nextLv := &Level{}
		ws := make([]*levelWriter, workers)
		for w := range ws {
			ws[w] = newLevelWriter(nextLv, depth+1, w)
		}
		var wg sync.WaitGroup
		for w := 0; w < workers; w++ {
			wg.Add(1)
			go func(w int) {
				defer wg.Done()
				b1, b2 := make([]byte, 0, 256), make([]byte, 0, 256)
				out := ws[w]
				var ntr int64
				var es State
				for !stop.Load() {
					ch := cur.next()
					if ch == nil {
						break
					}
					data := ch.data
					for off := 0; off < len(data); {
						var eslot uint32
						eslot, off = unpack(data, off, &es)
						succ(&es, func(a Action, ns *State, tv int) {
							ntr++
							if tv == VNone {
								tv = checkState(ns)
							}
							if tv != VNone {
								foundMu.Lock()
								if !seenKinds[tv] {
									seenKinds[tv] = true
									found = append(found, Found{parent: es, pslot: eslot, action: a, kind: tv, depth: depth + 1, succ: *ns})
								}
								foundMu.Unlock()
								if !keepGoing {
									stop.Store(true)
								}
								return // do not explore past a violation
							}
							slot, isNew := tab.insert(fingerprint(ns, b1, b2), eslot)
							if isNew {
								out.add(slot, ns)
								if tab.count.Load() > limit {
									stop.Store(true) // the table must never fill up: probing would not end
								}
							}
						})
					}
				}
				out.close()
				transitions.Add(ntr)
			}(w)
		}
		wg.Wait()
		cur.release()
		frontier = nextLv
		nnew := nextLv.n
		depth++
		cum += int64(nnew)
		var ms runtime.MemStats
		runtime.ReadMemStats(&ms)
		fmt.Printf("depth %d: %d new, %d total, %d transitions, %.1fs, heap %.1f GB\n",
			depth, nnew, cum, transitions.Load(), time.Since(start).Seconds(), float64(ms.HeapAlloc)/1e9)
		if len(found) > 0 && !keepGoing {
			break
		}
		if tab.count.Load() > limit {
			fmt.Printf("visited table 85%% full during depth %d: stopping; depths up to %d are complete (raise -tablelog)\n", depth, depth-1)
			full = true
			break
		}
		if nnew == 0 {
			break
		}
	}
	if len(found) == 0 {
		done := "exhaustive: no new states"
		if full || (depth >= maxDepth && frontier.n > 0) {
			done = "NOT exhaustive (bound on depth or table)"
		}
		fmt.Printf("no violation; %d distinct states (up to symmetry), %d transitions, depth %d, %.1fs; %s\n",
			cum, transitions.Load(), depth, time.Since(start).Seconds(), done)
		return 0
	}
	for _, f := range found {
		fmt.Printf("\nVIOLATION of %s at depth %d (after %.1fs, %d states)\n", vName[f.kind], f.depth, time.Since(start).Seconds(), cum)
		printTrace(tab, f)
	}
	return 1
}

// printTrace rebuilds a concrete trace from the parent slots: the canonical
// fingerprints along the chain, matched by re-running succ from the initial state.
func printTrace(tab *Table, f Found) {
	if tab.parents == nil {
		fmt.Println("(-noparents: no trace) last action:", f.action.String())
		fmt.Print("state before:\n", f.parent.Dump(), "state after:\n", f.succ.Dump())
		return
	}
	var chain []uint64
	for sl := f.pslot; sl != noParent; sl = tab.parents[sl] {
		chain = append(chain, tab.fps[sl])
	}
	// chain: parent ... initial; reverse
	for a, b := 0, len(chain)-1; a < b; a, b = a+1, b-1 {
		chain[a], chain[b] = chain[b], chain[a]
	}
	b1, b2 := make([]byte, 0, 256), make([]byte, 0, 256)
	s := initState()
	var acts []Action
	for k := 1; k < len(chain); k++ {
		var nxt *State
		succ(&s, func(a Action, ns *State, v int) {
			if nxt == nil && fingerprint(ns, b1, b2) == chain[k] {
				c := *ns
				nxt = &c
				acts = append(acts, a)
			}
		})
		if nxt == nil {
			fmt.Println("trace reconstruction failed at step", k)
			return
		}
		s = *nxt
	}
	// last step: from s (equivalent to f.parent up to symmetry), the violating action
	var last *Action
	var lastS State
	succ(&s, func(a Action, ns *State, v int) {
		if last != nil {
			return
		}
		if v == VNone {
			v = checkState(ns)
		}
		if v == f.kind {
			aa := a
			last, lastS = &aa, *ns
		}
	})
	if last == nil {
		fmt.Println("trace reconstruction: violating step not found")
		return
	}
	acts = append(acts, *last)
	fmt.Println("trace (model.py actions, replayable with -replay):")
	for _, a := range acts {
		fmt.Println(a.String())
	}
	if lagging && LagMask != 1<<N-1 {
		// model.py lets every node lag: a non-lagging node's apply is apply + applyconf there
		fmt.Println("the same trace for model.py (an applyconf after each apply of a non-lagging node):")
		for _, a := range acts {
			fmt.Println(a.String())
			if a.Kind == AApply && LagMask&bit(int(a.I)) == 0 {
				fmt.Println(Action{Kind: AApplyConf, I: a.I, X: a.X}.String())
			}
		}
	}
	fmt.Println("final state:")
	fmt.Print(lastS.Dump())
}
