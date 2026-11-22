package etcd3

// This directory is a copy of examples/k8s/etcd3's package (k8setcd3.go, watch.go and realcheck.go,
// byte for byte: TestVerbatim in examples/k8s/dist checks it), so that examples/k8s/dist can split
// the driver's Check between machines: its model, its seeds, its generator and the per-client cache
// are unexported there, and the driver itself must stay as k8s_safe's proof has it. This file is
// the only addition: what the distributed workload needs of the copy, each a thin wrapper of the
// driver's own functions (notes/k8s-dist.md, "Copies").

import (
	"context"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
)

// Seeded is the model's store after the seeds, with its history (seed's results).
type Seeded struct {
	st0 mstore
	h0  []mstore
}

// Model is the driver's Model from the seeded store.
func (s Seeded) Model() porcupine.Model {
	return Model(s.st0, s.h0)
}

// NewCache is Check's per-client cache (newWCache): clients unary clients of ops operations each,
// the rest watchers, the drawn resource versions floored at the seeded store's revision.
func (s Seeded) NewCache(clients int, ops int) *cache {
	return newWCache(clients, int64(clients)*int64(ops), s.st0.rv)
}

// RealCheck is the maintainers' checker (realCheck) on a failure-free history ordered by the
// driver's linearization.
func (s Seeded) RealCheck(ops []porcupine.Operation, timeout time.Duration) porcupine.CheckResult {
	return realCheck(s.st0, ops, timeout)
}

// FailureFree is failureFree.
func FailureFree(ops []porcupine.Operation) bool {
	return failureFree(ops)
}

// NewStoreOnly is newStore without the seeds (an API server's store, made on its own machine;
// the seeds are the orchestrator's): the features set (no streaming lists, WatchList on), then the
// store over kc with the driver's codec, versioner, decoder and transformer; false if a step
// failed.
func NewStoreOnly(kc *kubernetes.Client) (storage.Interface, bool) {
	if !noStreaming() || !watchList() {
		return nil, false
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return nil, false
	}
	return s, true
}

// Serve is Apply's half on the API server's machine: the operation in through the store s (a
// watch: runWatch's output; otherwise call's), without the prophecy and without the cache, which
// stay with the orchestrator (Record).
func Serve(s storage.Interface, in Input) Output {
	if in.Kind == KWatch {
		out, _, _ := runWatch(s, in)
		return out
	}
	return call(s, in)
}

// Record is Apply's other half, on the orchestrator: what Apply puts in the cache tbl for the
// operation in and its output out (a watch's last object that is not an error; a unary answer
// with a name; the unary operations' count). An output whose call got no answer (a unary EOther,
// a failed watch) records nothing but the count, as Apply's output of a failed call.
func Record(tbl *cache, in Input, out Output) {
	if in.Kind == KWatch {
		if out.WFailed {
			return
		}
		evs, ok := decodeWEvents(out.WEvents)
		if !ok {
			return
		}
		if last, ok := lastObj(evs); ok {
			tbl.putW(in.Client, last)
		}
		return
	}
	if out.Err == ENone && out.Name != "" {
		tbl.put(in.Client, objOf(out))
	}
	tbl.done.Add(1)
}

// IsWrite is isWrite.
func IsWrite(in Input) bool {
	return isWrite(in)
}

// Rejections are the callbacks' own errors (errDeleteRejected, errUpdateRejected), which a Raw's
// encoding names.
func Rejections() (error, error) {
	return errDeleteRejected, errUpdateRejected
}

// SetFeatures sets the features newStore sets (no streaming lists, WatchList on), or returns
// false: the orchestrator's process has the API servers' features, as the driver's one process.
func SetFeatures() bool {
	return noStreaming() && watchList()
}

// ---------------------------------------------------------------------------------------------
// One cluster shared with other writers (notes/k8s-dist.md, "One cluster")
//
// In the distributed test the store's cluster is also the compactor workload's: its writer and its
// compactors write keys outside the store's prefix (Prefix + ResourcePrefix), each write a revision
// of the one cluster. The driver's Model numbers the store's revisions itself (a write is at the
// store's revision plus one), so it cannot follow such a cluster. SharedModel is Model with foreign
// revisions: at any time the cluster's revision may advance by any amount with the store's items
// unchanged (every store at those revisions is the store before them, at its own revision). Every
// check of Model is kept: SharedModel runs Model's own step on each configuration, after the
// foreign revisions the operation needs. Only the revision numbers are let go.
//
// The foreign revisions cannot be enumerated, so the history drives them: before an operation, a
// configuration first lets pending writes take effect (Model's closure), each at the next revision
// or at one of the revisions the history names (Revs), then moves to the least revision the
// operation's answer needs (its target), then takes Model's step.

// Revs are the revisions a history names: anchors, every revision an input or output names
// (resource versions of objects, lists, errors, events and bookmarks, minimum resource versions,
// preconditions), sorted; and, per item key, the objects' resource versions the outputs show for it
// (where a failed write that took effect shows its revision).
type Revs struct {
	anchors []uint64
	byKey   map[string][]uint64
	// byKey without the revisions a successful Create, Delete or update not asked to be a no-op
	// answered with (each, but for an update that left the object as it was, a write of the
	// store's own): the earlier modes' landings
	fastByKey map[string][]uint64
}

// rvOfMsg is the resource version a failed precondition's message names (preMsg), or 0.
func rvOfMsg(msg string) uint64 {
	const p = "ResourceVersion in object meta: "
	i := strings.Index(msg, p)
	if i < 0 {
		return 0
	}
	r, err := parseRV(msg[i+len(p):])
	if err != nil {
		return 0
	}
	return r
}

// decodeItemRVs is a list's items (encodeItems) as key and resource version, or false.
func decodeItemRVs(s string) ([]item, bool) {
	var its []item
	i := 0
	for i < len(s) {
		if len(s)-i < 16 {
			return nil, false
		}
		rv, _ := parseRV(s[i : i+8])
		n, _ := parseRV(s[i+8 : i+16])
		i += 16
		if uint64(len(s)-i) < n {
			return nil, false
		}
		o, ok := decodeObj([]byte(s[i : i+int(n)]))
		if !ok {
			return nil, false
		}
		i += int(n)
		o.ResourceVersion = rv
		its = append(its, item{key: o.Namespace + "/" + o.Name, obj: o})
	}
	return its, true
}

// HistoryRevs collects the revisions the history ops names.
func HistoryRevs(ops []porcupine.Operation) Revs {
	all := map[uint64]bool{}
	byKey := map[string]map[uint64]bool{}
	written := map[uint64]bool{}
	obj := func(key string, rv uint64) {
		if rv == 0 {
			return
		}
		all[rv] = true
		if byKey[key] == nil {
			byKey[key] = map[uint64]bool{}
		}
		byKey[key][rv] = true
	}
	num := func(rv uint64) {
		if rv != 0 {
			all[rv] = true
		}
	}
	for _, op := range ops {
		in := op.Input.(Input)
		out := op.Output.(Output)
		if r, err := parseRV(in.MinRV); err == nil {
			num(r)
		}
		if r, err := parseRV(in.PreRV); in.HasPreRV && err == nil {
			num(r)
		}
		if in.UseCached {
			obj(in.Key, in.Cached.ResourceVersion)
		}
		if in.Kind == KWatch {
			if evs, ok := decodeWEvents(out.WEvents); ok && !out.WFailed {
				for _, ev := range evs {
					if ev.Type == WBookmark {
						num(ev.Obj.ResourceVersion)
					} else if ev.Type < WError {
						obj(ev.Obj.Namespace+"/"+ev.Obj.Name, ev.Obj.ResourceVersion)
					}
				}
			}
			continue
		}
		num(uint64(out.ErrRV))
		num(out.ListRV)
		if r := rvOfMsg(out.ErrMsg); r != 0 {
			obj(in.Key, r)
		}
		if out.Err == ENone && out.Name != "" {
			obj(out.Namespace+"/"+out.Name, out.RV)
			if in.Kind == KCreate || in.Kind == KDelete || (in.Kind == KUpdate && !in.NoOp) {
				written[out.RV] = true
			}
		}
		if in.Kind == KList && out.Err == ENone {
			if its, ok := decodeItemRVs(out.Items); ok {
				for _, it := range its {
					obj(it.key, it.obj.ResourceVersion)
				}
			}
		}
	}
	var r Revs
	for v := range all {
		r.anchors = append(r.anchors, v)
	}
	sort.Slice(r.anchors, func(i, j int) bool { return r.anchors[i] < r.anchors[j] })
	r.byKey = map[string][]uint64{}
	r.fastByKey = map[string][]uint64{}
	for k, m := range byKey {
		for v := range m {
			r.byKey[k] = append(r.byKey[k], v)
			if !written[v] {
				r.fastByKey[k] = append(r.fastByKey[k], v)
			}
		}
		sort.Slice(r.byKey[k], func(i, j int) bool { return r.byKey[k][i] < r.byKey[k][j] })
		sort.Slice(r.fastByKey[k], func(i, j int) bool { return r.fastByKey[k][i] < r.fastByKey[k][j] })
	}
	return r
}

// skipTo is c at the revision t (foreign revisions: the store's items unchanged, a store per
// revision appended to the history), or c if it is at t or beyond. The stores appended to a
// history node are built once and shared (gaps), so that histories that skip alike are one.
func (hh *histHashes) skipTo(c mcfg, t uint64) mcfg {
	if t <= c.st.rv || c.hist == nil {
		return c
	}
	hh.mu.Lock()
	base := hh.canonLocked(c.hist)
	if hh.gaps == nil {
		hh.gaps = map[*hnode][]*hnode{}
	}
	g := hh.gaps[base]
	for uint64(len(g)) < t-c.st.rv {
		h := base
		if len(g) > 0 {
			h = g[len(g)-1]
		}
		g = append(g, hh.intern(h, mstore{items: c.st.items, rv: histLen(h) + 1}, histLen(h)+1))
	}
	hh.gaps[base] = g
	n := g[t-c.st.rv-1]
	hh.mu.Unlock()
	return mcfg{st: n.st, pend: c.pend, hist: n}
}

// target is the least revision a configuration at rv must be at for the operation in to answer
// out (0: none): a write's new revision less one, the current revision a "not found" or a current
// List names, the revision a past List reads, a Get's minimum resource version, the greatest
// revision a watch's events name. A write that answers with a revision at most rv is a no-op
// update (the stored object) and needs none.
func target(in Input, out Output, rv uint64) uint64 {
	if in.Kind == KWatch {
		if out.WFailed || in.Skip {
			return 0
		}
		evs, ok := decodeWEvents(out.WEvents)
		if !ok {
			return 0
		}
		var t uint64
		for _, ev := range evs {
			if ev.Type < WError {
				t = max(t, ev.Obj.ResourceVersion)
			}
		}
		return t
	}
	if out.Err == ENotFound {
		return uint64(out.ErrRV)
	}
	if out.Err != ENone {
		return 0
	}
	req, err := parseRV(in.MinRV)
	if err != nil {
		return 0
	}
	switch in.Kind {
	case KList:
		if pastRead(in, req) {
			return req
		}
		return out.ListRV
	case KGet:
		return req
	}
	if out.RV > rv {
		return out.RV - 1
	}
	return 0
}

// bound is the greatest revision a configuration may be at, after its pending writes took effect
// and before the operation in answers out, as far as the answer says (0: it does not say): a
// write's answer's revision, the current revision a "not found" or a current List names, one less
// than a too-large resource version.
func bound(in Input, out Output) uint64 {
	if in.Kind == KWatch {
		return 0
	}
	req, _ := parseRV(in.MinRV)
	switch out.Err {
	case ENotFound:
		return uint64(out.ErrRV)
	case ETooLarge:
		if req > 0 {
			return req - 1
		}
	case ENone:
		if isWrite(in) {
			return out.RV
		}
		if in.Kind == KList && !pastRead(in, req) {
			return out.ListRV
		}
	}
	return 0
}

// landings are the revisions a pending write w may take effect at on c, before the operation in
// answers out: the next one, and (each above it) the revisions the history shows objects of w's
// key at (without full, but those a successful write answered with, fastByKey), each at most the bound b
// if b > 0 or where the answer needs w at that revision (shows), and the answer's own revision
// for w's key; with full, those and every anchor and the one after it, whatever the bound.
func landings(revs Revs, c mcfg, w Input, b uint64, full bool, in Input, out Output) []uint64 {
	next := c.st.rv + 1
	ls := []uint64{next}
	add := func(r uint64) {
		if r > next && (full || (b > 0 && r <= b) || shows(in, out, w.Key, r)) {
			ls = append(ls, r)
		}
	}
	byKey := revs.fastByKey
	if full {
		byKey = revs.byKey
	}
	for _, r := range byKey[w.Key] {
		add(r)
	}
	// the answer's own revision for w's key, which byKey may leave out (a no-op update answers
	// with the stored object, its revision perhaps a pending write's)
	if in.Key == w.Key && out.Err == ENone && in.Kind != KList && in.Kind != KWatch {
		add(out.RV)
	}
	if full {
		i := sort.Search(len(revs.anchors), func(i int) bool { return revs.anchors[i] >= c.st.rv })
		for ; i < len(revs.anchors); i++ {
			add(revs.anchors[i])
			add(revs.anchors[i] + 1)
		}
	}
	return ls
}

// shows says whether the answer out to in needs a write of the key key at the revision r to have
// taken effect: it shows key's object at r (a Get's, a List's item, a watch event's), or it is a
// write's refusal on key (exists, rejected, a failed precondition), which shows an object there
// and not its revision.
func shows(in Input, out Output, key string, r uint64) bool {
	if in.Kind == KWatch {
		evs, ok := decodeWEvents(out.WEvents)
		if !ok || out.WFailed {
			return false
		}
		for _, ev := range evs {
			if ev.Type < WBookmark && ev.Obj.Namespace+"/"+ev.Obj.Name == key && ev.Obj.ResourceVersion == r {
				return true
			}
		}
		return false
	}
	if in.Kind == KList {
		its, ok := decodeItemRVs(out.Items)
		if !ok || out.Err != ENone {
			return false
		}
		for _, it := range its {
			if it.key == key && it.obj.ResourceVersion == r {
				return true
			}
		}
		return false
	}
	if in.Key != key {
		return false
	}
	switch out.Err {
	case ENone:
		return out.RV == r
	case EExists, ERejected, EInvalid:
		return true
	}
	return false
}

// histHashes keeps the histories' nodes hash-consed (canon: one node per history, by its
// previous node and its store), so that equal histories are one pointer (histEqual walks two
// histories back to a node they share, which nodes built apart, by foreign revisions or by
// pending writes taking effect in different orders, make long), and the foreign revisions
// appended to each node (gaps, skipTo).
type histHashes struct {
	mu    sync.Mutex
	canon map[ikey][]*hnode
	is    map[*hnode]bool
	gaps  map[*hnode][]*hnode
}

type ikey struct {
	prev *hnode
	n    uint64
	h    uint64
}

// intern is the canonical node of the store st after the canonical history prev (hh.mu held).
func (hh *histHashes) intern(prev *hnode, st mstore, n uint64) *hnode {
	if hh.canon == nil {
		hh.canon = map[ikey][]*hnode{}
		hh.is = map[*hnode]bool{}
	}
	k := ikey{prev: prev, n: n, h: storeHash(st)}
	for _, c := range hh.canon[k] {
		if storeEqual(c.st, st) {
			return c
		}
	}
	c := &hnode{st: st, n: n, prev: prev}
	hh.canon[k] = append(hh.canon[k], c)
	hh.is[c] = true
	return c
}

// canonical is h's canonical node.
func (hh *histHashes) canonical(h *hnode) *hnode {
	hh.mu.Lock()
	defer hh.mu.Unlock()
	return hh.canonLocked(h)
}

func (hh *histHashes) canonLocked(h *hnode) *hnode {
	var todo []*hnode
	n := h
	for n != nil && !hh.is[n] {
		todo = append(todo, n)
		n = n.prev
	}
	for i := len(todo) - 1; i >= 0; i-- {
		n = hh.intern(n, todo[i].st, todo[i].n)
	}
	return n
}

func mix(h, v uint64) uint64 {
	h ^= v
	h *= 1099511628211
	return h
}

func strHash(h uint64, s string) uint64 {
	h = mix(h, uint64(len(s)))
	for i := 0; i < len(s); i++ {
		h = mix(h, uint64(s[i]))
	}
	return h
}

// storeHash is a hash of a store (its revision and items).
func storeHash(st mstore) uint64 {
	h := mix(14695981039346656037, st.rv)
	for _, it := range st.items {
		h = strHash(h, it.key)
		o := it.obj
		for _, f := range []string{o.Namespace, o.Name, o.UID, o.Value, o.Node, o.App} {
			h = strHash(h, f)
		}
		h = mix(h, o.ResourceVersion)
		if o.Annotated {
			h = mix(h, 1)
		}
		if it.canon {
			h = mix(h, 2)
		}
	}
	return h
}

// cfgSet is a set of configurations, their histories canonical (hh), so that two are equal iff
// their stores and pending writes are and their histories are one node (configEqual's test).
type cfgSet struct {
	hh      *histHashes
	list    []mcfg
	buckets map[ckey][]int
}

type ckey struct {
	hist *hnode
	rv   uint64
	np   int
	h    uint64
}

func (s *cfgSet) add(c mcfg) bool {
	if s.buckets == nil {
		s.buckets = map[ckey][]int{}
	}
	c.hist = s.hh.canonical(c.hist)
	k := ckey{hist: c.hist, rv: c.st.rv, np: len(c.pend), h: storeHash(c.st)}
	for _, i := range s.buckets[k] {
		d := s.list[i]
		if storeEqual(d.st, c.st) && pendEqual(d.pend, c.pend) {
			return false
		}
	}
	s.buckets[k] = append(s.buckets[k], len(s.list))
	s.list = append(s.list, c)
	return true
}

func pendEqual(a, b []Input) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if !inputEqual(a[i], b[i]) {
			return false
		}
	}
	return true
}

// settle is every configuration c reaches by its pending writes taking effect, in any order, each
// at one of its landings (Model's closure, with the revision chosen).
func settle(hh *histHashes, revs Revs, c mcfg, b uint64, full bool, in Input, out Output) []mcfg {
	set := cfgSet{hh: hh}
	work := []mcfg{c}
	for len(work) > 0 {
		d := work[len(work)-1]
		work = work[:len(work)-1]
		if !set.add(d) {
			continue
		}
		for i, w := range d.pend {
			rest := removeAt(d.pend, i)
			st, _ := mstep(w, d.st)
			if st.rv == d.st.rv {
				// no effect: the write fails on this store at any revision
				work = append(work, mcfg{st: d.st, pend: rest, hist: d.hist})
				continue
			}
			for _, l := range landings(revs, d, w, b, full, in, out) {
				e := hh.skipTo(d, l-1)
				st, _ := mstep(w, e.st)
				work = append(work, advance(e, st, rest))
			}
		}
	}
	return set.list
}

// The modes of SharedModel, each complete where the one before is not, and slower.
const (
	// pending writes take effect only before an operation the configuration does not answer
	// without
	Lazy = 0
	// before any operation, at the revisions landings allows without full
	Eager = 1
	// at every revision landings allows with full
	Full = 2
)

// SharedModel is Model from the seeded store, with foreign revisions (above), the history's
// revisions revs (HistoryRevs), in the mode mode. Lazy: a configuration's pending writes take
// effect only before an operation it does not answer without them. Eager (and Lazy then): before
// any operation, each at the next revision or at one its key's objects show and no successful
// write answered with, up to the bound the operation's answer sets (bound), or where the answer
// shows it (shows). Full: also at every anchor and the one after it. Each mode is complete where
// the one before is not; CheckShared (examples/k8s/dist) runs them in turn on Illegal, and only
// Full's Illegal is a verdict.
func (s Seeded) SharedModel(revs Revs, mode int) porcupine.Model {
	full := mode == Full
	hh := &histHashes{}
	memo := map[wkey]bool{}
	return porcupine.Model{
		Init: func() any { return state{mcfg{st: s.st0, hist: hh.canonical(histOf(s.h0))}} },
		Step: func(st, input, output any) (bool, any) {
			in := input.(Input)
			out := output.(Output)
			b := bound(in, out)
			next := cfgSet{hh: hh}
			for _, c := range st.(state) {
				if mode == Lazy {
					d := hh.skipTo(c, target(in, out, c.st.rv))
					if es := stepIdx(memo, d, in, out); len(es) > 0 {
						for _, e := range es {
							next.add(e)
						}
						continue
					}
				}
				for _, d := range settle(hh, revs, c, b, full, in, out) {
					d = hh.skipTo(d, target(in, out, d.st.rv))
					for _, e := range stepIdx(memo, d, in, out) {
						next.add(e)
					}
				}
			}
			return len(next.list) > 0, state(next.list)
		},
		Equal: func(a, b any) bool {
			// the histories are canonical: equal iff one node
			sa := a.(state)
			sb := b.(state)
			if len(sa) != len(sb) {
				return false
			}
			for i := range sa {
				if sa[i].hist != sb[i].hist || !storeEqual(sa[i].st, sb[i].st) || !pendEqual(sa[i].pend, sb[i].pend) {
					return false
				}
			}
			return true
		},
	}
}

// SeedShared is Seed on a cluster that others write too: the same two Puts of the seed keys
// through cli, at whatever revisions they get; the history has the empty store up to the first,
// then each seed's store up to the next revision it reaches. False if a Put failed.
func SeedShared(cli *clientv3.Client) (Seeded, bool) {
	st := mstore{rv: 1}
	h := []mstore{st}
	for _, k := range []string{"ns-1/pod-1", "ns-2/pod-2"} {
		ns, name := splitKey(k)
		o := Obj{Namespace: ns, Name: name, Value: "x"}
		resp, err := cli.Put(context.Background(), Prefix+storeKey(k), string(encodeV0(o)))
		if err != nil || uint64(resp.Header.Revision) <= st.rv {
			return Seeded{}, false
		}
		rv := uint64(resp.Header.Revision)
		for r := st.rv + 1; r < rv; r++ {
			h = append(h, mstore{items: st.items, rv: r})
		}
		o.ResourceVersion = rv
		st = mstore{items: setItem(st.items, item{key: k, obj: o, canon: false}), rv: rv}
		h = append(h, st)
	}
	return Seeded{st0: st, h0: h}, true
}

// Floor is the seeded store's revision (the resource versions drawn are floored at it).
func (s Seeded) Floor() uint64 {
	return s.st0.rv
}

// NoForeign says whether the failure-free history ops (as RunLin2 returns it) shows no foreign
// revision above the seeds, so that a history without any explains it and Kubernetes' checker,
// whose model numbers the revisions itself as Model does, applies: the revisions its successful
// writes answer with above the seeded store's are exactly the next ones, from it up to the greatest
// M, and no revision any input or output names is above M.
func (s Seeded) NoForeign(ops []porcupine.Operation) bool {
	writes := map[uint64]bool{}
	m := s.st0.rv
	for _, op := range ops {
		in := op.Input.(Input)
		out := op.Output.(Output)
		if isWrite(in) && out.Err == ENone && out.RV > s.st0.rv {
			writes[out.RV] = true
			m = max(m, out.RV)
		}
	}
	if uint64(len(writes)) != m-s.st0.rv {
		return false
	}
	revs := HistoryRevs(ops)
	return len(revs.anchors) == 0 || revs.anchors[len(revs.anchors)-1] <= m
}

// AcceptAll is a model that accepts every history: RunLin2 with it only runs the clients and
// returns their history, which the caller checks.
func AcceptAll() porcupine.Model {
	return porcupine.Model{
		Init:  func() any { return 0 },
		Step:  func(st, input, output any) (bool, any) { return true, 0 },
		Equal: func(a, b any) bool { return true },
	}
}

// PastRead says whether in reads at an explicit old revision: a List that reads at its resource
// version (pastRead: Exact, or the legacy match recursive with a limit), or a watch from a resource
// version above 0.
func PastRead(in Input) bool {
	r, err := parseRV(in.MinRV)
	if err != nil {
		return false
	}
	if in.Kind == KList {
		return pastRead(in, r)
	}
	return in.Kind == KWatch && r > 0
}

// PinnedRead says whether in reads at a revision the store fixed at an earlier read of its own
// (Kubernetes' etcd3 store): a paged List (a limit: its later pages at its first page's revision,
// pagedChunks), or any watch (its start revision is the requested one, its list's for a
// watch-list, the current revision the store read for one from the most recent,
// getStartWatchResourceVersion; and the etcd client resumes a broken watch stream from the last
// revision it received).
func PinnedRead(in Input) bool {
	return (in.Kind == KList && in.Limit > 0) || in.Kind == KWatch
}

// SeededAt is the seeded store SeedShared makes when its Puts get the revisions r1 < r2 (the
// driver's seed: 2 and 3), without a cluster: for the tests and for rechecking a dumped history.
func SeededAt(r1, r2 uint64) Seeded {
	st := mstore{rv: 1}
	h := []mstore{st}
	for i, k := range []string{"ns-1/pod-1", "ns-2/pod-2"} {
		rv := []uint64{r1, r2}[i]
		for r := st.rv + 1; r < rv; r++ {
			h = append(h, mstore{items: st.items, rv: r})
		}
		ns, name := splitKey(k)
		o := Obj{Namespace: ns, Name: name, Value: "x", ResourceVersion: rv}
		st = mstore{items: setItem(st.items, item{key: k, obj: o, canon: false}), rv: rv}
		h = append(h, st)
	}
	return Seeded{st0: st, h0: h}
}

// SeedRevs are the seeds' revisions.
func (s Seeded) SeedRevs() (uint64, uint64) {
	it1, _ := lookup(s.st0.items, "ns-1/pod-1")
	it2, _ := lookup(s.st0.items, "ns-2/pod-2")
	return it1.obj.ResourceVersion, it2.obj.ResourceVersion
}

// EncodeItems is encodeItems (a List output's items), and RVBytes rvBytes (a resource version's
// string): for the tests of SharedModel.
func EncodeItems(items []Obj) string { return encodeItems(items) }
func RVBytes(n uint64) string        { return rvBytes(n) }

// ---------------------------------------------------------------------------------------------
// The watch check over an indexed history
//
// watchOk reads the history through histAt, a walk back from the configuration's revision: its
// window of revisions (wantEvents, initialPrefixOk) costs the square of its length in walks. On the
// shared cluster a watch's window spans the compactor's writes too, thousands of revisions, and
// the check timed out. watchOkIdx is watchOk line for line (watchListOk, initialPrefixOk,
// reliableOk, wantEvents likewise), every other function the copy's own, with histAt answered from
// one walk (hview); TestReplayHistory checks the two agree on every watch step of a history
// (CrossCheckWatches).

// An hview is the stores of a history at the revisions lo to its own, by revision.
type hview struct {
	h   *hnode
	lo  uint64
	sts []mstore
}

// viewFrom is h's view from the revision lo (at least 1).
func viewFrom(h *hnode, lo uint64) hview {
	lo = max(lo, 1)
	v := hview{h: h, lo: lo}
	n := histLen(h)
	if n < lo {
		return v
	}
	v.sts = make([]mstore, n-lo+1)
	for x := h; x != nil && x.n >= lo; x = x.prev {
		v.sts[x.n-lo] = x.st
	}
	return v
}

// at is histAt(v.h, r): the store at r from the view when r is in it (every revision has its node:
// histOf, advance and skipTo append one per revision), histAt otherwise.
func (v hview) at(r uint64) mstore {
	if r >= v.lo && r-v.lo < uint64(len(v.sts)) {
		return v.sts[r-v.lo]
	}
	return histAt(v.h, r)
}

// watchOkIdx is watchOk.
func watchOkIdx(in Input, out Output, c mcfg) bool {
	if out.WFailed || in.Skip {
		return true
	}
	all, ok := decodeWEvents(out.WEvents)
	if !ok {
		return false
	}
	evs, ok := checkedEvents(all, c.st.rv)
	if !ok {
		return false
	}
	if !bookmarksOk(evs) {
		return false
	}
	req, err := parseRV(in.MinRV)
	if err != nil {
		return false
	}
	if in.SendInit == 2 {
		return watchListOkIdx(in, req, evs, c)
	}
	return reliableOkIdx(in, req, evs, c)
}

// watchListOkIdx is watchListOk.
func watchListOkIdx(in Input, req uint64, evs []WEvent, c mcfg) bool {
	b := firstBookmark(evs)
	if b < 0 {
		return initialPrefixOkIdx(in, req, evs, c)
	}
	if !evs[b].Obj.Annotated {
		return false
	}
	brv := evs[b].Obj.ResourceVersion
	if (req != 0 && brv < req) || brv < 1 || brv > c.st.rv {
		return false
	}
	if !eventsEqual(initialEvents(in, histAt(c.hist, brv)), evs[:b]) {
		return false
	}
	return reliableOkIdx(in, req, evs[b:], c)
}

// initialPrefixOkIdx is initialPrefixOk.
func initialPrefixOkIdx(in Input, req uint64, evs []WEvent, c mcfg) bool {
	if len(evs) == 0 {
		return true
	}
	lo := req
	if lo < 1 {
		lo = 1
	}
	v := viewFrom(c.hist, lo)
	for r := lo; r <= c.st.rv; r++ {
		init := initialEvents(in, v.at(r))
		if len(evs) <= len(init) && eventsEqual(init[:len(evs)], evs) {
			return true
		}
	}
	return false
}

// reliableOkIdx is reliableOk.
func reliableOkIdx(in Input, req uint64, evs []WEvent, c mcfg) bool {
	if len(evs) == 0 {
		return true
	}
	lo, hi := evRange(evs)
	lo = reliableLo(in, req, lo)
	if in.Match == MExact && req == 0 {
		return false
	}
	if hi > c.st.rv+1 {
		return false
	}
	return eventsEqual(wantEventsIdx(in, lo, hi, c), nonBookmarks(evs))
}

// wantEventsIdx is wantEvents.
func wantEventsIdx(in Input, lo uint64, hi uint64, c mcfg) []WEvent {
	var want []WEvent
	v := viewFrom(c.hist, max(lo, 2)-1)
	for r := max(lo, 2); r < hi; r++ {
		ch, ok := changeAt(v.at(r-1), v.at(r), r)
		if !ok || !keyInScope(in.WKey, in.Recursive, storeKey(ch.key)) {
			continue
		}
		if ev, ok := toEvent(in, ch); ok {
			want = append(want, ev)
		}
	}
	return want
}

// crossCheck makes the shared model compute every watch step both ways and panic if they differ.
var crossCheck bool

// CrossCheckWatches turns the cross-check of watchOkIdx against watchOk on or off (the tests).
func CrossCheckWatches(on bool) { crossCheck = on }

// A wkey is a watch step: the configuration's (canonical) history and the watch with its events.
type wkey struct {
	hist *hnode
	in   Input
	evs  string
	fail bool
}

// stepIdx is step, with a watch checked by watchOkIdx, its verdict kept in memo per history (a
// watch's verdict is a function of the history: porcupine tries a watch at many points, and again
// after it backtracks).
func stepIdx(memo map[wkey]bool, c mcfg, in Input, out Output) []mcfg {
	if in.Kind != KWatch {
		return step(c, in, out)
	}
	k := wkey{hist: c.hist, in: in, evs: out.WEvents, fail: out.WFailed}
	ok, seen := memo[k]
	if !seen {
		ok = watchOkIdx(in, out, c)
		if crossCheck && ok != watchOk(in, out, c) {
			panic("storecopy: watchOkIdx and watchOk differ")
		}
		memo[k] = ok
	}
	if !ok {
		return nil
	}
	return []mcfg{c}
}
