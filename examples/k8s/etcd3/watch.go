package etcd3

// Stage 7f-0/7f-6 (notes/k8s-7f-scope.md, notes/k8s-7f6-scope.md): TestCorrectness's watch traffic (RunWatchTraffic,
// runWatch) and its watch validator (correctness.WatchValidator) in the driver. A watch is one
// lintest operation of a watcher client (lintest.RunLin2's second group): Apply runs it to its end
// and returns the events it received (encoded as a plain value, encodeWEvents, as Output.Items
// is); the model checks them, at the watch's linearization point
// (its end), against the configuration's history (mcfg.hist, 7e), as the validator checks them
// against the replay. So the check is porcupine's: it holds for some linearization and some
// configuration, which the real run's are (no replay along porcupine's linearization, whose
// histories a failed write that took effect may not be in: notes/k8s-7d-scope.md §2).

import (
	"context"
	"time"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	"github.com/goose-lang/primitive"
)

// The behaviours of a watcher (Input.Behavior; the test's WatcherBehavior).
const (
	BFast    = 0
	BSlow    = 1
	BHiccup  = 2
	BStalled = 3
)

// The test's WatchConfig.
const (
	watchDuration  = 500 * time.Millisecond
	slowDelay      = 2 * time.Millisecond
	hiccupDuration = 150 * time.Millisecond
	maxEvents      = 200
)

// The types of a watch event (WEvent.Type: watch.Added, Modified, Deleted, Bookmark, Error).
const (
	WAdded    = 0
	WModified = 1
	WDeleted  = 2
	WBookmark = 3
	WError    = 4
	// an event the check rejects: an Added, Modified, Deleted or Bookmark event whose object is
	// not the driver's, or an Error event whose object is not a metav1.Status with status Failure
	WBad = 5
)

// A WEvent is a watch event as the driver records it: its type and its object (none for an
// error or a bad event).
type WEvent struct {
	Type int
	Obj  Obj
}

// genWatch is the watch watcher id picks for the random number n with its cached object c (if
// hasC): the test's randomWatchRequest. SendInitialEvents (30%; then no future resource
// version); a resource version (empty, 0, 1, the cached object's, and relative to it: current,
// past, future; 1/7 each; relative to the cached object, not the store's current one, as the
// driver's Gets'); a key (existing 80, in a namespace with no object 10, a missing object 10); a
// scope (cluster 40, namespace 30, object 30) and Recursive drawn again (70); the selectors as a
// List's; AllowWatchBookmarks (50%); a behaviour (fast 40, slow 20, hiccup 25, stalled 15).
func genWatch(id int, c Obj, hasC bool, floor uint64) Input {
	return genWatchFrom(primitive.RandomUint64(), id, c, hasC, floor)
}

// genWatchFrom is genWatch for the random number n. With no cached object the RV is drawn among
// the three that need none (empty, 0, 1), where the test skips the request and draws again. A
// non-zero resource version below floor is raised to it (floored, k8s 7g).
func genWatchFrom(n uint64, id int, c Obj, hasC bool, floor uint64) Input {
	wl, n := pick(n, 10)
	m, n := pick(n, 7)
	m2, n := pick(n, 6)
	m3, n := pick(n, 3)
	d, n := pick(n, 200)
	kt, n := pick(n, 10)
	ki, n := pick(n, 4)
	sc, n := pick(n, 10)
	rc, n := pick(n, 10)
	fs, n := pick(n, 100)
	ls, n := pick(n, 100)
	ni, n := pick(n, 2)
	ai, n := pick(n, 2)
	bm, n := pick(n, 2)
	bh, _ := pick(n, 100)
	watchList := wl < 3
	if watchList && m == 6 {
		m = m2
	}
	// The proof's bound (runWatch's resource version below 2^63 - 1, which the store's Watch
	// needs; the watchers' cached objects carry no fact): a cached object at 2^62 or above counts
	// as none, as minRV's clamp, so every drawn RV parses below 2^62 + 201. Unreachable in a real
	// run, whose resource versions stay far below 2^62.
	if hasC && c.ResourceVersion >= 1<<62 {
		hasC = false
	}
	if !hasC && m >= 3 {
		m = m3
	}
	rv := ""
	switch {
	case m == 1:
		rv = rvBytes(0)
	case m == 2:
		rv = rvBytes(floored(1, floor))
	case m >= 3:
		r := c.ResourceVersion
		if m == 5 {
			if r <= d+1 {
				r = 1
			} else {
				r = r - d - 1
			}
		} else if m == 6 {
			r = r + d + 1
		}
		rv = rvString(floored(r, floor))
	}
	key := workloadKeys()[ki]
	ns, name := splitKey(key)
	if kt == 8 {
		ns = "ns-nonexistent"
	} else if kt == 9 {
		name = "pod-nonexistent"
	}
	in := Input{Kind: KWatch, Client: id, MinRV: rv, SelNS: ns, SelName: name,
		SelNode: workloadNodes()[1+ni]}
	if sc < 4 {
		in.WKey = ResourcePrefix + "/"
	} else if sc < 7 {
		in.WKey = ResourcePrefix + "/" + ns
	} else {
		in.WKey = storeKey(ns + "/" + name)
	}
	in.Recursive = rc < 7
	if fs < 25 {
		in.Field = FEverything
	} else if fs < 40 {
		in.Field = FByName
	} else if fs < 55 {
		in.Field = FByNS
	} else if fs < 75 {
		in.Field = FByNode
	} else if fs < 90 {
		in.Field = FEmptyNode
	} else {
		in.Field = FCombined
	}
	if ls >= 60 {
		in.SelApp = workloadApps()[1+ai]
	}
	in.Bookmarks = bm == 0
	r, _ := parseRV(rv)
	if watchList {
		in.SendInit = 2
		in.Bookmarks = true
		in.Match = MNotOlderThan
	} else if r == 0 {
		in.SendInit = 1
		in.Match = MNotOlderThan
	}
	if bh < 40 {
		in.Behavior = BFast
	} else if bh < 60 {
		in.Behavior = BSlow
	} else if bh < 85 {
		in.Behavior = BHiccup
	} else {
		in.Behavior = BStalled
	}
	return in
}

// watchOptions is a watch's storage.ListOptions.
func watchOptions(in Input) storage.ListOptions {
	pred := predicate(in)
	pred.AllowWatchBookmarks = in.Bookmarks
	opts := storage.ListOptions{ResourceVersion: in.MinRV, ResourceVersionMatch: matchOpt(in),
		Predicate: pred, Recursive: in.Recursive}
	if in.SendInit == 1 {
		f := false
		opts.SendInitialEvents = &f
	} else if in.SendInit == 2 {
		t := true
		opts.SendInitialEvents = &t
	}
	return opts
}

// toWEvent is a received event as the driver records it: an Added, Modified, Deleted or Bookmark
// event with the driver's object, an Error event with a metav1.Status of status Failure (what
// the validator's validateMaybeLastEventError asks), or a bad event.
func toWEvent(ev watch.Event) WEvent {
	switch ev.Type {
	case watch.Added, watch.Modified, watch.Deleted, watch.Bookmark:
		o, ok := ev.Object.(*Obj)
		if !ok {
			return WEvent{Type: WBad}
		}
		t := WAdded
		if ev.Type == watch.Modified {
			t = WModified
		} else if ev.Type == watch.Deleted {
			t = WDeleted
		} else if ev.Type == watch.Bookmark {
			t = WBookmark
		}
		return WEvent{Type: t, Obj: *o}
	case watch.Error:
		st, ok := ev.Object.(*metav1.Status)
		if ok && st.Status == metav1.StatusFailure {
			return WEvent{Type: WError}
		}
	}
	return WEvent{Type: WBad}
}

// encodeWEvents is a watch's events as a plain value (Output.WEvents, which porcupine's model
// decodes purely; as encodeItems): for each, its type and annotation (a byte each), its object's
// resource version (rvBytes), the length of its object's encoding (rvBytes) and that encoding
// (encodeObj).
func encodeWEvents(evs []WEvent) string {
	var out []byte
	for i := range evs {
		e := encodeObj(&evs[i].Obj)
		a := byte(0)
		if evs[i].Obj.Annotated {
			a = 1
		}
		out = append(out, byte(evs[i].Type), a)
		out = append(out, []byte(rvBytes(evs[i].Obj.ResourceVersion))...)
		out = append(out, []byte(rvBytes(uint64(len(e))))...)
		out = append(out, e...)
	}
	return string(out)
}

// decodeWEvents inverts encodeWEvents, or false.
func decodeWEvents(s string) ([]WEvent, bool) {
	var evs []WEvent
	i := 0
	for i < len(s) {
		if len(s)-i < 18 {
			return nil, false
		}
		t, a := int(s[i]), s[i+1]
		rv, _ := parseRV(s[i+2 : i+10])
		n, _ := parseRV(s[i+10 : i+18])
		i += 18
		if uint64(len(s)-i) < n {
			return nil, false
		}
		o, ok := decodeObj([]byte(s[i : i+int(n)]))
		if !ok {
			return nil, false
		}
		i += int(n)
		o.ResourceVersion = rv
		o.Annotated = a == 1
		evs = append(evs, WEvent{Type: t, Obj: o})
	}
	return evs, true
}

// runWatch runs the watch in through the store s and returns its output (the events it received,
// encoded) and the object of its last event that is not an error, if any (the watcher's next
// cached object: the test's lastNonErrorEvent). It is the test's runWatch, but for two
// departures. A Watch call that fails is a failed watch (WFailed: the client's error, in a
// partition; the test panics on an error that is not a StorageError). Events after a watch.Error
// event are kept and read until the channel closes or the watch's time is up (the etcd3 watcher
// sends them: nonissues/k8s-etcd3-watcher-events-after-error.md; the test reports an error). As
// the test's RunWatchTraffic, a watch shorter than HiccupDuration is followed by a sleep for the
// rest of it.
func runWatch(s storage.Interface, in Input) (Output, Obj, bool) {
	if in.Skip {
		return Output{WFailed: true}, Obj{}, false
	}
	start := time.Now()
	evs, raw, failed := watchEvents(s, in)
	if d := time.Since(start); d < hiccupDuration {
		time.Sleep(hiccupDuration - d)
	}
	if failed {
		return Output{WFailed: true}, Obj{}, false
	}
	o, ok := lastObj(evs)
	return Output{WEvents: encodeWEvents(evs), Raw: Raw{Events: raw}}, o, ok
}

// watchEvents runs the watch in through the store s, consumed as in.Behavior says (consume): its
// events (as recorded, and as received), or true if the Watch call failed. The watch's context is the driver's own
// WithCancel(Background()), not the test's WithTimeout(2s + HiccupDuration): the driver cancels it
// once it has stopped reading (where the test's deadline would fire, at the latest), so every event
// it records was received while the watch was live (not stopped, its context not done), when the
// store promises a gap-free prefix of the history (notes/k8s-7f5a-draft.md §2; after a deadline the
// watcher may skip events, nonissues/k8s-etcd3-watcher-gap-after-cancel.md). The consumer's timer
// (watchDuration) bounds the watch as the deadline did.
func watchEvents(s storage.Interface, in Input) ([]WEvent, []watch.Event, bool) {
	ctx, cancel := context.WithCancel(context.Background())
	w, err := s.Watch(ctx, in.WKey, watchOptions(in))
	if err != nil {
		cancel()
		return nil, nil, true
	}
	evs, raw := consume(w, in)
	w.Stop()
	cancel()
	return evs, raw, false
}

// consume reads the watch w as in.Behavior says (the test's runWatch): for watchDuration or until
// maxEvents events, or until the channel closes; slow (slowDelay before each read), with a hiccup
// (one HiccupDuration pause after the first event, once a watch-list's initial events are done),
// or stalled (nothing read for HiccupDuration, then no events). Returns the events as recorded
// (toWEvent) and as received, one for one.
func consume(w watch.Interface, in Input) ([]WEvent, []watch.Event) {
	timer := time.NewTimer(watchDuration)
	defer timer.Stop()
	if in.Behavior == BStalled {
		<-time.After(hiccupDuration)
		return nil, nil
	}
	initialDone := in.SendInit != 2
	hiccupDone := in.Behavior != BHiccup
	var evs []WEvent
	var raw []watch.Event
	for {
		if initialDone {
			var delay time.Duration
			if !hiccupDone && len(evs) > 0 {
				delay = hiccupDuration
				hiccupDone = true
			} else if in.Behavior == BSlow {
				delay = slowDelay
			}
			if delay > 0 {
				select {
				case <-timer.C:
					return evs, raw
				case <-time.After(delay):
				}
			}
		}
		select {
		case <-timer.C:
			return evs, raw
		case ev, open := <-w.ResultChan():
			if !open {
				return evs, raw
			}
			we := toWEvent(ev)
			evs = append(evs, we)
			raw = append(raw, ev)
			if we.Type == WBookmark {
				initialDone = true
			}
			if len(evs) >= maxEvents {
				return evs, raw
			}
		}
	}
}

// lastObj is the object of the last event that is not an error (the test's lastNonErrorEvent):
// the watcher's next cached object.
func lastObj(evs []WEvent) (Obj, bool) {
	for i := len(evs) - 1; i >= 0; i-- {
		if evs[i].Type != WError && evs[i].Type != WBad {
			return evs[i].Obj, true
		}
	}
	return Obj{}, false
}

// ---------------------------------------------------------------------------------------------
// The check (correctness.WatchValidator, against a configuration's history)

// A change is the write at revision rv: its key and the item before and after (the replay's
// Change).
type change struct {
	key       string
	prev, cur Obj
	hasPrev   bool
	hasCur    bool
	rv        uint64
}

// changeAt is the change at revision r: the first key (in key order) whose item differs between
// the stores at r-1 and r, a merge of their key-sorted items (a write changes one key), or false.
func changeAt(prev mstore, cur mstore, r uint64) (change, bool) {
	i, j := 0, 0
	for i < len(prev.items) || j < len(cur.items) {
		switch {
		case j >= len(cur.items) || (i < len(prev.items) && prev.items[i].key < cur.items[j].key):
			p := prev.items[i]
			return change{key: p.key, prev: p.obj, hasPrev: true, rv: r}, true
		case i >= len(prev.items) || cur.items[j].key < prev.items[i].key:
			q := cur.items[j]
			return change{key: q.key, cur: q.obj, hasCur: true, rv: r}, true
		default:
			p, q := prev.items[i], cur.items[j]
			if p != q {
				return change{key: p.key, prev: p.obj, cur: q.obj, hasPrev: true, hasCur: true, rv: r}, true
			}
			i++
			j++
		}
	}
	return change{}, false
}

// toEvent is the change's event for a watch of in (Change.toWatchEvent): Modified if the
// predicate matches both, Added if only the new one, Deleted (the old object at the change's
// revision) if only the old one, none otherwise.
func toEvent(in Input, ch change) (WEvent, bool) {
	pred := predicate(in)
	cm, pm := false, false
	if ch.hasCur {
		o := ch.cur
		ok, err := pred.Matches(&o)
		cm = err == nil && ok
	}
	if ch.hasPrev {
		o := ch.prev
		ok, err := pred.Matches(&o)
		pm = err == nil && ok
	}
	switch {
	case cm && pm:
		return WEvent{Type: WModified, Obj: ch.cur}, true
	case cm:
		return WEvent{Type: WAdded, Obj: ch.cur}, true
	case pm:
		o := ch.prev
		o.ResourceVersion = ch.rv
		return WEvent{Type: WDeleted, Obj: o}, true
	}
	return WEvent{}, false
}

// initialEvents is the watch's initial events at the store st (Model.initialEvents): an Added
// event for each matching item in scope, in key order.
func initialEvents(in Input, st mstore) []WEvent {
	pred := predicate(in)
	var evs []WEvent
	for _, it := range st.items {
		if !keyInScope(in.WKey, in.Recursive, storeKey(it.key)) {
			continue
		}
		o := it.obj
		if ok, err := pred.Matches(&o); err == nil && ok {
			evs = append(evs, WEvent{Type: WAdded, Obj: it.obj})
		}
	}
	return evs
}

// eventsEqual compares events by type and object (the validator's references, key, type and
// resource version, and its objects).
func eventsEqual(a, b []WEvent) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].Type != b[i].Type || a[i].Obj != b[i].Obj {
			return false
		}
	}
	return true
}

// bookmarksOk is validateBookmarks, on the events that are not errors.
func bookmarksOk(evs []WEvent) bool {
	var lastBookmark, lastEvent uint64
	annotated := false
	for _, ev := range evs {
		rv := ev.Obj.ResourceVersion
		if ev.Type == WBookmark {
			if rv < lastBookmark || rv < lastEvent {
				return false
			}
			lastBookmark = rv
			if ev.Obj.Annotated {
				if annotated {
					return false
				}
				annotated = true
			}
			continue
		}
		if rv <= lastBookmark {
			return false
		}
		if rv > lastEvent {
			lastEvent = rv
		}
	}
	return true
}

// watchOk is the validator's ValidateWatch of the watch in with output out, against the
// configuration c's history: a failed or skipped watch constrains nothing; a bad event (a foreign
// object, an Error event without a Failure status) rejects; Error events are dropped wherever
// they are (validateMaybeLastEventError wants one, last: the etcd3 watcher can send events after
// it); every other event's resource version, bookmarks' included, is at most the
// configuration's; then the bookmarks, the initial events at the initial-events-end
// bookmark's revision (if the watch asked for them; a watch that ended before that bookmark: a
// prefix of the initial events at some revision, where the validator wants none), and the
// events over the revisions they mark (validateReliable), every revision involved at most the
// configuration's.
func watchOk(in Input, out Output, c mcfg) bool {
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
		return watchListOk(in, req, evs, c)
	}
	return reliableOk(in, req, evs, c)
}

// checkedEvents is the events that are not errors, or false if one is bad or, an error aside,
// has a resource version above rv.
func checkedEvents(all []WEvent, rv uint64) ([]WEvent, bool) {
	var evs []WEvent
	for _, ev := range all {
		if ev.Type >= WBad {
			return nil, false
		}
		if ev.Type == WError {
			continue
		}
		if ev.Obj.ResourceVersion > rv {
			return nil, false
		}
		evs = append(evs, ev)
	}
	return evs, true
}

// firstBookmark is the index of the first bookmark, or -1.
func firstBookmark(evs []WEvent) int {
	for i, ev := range evs {
		if ev.Type == WBookmark {
			return i
		}
	}
	return -1
}

// watchListOk is the check of a watch-list (SendInitialEvents): the initial events at the
// initial-events-end bookmark's revision, then the events after it; a watch that ended before
// that bookmark, a prefix of the initial events at some revision.
func watchListOk(in Input, req uint64, evs []WEvent, c mcfg) bool {
	b := firstBookmark(evs)
	if b < 0 {
		return initialPrefixOk(in, req, evs, c)
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
	return reliableOk(in, req, evs[b:], c)
}

// initialPrefixOk: the events are a prefix of the initial events at some revision from the
// requested one (1 for none) to the configuration's.
func initialPrefixOk(in Input, req uint64, evs []WEvent, c mcfg) bool {
	if len(evs) == 0 {
		return true
	}
	lo := req
	if lo < 1 {
		lo = 1
	}
	for r := lo; r <= c.st.rv; r++ {
		init := initialEvents(in, histAt(c.hist, r))
		if len(evs) <= len(init) && eventsEqual(init[:len(evs)], evs) {
			return true
		}
	}
	return false
}

// reliableOk is validateReliable: the revisions the events mark (watchRevisionRange), and the
// events there exactly the changes' events in scope. (KWatch.lean's reliableOkL: no event or
// bookmark constrains nothing; the events' revisions are at most the configuration's, below 2^63,
// so rv+1 does not overflow.)
func reliableOk(in Input, req uint64, evs []WEvent, c mcfg) bool {
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
	return eventsEqual(wantEvents(in, lo, hi, c), nonBookmarks(evs))
}

// evRange is the revisions the events mark (eventResourceVersionRange): from the least event's
// revision (a bookmark's plus one) to the greatest event's plus one (a bookmark's), exclusive.
func evRange(evs []WEvent) (uint64, uint64) {
	lo, hi := ^uint64(0), uint64(0)
	for _, ev := range evs {
		rv := ev.Obj.ResourceVersion
		if ev.Type == WBookmark {
			lo = min(lo, rv+1)
			hi = max(hi, rv)
		} else {
			lo = min(lo, rv)
			hi = max(hi, rv+1)
		}
	}
	return lo, hi
}

// reliableLo is the start of the window the request pins (watchRevisionRange): after the
// requested revision, for NotOlderThan only if the events start before it.
func reliableLo(in Input, req uint64, lo uint64) uint64 {
	if in.Match == MNotOlderThan {
		if req > 0 {
			return max(lo, req+1)
		}
		return lo
	}
	if req > 0 {
		return req + 1
	}
	return lo
}

// wantEvents is the changes' events in scope at the revisions [lo, hi) (from 2: revision 1 is the
// empty store).
func wantEvents(in Input, lo uint64, hi uint64, c mcfg) []WEvent {
	var want []WEvent
	for r := max(lo, 2); r < hi; r++ {
		ch, ok := changeAt(histAt(c.hist, r-1), histAt(c.hist, r), r)
		if !ok || !keyInScope(in.WKey, in.Recursive, storeKey(ch.key)) {
			continue
		}
		if ev, ok := toEvent(in, ch); ok {
			want = append(want, ev)
		}
	}
	return want
}

// nonBookmarks is the events that are not bookmarks.
func nonBookmarks(evs []WEvent) []WEvent {
	var got []WEvent
	for _, ev := range evs {
		if ev.Type != WBookmark {
			got = append(got, ev)
		}
	}
	return got
}

// What the check cannot see (as upstream's validator): a watch whose window the request does not
// pin (RV "" or "0", not a watch-list) starts at its first event, so a dropped first event, or
// the only one, leaves a valid window; so does a dropped last event of any watch.
