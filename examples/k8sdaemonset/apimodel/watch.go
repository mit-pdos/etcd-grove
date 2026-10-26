package apimodel

import (
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/watch"
)

// watcher is one watch of a table: it sends the initial objects, then the table's log from
// index next on, filtered by namespace.
type watcher struct {
	s     *Server
	t     *table
	ns    string
	admin bool

	initial   []object
	bookmarks bool
	ch        chan watch.Event
	done      chan struct{}

	// guarded by s.mu
	next    int
	sentRV  uint64
	stopped bool
}

// watch starts a watch of t (the package documentation's Watch).
func (s *Server) watch(t *table, ns string, opts metav1.ListOptions, admin bool) (watch.Interface, error) {
	if opts.LabelSelector != "" || opts.FieldSelector != "" {
		return nil, apierrors.NewBadRequest("model: selectors are not supported")
	}
	if opts.SendInitialEvents != nil {
		return nil, apierrors.NewBadRequest("model: sendInitialEvents is not supported")
	}
	if s.chance(s.cfg.FailReads, admin) {
		return nil, apierrors.NewInternalError(errRead)
	}
	w := &watcher{s: s, t: t, ns: ns, admin: admin, bookmarks: opts.AllowWatchBookmarks,
		ch: make(chan watch.Event), done: make(chan struct{})}

	s.mu.Lock()
	var start uint64
	if opts.ResourceVersion == "" || opts.ResourceVersion == "0" {
		for key, obj := range t.objs {
			if ns == "" || key.Namespace == ns {
				w.initial = append(w.initial, copyObject(obj))
			}
		}
		start = s.rev
	} else {
		n, ok := s.rvs[opts.ResourceVersion]
		if !ok || (n < s.rev && s.chance(s.cfg.ExpireWatches, admin)) {
			s.mu.Unlock()
			return nil, apierrors.NewResourceExpired("too old resource version: " + opts.ResourceVersion)
		}
		start = n
	}
	next := 0
	for next < len(t.log) && t.log[next].rv <= start {
		next = next + 1
	}
	w.next = next
	w.sentRV = start
	s.mu.Unlock()

	go w.run()
	return w, nil
}

// ResultChan implements watch.Interface.
func (w *watcher) ResultChan() <-chan watch.Event {
	return w.ch
}

// Stop implements watch.Interface.
func (w *watcher) Stop() {
	w.s.mu.Lock()
	if !w.stopped {
		w.stopped = true
		close(w.done)
		w.s.changed.Broadcast()
	}
	w.s.mu.Unlock()
}

// send delivers ev unless the watch is stopped first.
func (w *watcher) send(ev watch.Event) bool {
	select {
	case w.ch <- ev:
		return true
	case <-w.done:
		return false
	}
}

// run is the watch's producer; it closes the result channel when the watch ends.
func (w *watcher) run() {
	for _, obj := range w.initial {
		if !w.send(watch.Event{Type: watch.Added, Object: obj}) {
			close(w.ch)
			return
		}
	}
	for {
		s := w.s
		s.mu.Lock()
		bookmark := false
		for !w.stopped && w.next >= len(w.t.log) {
			if w.bookmarks && w.sentRV < s.rev && s.chance(s.cfg.Bookmarks, w.admin) {
				bookmark = true
				break
			}
			s.changed.Wait()
		}
		if w.stopped {
			s.mu.Unlock()
			close(w.ch)
			return
		}
		var ev watch.Event
		if bookmark {
			b := w.t.empty()
			b.SetResourceVersion(rvString(s.rev))
			w.sentRV = s.rev
			ev = watch.Event{Type: watch.Bookmark, Object: b}
		} else {
			c := w.t.log[w.next]
			w.next = w.next + 1
			w.sentRV = c.rv
			if w.ns != "" && c.obj.GetNamespace() != w.ns {
				s.mu.Unlock()
				continue
			}
			ev = watch.Event{Type: c.typ, Object: copyObject(c.obj)}
		}
		end := s.chance(s.cfg.EndWatches, w.admin)
		s.mu.Unlock()
		if end || !w.send(ev) {
			close(w.ch)
			return
		}
	}
}
