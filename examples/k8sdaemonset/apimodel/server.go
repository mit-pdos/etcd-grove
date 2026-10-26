package apimodel

import (
	"errors"
	"math/rand"
	"strconv"
	"sync"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apimachinery/pkg/watch"
)

// Config says which nondeterministic failures the server may produce (see the package
// documentation).
type Config struct {
	FailWrites      bool
	AmbiguousWrites bool
	FailReads       bool
	EndWatches      bool
	ExpireWatches   bool
	Bookmarks       bool
	// FaultPercent is the probability, in percent, of each flagged choice when run in Go.
	FaultPercent int64
}

// object is what the server stores: every API type the model serves is both.
type object interface {
	runtime.Object
	metav1.Object
}

// change is one entry of a resource's log: the object's state after the change (for a
// deletion, its last state), at the change's resource version.
type change struct {
	typ watch.EventType
	rv  uint64
	obj object
}

// table is one resource's state.
type table struct {
	resource   schema.GroupResource
	namespaced bool
	objs       map[types.NamespacedName]object
	log        []change
	// empty returns a new empty object of the resource's type (for bookmarks).
	empty func() object
}

// Server is the model API server.
type Server struct {
	mu sync.Mutex
	// changed is broadcast on every change to any table and when a watch stops.
	changed *sync.Cond

	cfg Config
	// rev is the last resource version issued (0: none yet).
	rev uint64
	// rvs maps every resource version issued to its number.
	rvs map[string]uint64
	// uids is the number of UIDs issued.
	uids uint64

	pods       *table
	nodes      *table
	daemonSets *table
	revisions  *table
}

// NewServer returns an empty server with the given failure configuration.
func NewServer(cfg Config) *Server {
	s := &Server{cfg: cfg, rvs: make(map[string]uint64)}
	s.changed = sync.NewCond(&s.mu)
	s.pods = newTable(schema.GroupResource{Resource: "pods"}, true, emptyPod)
	s.nodes = newTable(schema.GroupResource{Resource: "nodes"}, false, emptyNode)
	s.daemonSets = newTable(schema.GroupResource{Group: "apps", Resource: "daemonsets"}, true, emptyDaemonSet)
	s.revisions = newTable(schema.GroupResource{Group: "apps", Resource: "controllerrevisions"}, true, emptyRevision)
	return s
}

func newTable(gr schema.GroupResource, namespaced bool, empty func() object) *table {
	return &table{resource: gr, namespaced: namespaced, objs: make(map[types.NamespacedName]object), empty: empty}
}

// chance reports whether a flagged nondeterministic choice happens. Admin clients never fail.
func (s *Server) chance(flag bool, admin bool) bool {
	if !flag || admin {
		return false
	}
	return rand.Int63n(100) < s.cfg.FaultPercent
}

// rvString is a resource version's string form (decimal; injective).
func rvString(n uint64) string {
	return strconv.FormatUint(n, 10)
}

func copyObject(o object) object {
	return o.DeepCopyObject().(object)
}

// nextRV issues the next resource version. Called with mu held.
func (s *Server) nextRV() (uint64, string) {
	s.rev = s.rev + 1
	rv := rvString(s.rev)
	s.rvs[rv] = s.rev
	return s.rev, rv
}

// record stores obj (already at its new resource version) and appends the change. Called with
// mu held.
func (s *Server) record(t *table, typ watch.EventType, rv uint64, obj object) {
	key := types.NamespacedName{Namespace: obj.GetNamespace(), Name: obj.GetName()}
	if typ == watch.Deleted {
		delete(t.objs, key)
	} else {
		t.objs[key] = obj
	}
	t.log = append(t.log, change{typ: typ, rv: rv, obj: copyObject(obj)})
	s.changed.Broadcast()
}

var (
	errStorage   = errors.New("model: storage write failed")
	errRead      = errors.New("model: storage read failed")
	errAmbiguous = "model: the request timed out after the write was committed"
)

// create stores a new object (the package documentation's Create). prepare is the resource's
// create strategy.
func (s *Server) create(t *table, ns string, in object, prepare func(object), admin bool) (object, error) {
	if s.chance(s.cfg.FailWrites, admin) {
		return nil, apierrors.NewInternalError(errStorage)
	}
	obj := copyObject(in)
	if t.namespaced {
		if obj.GetNamespace() == "" {
			obj.SetNamespace(ns)
		} else if obj.GetNamespace() != ns {
			return nil, apierrors.NewBadRequest("the namespace of the provided object does not match the namespace sent on the request")
		}
	} else {
		obj.SetNamespace("")
	}
	if obj.GetResourceVersion() != "" {
		return nil, apierrors.NewBadRequest("resourceVersion should not be set on objects to be created")
	}

	s.mu.Lock()
	if obj.GetName() == "" {
		if obj.GetGenerateName() == "" {
			s.mu.Unlock()
			return nil, apierrors.NewBadRequest("name or generateName is required")
		}
		obj.SetName(obj.GetGenerateName() + rvString(s.rev+1))
	}
	key := types.NamespacedName{Namespace: obj.GetNamespace(), Name: obj.GetName()}
	if _, ok := t.objs[key]; ok {
		s.mu.Unlock()
		return nil, apierrors.NewAlreadyExists(t.resource, obj.GetName())
	}
	s.uids = s.uids + 1
	obj.SetUID(types.UID("uid-" + rvString(s.uids)))
	obj.SetCreationTimestamp(metav1.Now())
	prepare(obj)
	n, rv := s.nextRV()
	obj.SetResourceVersion(rv)
	s.record(t, watch.Added, n, obj)
	out := copyObject(obj)
	s.mu.Unlock()

	if s.chance(s.cfg.AmbiguousWrites, admin) {
		return nil, apierrors.NewTimeoutError(errAmbiguous, 0)
	}
	return out, nil
}

// get returns a copy of the stored object.
func (s *Server) get(t *table, ns string, name string, admin bool) (object, error) {
	if s.chance(s.cfg.FailReads, admin) {
		return nil, apierrors.NewInternalError(errRead)
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	obj, ok := t.objs[types.NamespacedName{Namespace: ns, Name: name}]
	if !ok {
		return nil, apierrors.NewNotFound(t.resource, name)
	}
	return copyObject(obj), nil
}

// list returns copies of the objects in ns ("": all) and the current resource version.
func (s *Server) list(t *table, ns string, opts metav1.ListOptions, admin bool) ([]object, string, error) {
	if opts.LabelSelector != "" || opts.FieldSelector != "" {
		return nil, "", apierrors.NewBadRequest("model: selectors are not supported")
	}
	if s.chance(s.cfg.FailReads, admin) {
		return nil, "", apierrors.NewInternalError(errRead)
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	var out []object
	for key, obj := range t.objs {
		if ns == "" || key.Namespace == ns {
			out = append(out, copyObject(obj))
		}
	}
	return out, rvString(s.rev), nil
}

// update replaces a stored object (the package documentation's Update and UpdateStatus).
// mutate returns the object to store from the stored one and the request's (both copies), or
// nil when the update changes nothing.
func (s *Server) update(t *table, ns string, in object, mutate func(old object, req object) object, admin bool) (object, error) {
	if s.chance(s.cfg.FailWrites, admin) {
		return nil, apierrors.NewInternalError(errStorage)
	}
	req := copyObject(in)
	if t.namespaced && req.GetNamespace() != "" && req.GetNamespace() != ns {
		return nil, apierrors.NewBadRequest("the namespace of the provided object does not match the namespace sent on the request")
	}

	s.mu.Lock()
	key := types.NamespacedName{Namespace: ns, Name: req.GetName()}
	if !t.namespaced {
		key.Namespace = ""
	}
	stored, ok := t.objs[key]
	if !ok {
		s.mu.Unlock()
		return nil, apierrors.NewNotFound(t.resource, req.GetName())
	}
	if req.GetResourceVersion() != "" && req.GetResourceVersion() != stored.GetResourceVersion() {
		s.mu.Unlock()
		return nil, apierrors.NewConflict(t.resource, req.GetName(),
			errors.New("the object has been modified; please apply your changes to the latest version and try again"))
	}
	obj := mutate(copyObject(stored), req)
	if obj == nil {
		out := copyObject(stored)
		s.mu.Unlock()
		return out, nil
	}
	obj.SetName(stored.GetName())
	obj.SetNamespace(stored.GetNamespace())
	obj.SetUID(stored.GetUID())
	obj.SetCreationTimestamp(stored.GetCreationTimestamp())
	n, rv := s.nextRV()
	obj.SetResourceVersion(rv)
	s.record(t, watch.Modified, n, obj)
	out := copyObject(obj)
	s.mu.Unlock()

	if s.chance(s.cfg.AmbiguousWrites, admin) {
		return nil, apierrors.NewTimeoutError(errAmbiguous, 0)
	}
	return out, nil
}

// remove deletes a stored object (the package documentation's Delete). grace returns the
// graceful-deletion period of the stored object under the options (0: delete at once).
func (s *Server) remove(t *table, ns string, name string, opts metav1.DeleteOptions, grace func(object, metav1.DeleteOptions) int64, admin bool) error {
	if s.chance(s.cfg.FailWrites, admin) {
		return apierrors.NewInternalError(errStorage)
	}

	s.mu.Lock()
	key := types.NamespacedName{Namespace: ns, Name: name}
	if !t.namespaced {
		key.Namespace = ""
	}
	stored, ok := t.objs[key]
	if !ok {
		s.mu.Unlock()
		return apierrors.NewNotFound(t.resource, name)
	}
	if opts.Preconditions != nil {
		p := opts.Preconditions
		if (p.UID != nil && *p.UID != stored.GetUID()) ||
			(p.ResourceVersion != nil && *p.ResourceVersion != stored.GetResourceVersion()) {
			s.mu.Unlock()
			return apierrors.NewConflict(t.resource, name, errors.New("the object's preconditions do not hold"))
		}
	}
	if stored.GetDeletionTimestamp() != nil {
		// already being deleted: nothing changes
		s.mu.Unlock()
		return nil
	}
	period := grace(stored, opts)
	obj := copyObject(stored)
	n, rv := s.nextRV()
	obj.SetResourceVersion(rv)
	if period > 0 || len(obj.GetFinalizers()) > 0 {
		now := metav1.Now()
		obj.SetDeletionTimestamp(&now)
		obj.SetDeletionGracePeriodSeconds(&period)
		s.record(t, watch.Modified, n, obj)
	} else {
		s.record(t, watch.Deleted, n, obj)
	}
	s.mu.Unlock()

	if s.chance(s.cfg.AmbiguousWrites, admin) {
		return apierrors.NewTimeoutError(errAmbiguous, 0)
	}
	return nil
}

// noGrace is the grace function of resources deleted at once.
func noGrace(object, metav1.DeleteOptions) int64 {
	return 0
}
