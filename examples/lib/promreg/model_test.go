package promreg

// The evidence that the model is client_golang v1.24.1's default registry (notes/prom-registry.md):
// each test runs the real registry and the model side by side.

import (
	"errors"
	"reflect"
	"sort"
	"strings"
	"testing"
	"unsafe"

	"github.com/cespare/xxhash/v2"
	"github.com/prometheus/client_golang/prometheus"
)

// field reads the unexported field name of the struct v.
func field(v reflect.Value, name string) reflect.Value {
	f := v.FieldByName(name)
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem()
}

// realState is what the model keeps of a real *prometheus.Registry.
func realState(r *prometheus.Registry) (map[uint64]bool, map[string]uint64, map[uint64]bool) {
	v := reflect.ValueOf(r).Elem()
	ids := map[uint64]bool{}
	for _, k := range field(v, "descIDs").MapKeys() {
		ids[k.Uint()] = true
	}
	dims := map[string]uint64{}
	dm := field(v, "dimHashesByName")
	for _, k := range dm.MapKeys() {
		dims[k.String()] = dm.MapIndex(k).Uint()
	}
	cs := map[uint64]bool{}
	for _, k := range field(v, "collectorsByID").MapKeys() {
		cs[k.Uint()] = true
	}
	return ids, dims, cs
}

func sameState(t *testing.T, r *prometheus.Registry, m *Registry) {
	t.Helper()
	ids, dims, cs := realState(r)
	if !reflect.DeepEqual(ids, m.descIDs) || !reflect.DeepEqual(dims, m.dimHashesByName) ||
		!reflect.DeepEqual(cs, m.collectorsByID) {
		t.Fatalf("states differ:\nreal  %v\n      %v\n      %v\nmodel %v\n      %v\n      %v",
			ids, dims, cs, m.descIDs, m.dimHashesByName, m.collectorsByID)
	}
}

// DescsOf is what the model reads of a collector (`collectorDescs`, TrustedCode): the descriptors
// its Describe sends, in order.
func DescsOf(c prometheus.Collector) []Desc {
	ch := make(chan *prometheus.Desc, 1000)
	go func() { c.Describe(ch); close(ch) }()
	var ds []Desc
	for d := range ch {
		v := reflect.ValueOf(d).Elem()
		ds = append(ds, Desc{
			ID:      field(v, "id").Uint(),
			FQName:  field(v, "fqName").String(),
			DimHash: field(v, "dimHash").Uint(),
			Invalid: !field(v, "err").IsNil(),
		})
	}
	return ds
}

// code classifies the real Register's result as the model's outcomes.
func code(err error) uint64 {
	if err == nil {
		return OK
	}
	var are prometheus.AlreadyRegisteredError
	if errors.As(err, &are) {
		return ErrAlreadyRegistered
	}
	s := err.Error()
	switch {
	case strings.Contains(s, "is invalid"):
		return ErrInvalid
	case strings.Contains(s, "a previously registered descriptor with the same fully-qualified name"):
		return ErrDims
	case strings.Contains(s, "descriptors reported by collector have inconsistent"):
		return ErrNewDims
	case strings.Contains(s, "already exists with the same fully-qualified name and const label values"):
		return ErrDuplicateDesc
	}
	return 99
}

// realDefault is a registry in the default registry's initial state (registry.go's init).
func realDefault() *prometheus.Registry {
	r := prometheus.NewRegistry()
	r.MustRegister(prometheus.NewProcessCollector(prometheus.ProcessCollectorOpts{}))
	r.MustRegister(prometheus.NewGoCollector())
	return r
}

func modelDefault() *Registry {
	m := NewRegistry()
	m.SeedBuiltins()
	return m
}

// TestBuiltins: SeedBuiltins is the default registry's state after client_golang's init, and a
// fresh registry with the two collectors registered is in that state.
func TestBuiltins(t *testing.T) {
	sameState(t, prometheus.DefaultRegisterer.(*prometheus.Registry), modelDefault())
	sameState(t, realDefault(), modelDefault())
	names := BuiltinNames()
	if !sort.StringsAreSorted(names) || len(names) != len(BuiltinDims()) {
		t.Fatal("BuiltinNames not sorted or not BuiltinDims' length")
	}
}

// multi is a collector describing the given descriptors.
type multi []*prometheus.Desc

func (m multi) Describe(ch chan<- *prometheus.Desc) {
	for _, d := range m {
		ch <- d
	}
}
func (m multi) Collect(chan<- prometheus.Metric) {}

func desc(name, help string, vl []string, cl prometheus.Labels) *prometheus.Desc {
	return prometheus.NewDesc(name, help, vl, cl)
}

// TestDecisions: on a sequence of registrations covering each check of Register, the model returns
// the real registry's outcome and keeps its state (the default registry's initial state first).
func TestDecisions(t *testing.T) {
	r, m := realDefault(), modelDefault()
	c1 := prometheus.NewCounter(prometheus.CounterOpts{Namespace: "etcd", Subsystem: "server", Name: "x", Help: "h"})
	steps := []struct {
		what string
		c    prometheus.Collector
	}{
		{"a counter", c1},
		{"the same counter again (collector ID)", c1},
		{"another counter of the same name", prometheus.NewCounter(prometheus.CounterOpts{Name: "etcd_server_x", Help: "h"})},
		{"the same name, other help (dimHash)", prometheus.NewCounter(prometheus.CounterOpts{Name: "etcd_server_x", Help: "other"})},
		{"a builtin's name", prometheus.NewGauge(prometheus.GaugeOpts{Name: "go_goroutines", Help: "h"})},
		{"a builtin's name and help", prometheus.NewGauge(prometheus.GaugeOpts{Name: "go_goroutines", Help: "Number of goroutines that currently exist."})},
		{"go_info without its label", prometheus.NewGauge(prometheus.GaugeOpts{Name: "go_info", Help: "h"})},
		{"an invalid name", prometheus.NewCounter(prometheus.CounterOpts{Name: "", Help: "h"})},
		{"a vector", prometheus.NewCounterVec(prometheus.CounterOpts{Name: "v", Help: "h"}, []string{"a"})},
		{"a vector's name, no labels", prometheus.NewCounter(prometheus.CounterOpts{Name: "v", Help: "h"})},
		{"ID collision (promidcollide)", prometheus.NewCounter(prometheus.CounterOpts{Name: "m_b699caa269ad35ee", Help: "a"})},
		{"ID collision, second", prometheus.NewCounter(prometheus.CounterOpts{Name: "m_641c7bdac316dcb7", Help: "b"})},
		{"no descriptor (unchecked)", multi{}},
		{"two descriptors", multi{desc("p", "h", nil, nil), desc("q", "h", nil, nil)}},
		{"one of them again, with a new one", multi{desc("p", "h", nil, nil), desc("r", "h", nil, nil)}},
		{"inconsistent within the collector", multi{desc("s", "h", nil, nil), desc("s", "h2", nil, prometheus.Labels{"k": "v"})}},
		{"a duplicate within the collector", multi{desc("u", "h", nil, nil), desc("u", "h", nil, nil)}},
		{"const labels", multi{desc("w", "h", nil, prometheus.Labels{"k": "1"}), desc("w", "h", nil, prometheus.Labels{"k": "2"})}},
		{"an invalid descriptor after a valid one", multi{desc("y", "h", nil, nil), desc("bad name", "h", nil, nil)}},
	}
	for _, s := range steps {
		got, want := m.Register(DescsOf(s.c)), code(r.Register(s.c))
		if got != want || want == 99 {
			t.Fatalf("%s: model %d, real %d", s.what, got, want)
		}
		sameState(t, r, m)
		t.Logf("%s: %d", s.what, got)
	}
}

// TestMustRegister: MustRegister panics exactly when Register returns an error (registry.go:416-422;
// prometheus.MustRegister is DefaultRegisterer.MustRegister).
func TestMustRegister(t *testing.T) {
	r := realDefault()
	c := prometheus.NewCounter(prometheus.CounterOpts{Name: "mr", Help: "h"})
	r.MustRegister(c)
	defer func() {
		if recover() == nil {
			t.Fatal("no panic")
		}
	}()
	r.MustRegister(c)
}

// TestConstructorDescs: the collectors etcd's packages make (`collectorName`) describe one valid
// descriptor named n with ID xxhash(n + "\xff") (`descId`), vectors included.
func TestConstructorDescs(t *testing.T) {
	o := prometheus.CounterOpts{Namespace: "etcd", Subsystem: "disk", Name: "n", Help: "h"}
	n := "etcd_disk_n"
	cs := []prometheus.Collector{
		prometheus.NewCounter(o),
		prometheus.NewGauge(prometheus.GaugeOpts(o)),
		prometheus.NewGaugeFunc(prometheus.GaugeOpts(o), func() float64 { return 0 }),
		prometheus.NewHistogram(prometheus.HistogramOpts{Namespace: "etcd", Subsystem: "disk", Name: "n", Help: "h",
			Buckets: prometheus.ExponentialBuckets(0.001, 2, 14)}),
		prometheus.NewCounterVec(o, []string{"a", "b"}),
		prometheus.NewGaugeVec(prometheus.GaugeOpts(o), []string{"a"}),
		prometheus.NewHistogramVec(prometheus.HistogramOpts{Namespace: "etcd", Subsystem: "disk", Name: "n", Help: "h"}, []string{"a"}),
	}
	for _, c := range cs {
		ds := DescsOf(c)
		if len(ds) != 1 || ds[0].FQName != n || ds[0].Invalid || ds[0].ID != xxhash.Sum64String(n+"\xff") {
			t.Fatalf("%T: %+v", c, ds)
		}
	}
}

// TestRandom: random registrations of collectors of one to three descriptors drawn from a small
// set of names, helps, variable and const labels (so that every check fires), both registries
// side by side; the outcomes and the states agree at every step.
func TestRandom(t *testing.T) {
	rnd := uint64(1)
	next := func(n uint64) uint64 { rnd = rnd*6364136223846793005 + 1442695040888963407; return (rnd >> 33) % n }
	names := []string{"a", "b", "c", "go_goroutines", "process_open_fds", "go_info", "", "m_b699caa269ad35ee", "m_641c7bdac316dcb7"}
	helps := []string{"h", "i", "Number of goroutines that currently exist."}
	for run := 0; run < 200; run++ {
		r, m := realDefault(), modelDefault()
		for step := 0; step < 30; step++ {
			var c multi
			for k := uint64(0); k <= next(3); k++ {
				var vl []string
				if next(3) == 0 {
					vl = []string{"x"}
				}
				var cl prometheus.Labels
				if next(3) == 0 {
					cl = prometheus.Labels{"k": []string{"1", "2"}[next(2)]}
				}
				c = append(c, desc(names[next(uint64(len(names)))], helps[next(uint64(len(helps)))], vl, cl))
			}
			got, want := m.Register(DescsOf(c)), code(r.Register(c))
			if got != want || want == 99 {
				t.Fatalf("run %d step %d: model %d, real %d", run, step, got, want)
			}
			sameState(t, r, m)
		}
	}
}
