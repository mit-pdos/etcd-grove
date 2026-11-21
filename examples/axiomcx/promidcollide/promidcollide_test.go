// Two distinct valid metric names whose label-free descriptors have the same ID
// (client_golang v1.24.1, desc.go: id = xxhash64(fqName + "\xff") when there are
// no const labels). Registering counters of both names with the default registry
// panics on the second (Registry.Register: the collector ID is taken,
// AlreadyRegisteredError), although neither name is registered twice:
// notes/axiom-review/prometheus-id-collision.md. The pair was found by a
// distinguished-point collision search (/shared/tmp/promdeep/collide, 17s on 16
// cores).
package promidcollide_test

import (
	"testing"

	"github.com/cespare/xxhash/v2"
	"github.com/prometheus/client_golang/prometheus"
)

const (
	n1 = "m_b699caa269ad35ee"
	n2 = "m_641c7bdac316dcb7"
)

func TestSameDescID(t *testing.T) {
	h1 := xxhash.Sum64String(n1 + "\xff")
	h2 := xxhash.Sum64String(n2 + "\xff")
	if h1 != h2 {
		t.Fatalf("no collision: %#x %#x", h1, h2)
	}
}

func TestMustRegisterPanics(t *testing.T) {
	c1 := prometheus.NewCounter(prometheus.CounterOpts{Name: n1, Help: "a"})
	c2 := prometheus.NewCounter(prometheus.CounterOpts{Name: n2, Help: "b"})
	prometheus.MustRegister(c1)
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("second MustRegister returned")
		}
		if _, ok := r.(prometheus.AlreadyRegisteredError); !ok {
			t.Fatalf("panic %v (%T), want AlreadyRegisteredError", r, r)
		}
		t.Logf("panics: %v", r)
	}()
	prometheus.MustRegister(c2)
}
