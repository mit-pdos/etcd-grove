package norefusal

import (
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

func TestMainPanics(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.Reset(t, "norefusal")
	defer func() {
		r := recover()
		t.Logf("recovered: %v", r)
		if r == nil {
			t.Fatal("Main did not panic")
		}
	}()
	Main()
}

// The residual route (see the package comment): the fixed axiom applies, and the call is refused.
func TestMainInterceptorPanics(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.Reset(t, "norefusal")
	defer func() {
		r := recover()
		t.Logf("recovered: %v", r)
		if r == nil {
			t.Fatal("MainInterceptor did not panic")
		}
	}()
	MainInterceptor()
}
