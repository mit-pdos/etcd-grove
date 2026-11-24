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

// The first fix's residual (see the package comment): it applied, and the call is refused; the final
// axiom, which reads the chain, does not apply.
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
