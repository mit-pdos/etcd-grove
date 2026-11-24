package bridgeaddrleft

import (
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

func TestMainPanics(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.Reset(t, "bridgeaddrleft")
	defer func() {
		r := recover()
		t.Logf("recovered: %v", r)
		if r == nil {
			t.Fatal("Main did not panic")
		}
	}()
	Main()
}
