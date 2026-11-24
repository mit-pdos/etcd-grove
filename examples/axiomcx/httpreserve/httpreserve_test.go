package httpreserve

import "testing"

func TestMainPanics(t *testing.T) {
	defer func() {
		r := recover()
		t.Logf("recovered: %v", r)
		if r == nil {
			t.Fatal("Main did not panic")
		}
	}()
	Main()
}
