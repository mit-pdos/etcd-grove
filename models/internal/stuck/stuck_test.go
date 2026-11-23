package stuck

import "testing"

func TestRun(t *testing.T) {
	if o, _ := Run(func() {}); o != Returned {
		t.Errorf("return: %v", o)
	}
	if o, v := Run(func() { panic("x") }); o != Panicked || v != "x" {
		t.Errorf("panic: %v %v", o, v)
	}
	if o, v := Run(func() { var p *int; _ = *p }); o != Panicked || v == nil {
		t.Errorf("nil dereference: %v %v", o, v)
	}
	if o, _ := Run(func() { select {} }); o != Stuck {
		t.Errorf("select {}: %v", o)
	}
	for i := 0; i < 500; i++ {
		if !IsStuck(func() { select {} }) {
			t.Fatalf("select {} #%d", i)
		}
	}
}
