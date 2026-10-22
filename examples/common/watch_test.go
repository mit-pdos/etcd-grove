package common

import "testing"

// mustPanic runs f and fails the test unless it panics.
func mustPanic(t *testing.T, name string, f func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Errorf("%s: no panic", name)
		}
	}()
	f()
}

// TestCheck checks the checker on hand-made histories: a good one passes; a delete, a repeated or
// decreasing revision, a gap, a put no writer attempted, a successful Put missing or different
// each panic.
func TestCheck(t *testing.T) {
	tried := []KV{{"wk/k0", "a"}, {"wk/k1", "b"}, {"wk/k0", "c"}}
	oks := []PutRec{{2, "wk/k0", "a"}, {4, "wk/k0", "c"}}
	good := []Event{{2, "wk/k0", "a", true}, {3, "wk/k1", "b", true}, {4, "wk/k0", "c", true}}
	Check("watchkv", "Put", good, tried, oks)
	Check("watchkv", "Put", nil, tried, nil)

	mustPanic(t, "delete", func() {
		Check("watchkv", "Put", []Event{{2, "wk/k0", "a", false}}, tried, nil)
	})
	mustPanic(t, "repeat", func() {
		Check("watchkv", "Put", []Event{{2, "wk/k0", "a", true}, {2, "wk/k1", "b", true}}, tried, nil)
	})
	mustPanic(t, "gap", func() {
		Check("watchkv", "Put", []Event{{2, "wk/k0", "a", true}, {4, "wk/k1", "b", true}}, tried, nil)
	})
	mustPanic(t, "start", func() {
		Check("watchkv", "Put", []Event{{3, "wk/k0", "a", true}}, tried, nil)
	})
	mustPanic(t, "unattempted", func() {
		Check("watchkv", "Put", []Event{{2, "wk/k2", "d", true}}, tried, nil)
	})
	mustPanic(t, "missing", func() {
		Check("watchkv", "Put", good[:2], tried, oks)
	})
	mustPanic(t, "different", func() {
		Check("watchkv", "Put", good, tried, []PutRec{{3, "wk/k0", "a"}})
	})
}

// TestMaxRev checks MaxRev.
func TestMaxRev(t *testing.T) {
	if m := MaxRev(nil); m != 0 {
		t.Fatalf("MaxRev(nil) = %d", m)
	}
	if m := MaxRev([]PutRec{{5, "a", "b"}, {9, "a", "b"}, {7, "a", "b"}}); m != 9 {
		t.Fatalf("MaxRev = %d", m)
	}
}
