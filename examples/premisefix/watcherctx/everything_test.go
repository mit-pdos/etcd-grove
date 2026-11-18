package watcherctx

// k8s 7f-5b H2 (notes/k8s-7f5b-everything.md; decided by etcd-grove-02, 2026-11-16): the evidence of
// the strengthened trust-boundary spec fields.Everything.spec and of what storage's package fact
// records of the global storage.Everything, at the pins (k8s.io/apimachinery 0b7d352f711c,
// k8s.io/apiserver 9c4ec15b8038):
//
//   - TestFieldsEverythingEmpty: fields.Everything() (selector.go:76, `return andTerm{}`) returns a
//     non-nil Selector whose Empty() is true (andTerm.Empty, selector.go:190: len 0), on every call,
//     from several goroutines, and its Empty() has no effect visible to a later call.
//   - TestStorageEverythingValue: storage.Everything (interfaces.go:101) is the composite literal
//     {Label: labels.Everything(), Field: fields.Everything()}: Label and Field non-nil with Empty()
//     true, ShardSelector nil, every other field zero; and SelectionPredicate.Empty() on it is true
//     (what watchChan.filter/acceptAll then read), Matches of any object true without GetAttrs.

import (
	"sync"
	"testing"

	"k8s.io/apimachinery/pkg/fields"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apiserver/pkg/storage"
)

func TestFieldsEverythingEmpty(t *testing.T) {
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := 0; i < 100; i++ {
				s := fields.Everything()
				if s == nil {
					t.Error("fields.Everything() returned a nil Selector")
					return
				}
				if !s.Empty() || !s.Empty() {
					t.Error("fields.Everything().Empty() is false")
					return
				}
			}
		}()
	}
	wg.Wait()
}

func TestStorageEverythingValue(t *testing.T) {
	p := storage.Everything
	if p.Label == nil || !p.Label.Empty() {
		t.Fatalf("storage.Everything.Label: %#v", p.Label)
	}
	if p.Field == nil || !p.Field.Empty() {
		t.Fatalf("storage.Everything.Field: %#v", p.Field)
	}
	if p.ShardSelector != nil {
		t.Fatalf("storage.Everything.ShardSelector: %#v", p.ShardSelector)
	}
	if p.GetAttrs != nil || p.IndexLabels != nil || p.IndexFields != nil || p.Limit != 0 ||
		p.Continue != "" || p.AllowWatchBookmarks {
		t.Fatalf("storage.Everything has a non-zero field: %#v", p)
	}
	if !p.Empty() {
		t.Fatal("storage.Everything.Empty() is false")
	}
	// GetAttrs is nil: Matches must not call it (labelFieldEmpty answers first).
	var obj runtime.Object
	ok, err := p.Matches(obj)
	if !ok || err != nil {
		t.Fatalf("storage.Everything.Matches: %v %v", ok, err)
	}
}
