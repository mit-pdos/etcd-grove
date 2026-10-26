package store

import (
	"fmt"
	"testing"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/client-go/tools/cache"
)

// An index function that fails on one object: UpdateStore returns its error, but the store's
// B-tree already holds the object, and the next successful update publishes a snapshot (the
// latest one, and the one at its revision) that contains it, as if its event had succeeded.
func TestUpdateStoreIndexErrorLeavesElement(t *testing.T) {
	obj := func(name string) runtime.Object {
		return &metav1.PartialObjectMetadata{ObjectMeta: metav1.ObjectMeta{Name: name}}
	}
	indexers := cache.Indexers{
		"byName": func(o interface{}) ([]string, error) {
			name := o.(*metav1.PartialObjectMetadata).Name
			if name == "bad" {
				return nil, fmt.Errorf("cannot index %q", name)
			}
			return []string{name}, nil
		},
	}
	w := NewWatchCacheStorage(&indexers)

	if _, err := w.UpdateStore(watch.Added, &Element{Key: "/a", Object: obj("a")}, 10); err != nil {
		t.Fatalf("first update: %v", err)
	}
	_, err := w.UpdateStore(watch.Added, &Element{Key: "/bad", Object: obj("bad")}, 11)
	if err == nil {
		t.Fatalf("expected the index error")
	}
	// The failed update is not visible yet...
	if _, ok, _ := w.LatestSnapshot().GetByKey("/bad"); ok {
		t.Fatalf("visible right after the failed update")
	}
	// ...but the next successful one, at revision 12, publishes it.
	if _, err := w.UpdateStore(watch.Added, &Element{Key: "/c", Object: obj("c")}, 12); err != nil {
		t.Fatalf("third update: %v", err)
	}
	snap := w.LatestSnapshot()
	if _, ok, _ := snap.GetByKey("/bad"); ok {
		t.Logf("BUG: the snapshot at revision %d contains /bad, whose update at 11 failed",
			snap.ResourceVersion())
	} else {
		t.Fatalf("not reproduced: /bad absent")
	}
	// The index does not know it.
	items, _, err := w.indexer.ByIndex("byName", "bad")
	if err != nil {
		t.Fatalf("ByIndex: %v", err)
	}
	t.Logf("index byName=bad has %d items (the store has the element)", len(items))
}
