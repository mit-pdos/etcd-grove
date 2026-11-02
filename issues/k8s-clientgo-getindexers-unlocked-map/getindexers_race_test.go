package cache_test

import (
	"fmt"
	"sync"
	"testing"

	"k8s.io/client-go/tools/cache"
)

// An Indexer is safe for concurrent use, and AddIndexers is documented to work
// on a store that already has items (a running informer's). GetIndexers returns
// the store's own map, read without the lock, while AddIndexers writes it under
// the lock: run with -race.
func TestGetIndexersRacesAddIndexers(t *testing.T) {
	idx := cache.NewIndexer(cache.MetaNamespaceKeyFunc, cache.Indexers{})
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		defer wg.Done()
		for i := 0; i < 1000; i++ {
			if err := idx.AddIndexers(cache.Indexers{fmt.Sprintf("i%d", i): func(obj interface{}) ([]string, error) { return nil, nil }}); err != nil {
				t.Error(err)
			}
		}
	}()
	go func() {
		defer wg.Done()
		for i := 0; i < 1000; i++ {
			_ = idx.GetIndexers()["i0"] // as pkg/controller's AddPodNodeNameIndexer does
		}
	}()
	wg.Wait()
}
