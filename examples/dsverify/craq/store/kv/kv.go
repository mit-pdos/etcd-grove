// kv package is an in-memory key/value database

package kv

import (
	"log"
	"sync"

	"github.com/despreston/go-craq/store"
)

// KV is an in-memory key/value storage.
type KV struct {
	items map[string][]*store.Item
	mu    sync.Mutex
}

// New store
func New() *KV {
	return &KV{
		items: make(map[string][]*store.Item),
	}
}

func (s *KV) lookup(key string) ([]*store.Item, bool) {
	items := s.items[key]
	if len(items) == 0 {
		return nil, false
	}
	return items, true
}

// Read an item from the store by key. If there is an uncommitted (dirty)
// version of the item in the store, it returns a ErrDirtystore.Item error. If
// no item exists for that key it returns a ErrNotFound error.
func (s *KV) Read(key string) (*store.Item, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	items, has := s.lookup(key)
	if !has {
		return nil, store.ErrNotFound
	}

	if !items[len(items)-1].Committed {
		return nil, store.ErrDirtyItem
	}

	return items[0], nil
}

// ReadVersion finds an item for the given key with the matching version. If no
// item is found for that version of key, ErrNotFound is returned
func (s *KV) ReadVersion(key string, version uint64) (*store.Item, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	items, has := s.lookup(key)
	if !has {
		return nil, store.ErrNotFound
	}

	for _, item := range items {
		if item.Version == version {
			return item, nil
		}
	}

	return nil, store.ErrNotFound
}

// Write a new item to the store.
func (s *KV) Write(key string, val []byte, version uint64) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	item := store.Item{
		Committed: false,
		Value:     val,
		Version:   version,
		Key:       key,
	}

	s.items[key] = append(s.items[key], &item)
	return nil
}

// Commit a version for the given key. All items with matching key and older
// than version are cleared (store.Storer). If no item has that version, the
// key's items are left as they are and ErrNotFound is returned.
func (s *KV) Commit(key string, version uint64) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	items, has := s.lookup(key)
	if !has {
		return store.ErrNotFound
	}

	// Mark the version committed.
	found := false
	for _, itm := range items {
		if itm.Version == version {
			itm.Committed = true
			found = true
		}
	}
	if !found {
		return store.ErrNotFound
	}

	// Remove the older versions (items arrive in any order, so compare versions).
	kept := []*store.Item{}
	for _, itm := range items {
		if itm.Version >= version {
			kept = append(kept, itm)
		}
	}
	s.items[key] = kept

	log.Printf("Marked version %d of key %s committed.\n", version, key)
	return nil
}

// AllNewerCommitted returns all committed items who's key is not in keyVersions
// or who's version is higher than the versions in keyVersions: for each key, its
// committed item with the highest version (items arrive in any order, so the last
// item is not necessarily the newest committed one).
func (s *KV) AllNewerCommitted(keyVersions map[string]uint64) ([]*store.Item, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	newer := []*store.Item{}

	for key, itemsForKey := range s.items {
		// Highest local committed version
		var local *store.Item
		for _, itm := range itemsForKey {
			if itm.Committed && (local == nil || itm.Version > local.Version) {
				local = itm
			}
		}
		if local == nil {
			continue
		}

		highestVer, has := keyVersions[key]
		if !has || local.Version > highestVer {
			newer = append(newer, local)
		}
	}

	return newer, nil
}

// AllNewerDirty returns all uncommitted items who's key is not in keyVersions
// or who's version is higher than the versions in keyVersions.
func (s *KV) AllNewerDirty(keyVersions map[string]uint64) ([]*store.Item, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	newer := []*store.Item{}

	for key, items := range s.items {
		// Highest local version
		local := items[len(items)-1]

		highestVer, has := keyVersions[key]
		if !local.Committed && (!has || local.Version > highestVer) {
			newer = append(newer, local)
		}
	}

	return newer, nil
}

// AllDirty returns all uncommitted items.
func (s *KV) AllDirty() ([]*store.Item, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	dirty := []*store.Item{}

	for _, forKey := range s.items {
		for _, item := range forKey {
			if !item.Committed {
				dirty = append(dirty, item)
			}
		}
	}

	return dirty, nil
}

// AllCommitted returns all committed items.
func (s *KV) AllCommitted() ([]*store.Item, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	committed := []*store.Item{}

	for _, forKey := range s.items {
		for _, item := range forKey {
			if item.Committed {
				committed = append(committed, item)
			}
		}
	}

	return committed, nil
}
