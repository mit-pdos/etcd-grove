// Package cmap is a thread-safe concurrent map.
//
// MODEL: this is the model of github.com/orcaman/concurrent-map v1.0.0 (models/README.md, "The
// third-party library models"), the API the dsverify kits call (SwiftPaxos's `swift` package, in
// the swiftpaxos kit): SHARD_COUNT, ConcurrentMap, ConcurrentMapShared, New, GetShard, Set,
// Upsert (UpsertCb), Get, Has, Remove, IterCb (IterCb), Count and IsEmpty (the fork's tests call
// IsEmpty, `swift/sw4_test.go`); and MarshalJSON, which encoding/json reaches through its
// json.Marshaler interface, a panic with a NotModelled value. Every other function it keeps is
// v1.0.0's code, unchanged (the same types, shards, fnv32 hash of the key, SHARD_COUNT read by New,
// Count and every GetShard, the same locks, Upsert's and IterCb's callbacks called with their
// shard's lock held). It leaves out what no program here calls and no interface of Go's reaches:
// MSet, SetIfAbsent, RemoveCb, Pop, Tuple, Iter, IterBuffered, Clear, Items, Keys (and their
// helpers snapshot and fanIn).
//
// The trusted claim: every behavior of v1.0.0 through this API, as the program observes it, is a
// behavior of the model (the same code and types), but a map's JSON, outside the model (the
// NotModelled panic). The evidence: models/diff.py concurrent-map and models/internal/tpdifftest
// (run.sh: random operation sequences, sequential and concurrent, with several SHARD_COUNTs, and
// fmt's printing, against v1.0.0 and the model).
package cmap

import (
	"sync"
)

var SHARD_COUNT = 32

// A "thread" safe map of type string:Anything.
// To avoid lock bottlenecks this map is dived to several (SHARD_COUNT) map shards.
type ConcurrentMap []*ConcurrentMapShared

// A "thread" safe string to anything map.
type ConcurrentMapShared struct {
	items        map[string]interface{}
	sync.RWMutex // Read Write mutex, guards access to internal map.
}

// Creates a new concurrent map.
func New() ConcurrentMap {
	m := make(ConcurrentMap, SHARD_COUNT)
	for i := 0; i < SHARD_COUNT; i++ {
		m[i] = &ConcurrentMapShared{items: make(map[string]interface{})}
	}
	return m
}

// GetShard returns shard under given key
func (m ConcurrentMap) GetShard(key string) *ConcurrentMapShared {
	return m[uint(fnv32(key))%uint(SHARD_COUNT)]
}

// Sets the given value under the specified key.
func (m ConcurrentMap) Set(key string, value interface{}) {
	// Get map shard.
	shard := m.GetShard(key)
	shard.Lock()
	shard.items[key] = value
	shard.Unlock()
}

// Callback to return new element to be inserted into the map
// It is called while lock is held, therefore it MUST NOT
// try to access other keys in same map, as it can lead to deadlock since
// Go sync.RWLock is not reentrant
type UpsertCb func(exist bool, valueInMap interface{}, newValue interface{}) interface{}

// Insert or Update - updates existing element or inserts a new one using UpsertCb
func (m ConcurrentMap) Upsert(key string, value interface{}, cb UpsertCb) (res interface{}) {
	shard := m.GetShard(key)
	shard.Lock()
	v, ok := shard.items[key]
	res = cb(ok, v, value)
	shard.items[key] = res
	shard.Unlock()
	return res
}

// Get retrieves an element from map under given key.
func (m ConcurrentMap) Get(key string) (interface{}, bool) {
	// Get shard
	shard := m.GetShard(key)
	shard.RLock()
	// Get item from shard.
	val, ok := shard.items[key]
	shard.RUnlock()
	return val, ok
}

// Count returns the number of elements within the map.
func (m ConcurrentMap) Count() int {
	count := 0
	for i := 0; i < SHARD_COUNT; i++ {
		shard := m[i]
		shard.RLock()
		count += len(shard.items)
		shard.RUnlock()
	}
	return count
}

// Looks up an item under specified key
func (m ConcurrentMap) Has(key string) bool {
	// Get shard
	shard := m.GetShard(key)
	shard.RLock()
	// See if element is within shard.
	_, ok := shard.items[key]
	shard.RUnlock()
	return ok
}

// Remove removes an element from the map.
func (m ConcurrentMap) Remove(key string) {
	// Try to get shard.
	shard := m.GetShard(key)
	shard.Lock()
	delete(shard.items, key)
	shard.Unlock()
}

// IsEmpty checks if map is empty.
func (m ConcurrentMap) IsEmpty() bool {
	return m.Count() == 0
}

// Iterator callback,called for every key,value found in
// maps. RLock is held for all calls for a given shard
// therefore callback sess consistent view of a shard,
// but not across the shards
type IterCb func(key string, v interface{})

// Callback based iterator, cheapest way to read
// all elements in a map.
func (m ConcurrentMap) IterCb(fn IterCb) {
	for idx := range m {
		shard := (m)[idx]
		shard.RLock()
		for key, value := range shard.items {
			fn(key, value)
		}
		shard.RUnlock()
	}
}

//Reviles ConcurrentMap "private" variables to json marshal.
//
// MODEL: a panic with a NotModelled value (v1.0.0: the items, gathered by IterBuffered's
// goroutines and channels, encoded by encoding/json as a map[string]interface{}).
func (m ConcurrentMap) MarshalJSON() ([]byte, error) {
	panic(notModelled{"MarshalJSON"})
}

// MODEL: the models' panic value, for what the model does not model.
type notModelled struct{ what string }

func (e notModelled) Error() string { return "concurrent-map model: not modelled: " + e.what }

// NotModelled marks the value as the models' panic.
func (notModelled) NotModelled() {}

func fnv32(key string) uint32 {
	hash := uint32(2166136261)
	const prime32 = uint32(16777619)
	keyLength := len(key)
	for i := 0; i < keyLength; i++ {
		hash *= prime32
		hash ^= uint32(key[i])
	}
	return hash
}

// Concurrent map uses Interface{} as its value, therefor JSON Unmarshal
// will probably won't know which to type to unmarshal into, in such case
// we'll end up with a value of type map[string]interface{}, In most cases this isn't
// out value type, this is why we've decided to remove this functionality.

// func (m *ConcurrentMap) UnmarshalJSON(b []byte) (err error) {
// 	// Reverse process of Marshal.

// 	tmp := make(map[string]interface{})

// 	// Unmarshal into a single map.
// 	if err := json.Unmarshal(b, &tmp); err != nil {
// 		return nil
// 	}

// 	// foreach key,value pair in temporary map insert into our concurrent map.
// 	for key, val := range tmp {
// 		m.Set(key, val)
// 	}
// 	return nil
// }
