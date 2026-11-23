// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package treemap implements a map backed by red-black tree.
//
// Elements are ordered by key in the map.
//
// Structure is not thread safe.
//
// Reference: http://en.wikipedia.org/wiki/Associative_array
//
// MODEL: this is the model of github.com/emirpasic/gods v1.18.1's maps/treemap
// (models/README.md, "The third-party library models"), the API the dsverify kits call
// (SwiftPaxos's `state` package, in the swiftpaxos and epaxos kits): NewWith, Put, Get, Select,
// Iterator and the iterator's Next and Value, and the methods Go's standard library reaches
// through an interface: String (fmt.Stringer, gods' code) and MarshalJSON/UnmarshalJSON
// (encoding/json; each blocks forever, not modelled). gods' red-black tree (trees/redblacktree) is
// replaced by a slice of the entries sorted by the comparator, behind a pointer as gods' tree is
// (a Map's copies share it; a zero Map has none, and every operation but Iterator panics on it with
// a nil dereference, as gods'). Every other exported name of the package is left out.
//
// The trusted claim: every behavior of v1.18.1's treemap, as the program observes it through this
// API, is a behavior of the model, provided
//   - the comparator, on every pair (a, b) of keys the program passes to a map (a key with itself
//     included), returns without an effect the program observes and without panicking, the same
//     result each time, with sign(c(a, b)) = -sign(c(b, a)), and is transitive (a total
//     preorder); a key whose comparison with itself panics is allowed at the first Put into an
//     empty map, where gods calls comparator(k, k) and the model too;
//   - the program does not observe the representation (reflection, unsafe, or fmt's printing of a
//     Map or Iterator value through its fields, rather than of a *Map through String).
// What follows:
//   - Put(k, v): if an entry's key compares equal to k, its key and value become k and v (the
//     tree's node takes both); otherwise a new entry, in order.
//   - Get(k): the value of the entry whose key compares equal to k, and true; else nil, false.
//   - Select(f): a new map, the same comparator, holding the entries for which f(key, value) is
//     true, f called once per entry in key order (the tree's in-order iterator).
//   - Iterator(): before the first entry; Next() moves to the next entry in key order and reports
//     whether there is one (false forever once past the last); Value() is the current entry's,
//     and panics with a nil dereference when there is none (before the first Next, after the
//     last), gods' runtime error.
//   - String: gods' text ("TreeMap\nmap[k:v ...]").
// Outside the model (a call blocks forever, `select {}`): a change to a map (a Put) while an
// iterator over it is in use, Select's f included (the model counts the map's changes); a map's
// JSON (gods' ToJSON goes through utils.ToString and encoding/json of a map[string]interface{}).
// Not claimed: how many times and on which pairs the comparator is called (the tree walks a path,
// the model scans). Evidence: models/internal/tpdifftest (run.sh: random operation sequences and
// the edge cases above against v1.18.1 and the model).
package treemap

import (
	"fmt"
	"strings"

	"github.com/emirpasic/gods/utils"
)

// MODEL: an entry of the map (gods: a node of the red-black tree).
type entry struct {
	key   interface{}
	value interface{}
}

// MODEL: the map's state (gods: the red-black tree, *rbt.Tree): the comparator, the entries sorted
// by it, and the number of changes made (Put), which an iterator checks.
type sorted struct {
	comparator utils.Comparator
	entries    []entry
	changes    uint64
}

// Map holds the elements in a red-black tree
//
// MODEL: in a sorted slice behind a pointer (gods: tree *rbt.Tree).
type Map struct {
	state *sorted
}

// NewWith instantiates a tree map with the custom comparator.
func NewWith(comparator utils.Comparator) *Map {
	return &Map{state: &sorted{comparator: comparator}} // MODEL: gods: rbt.NewWith(comparator)
}

// MODEL: find returns the position of the first entry whose key is not less than key, and whether
// the two compare equal; it compares as the tree does, comparator(key, entry's key).
func (s *sorted) find(key interface{}) (int, bool) {
	i := 0
	for i < len(s.entries) {
		c := s.comparator(key, s.entries[i].key)
		if c == 0 {
			return i, true
		}
		if c < 0 {
			return i, false
		}
		i++
	}
	return i, false
}

// Put inserts key-value pair into the map.
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (m *Map) Put(key interface{}, value interface{}) {
	// MODEL: rbt.Tree.Put, on the sorted slice.
	s := m.state
	if len(s.entries) == 0 {
		// Assert key is of comparator's type for initial tree
		s.comparator(key, key)
		s.entries = append(s.entries, entry{key: key, value: value})
		s.changes++
		return
	}
	i, found := s.find(key)
	s.changes++
	if found {
		s.entries[i] = entry{key: key, value: value}
		return
	}
	s.entries = append(s.entries, entry{})
	copy(s.entries[i+1:], s.entries[i:])
	s.entries[i] = entry{key: key, value: value}
}

// Get searches the element in the map by key and returns its value or nil if key is not found in tree.
// Second return parameter is true if key was found, otherwise false.
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (m *Map) Get(key interface{}) (value interface{}, found bool) {
	// MODEL: rbt.Tree.Get, on the sorted slice.
	s := m.state
	i, ok := s.find(key)
	if ok {
		return s.entries[i].value, true
	}
	return nil, false
}

// String returns a string representation of container
func (m *Map) String() string {
	str := "TreeMap\nmap["
	it := m.Iterator()
	for it.Next() {
		str += fmt.Sprintf("%v:%v ", it.key(), it.Value()) // MODEL: gods: it.Key()
	}
	return strings.TrimRight(str, " ") + "]"

}

// MODEL: where the model does not model gods' treemap it blocks forever (`select {}`, after a comment `MODEL: not modelled (stuck): ...`), never a panic:
// a panic can be recovered (Go's recover, Perennial's with_defer_recover), so a value panic would add
// behaviors the library does not have; being stuck only removes behaviors (models/README.md).
