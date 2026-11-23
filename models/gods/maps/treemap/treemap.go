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
// (models/README.md, "The third-party library models"), the API the dsverify kits call (SwiftPaxos's `state`
// package, in the swiftpaxos and epaxos kits): NewWith, Put, Get, Select, Iterator and the
// iterator's Next and Value. The red-black tree (gods' trees/redblacktree) is replaced by a slice
// of the entries sorted by the comparator; every other exported name of the package is left out.
//
// The trusted claim: for a comparator that is a total preorder on the keys the program passes
// (a function: no effect, the same result for the same keys, no panic on two keys of the map's
// key type), every behavior of v1.18.1's treemap, as the program observes it through this API,
// is a behavior of the model:
//   - Put(k, v): if an entry's key compares equal to k, its key and value become k and v (the
//     tree's node takes both); otherwise a new entry, in order. On an empty map Put calls
//     comparator(k, k) as the tree does ("Assert key is of comparator's type"), so a key the
//     comparator rejects panics there too.
//   - Get(k): the value of the entry whose key compares equal to k, and true; else nil, false.
//   - Select(f): a new map, the same comparator, holding the entries for which f(key, value) is
//     true, f called once per entry in key order (the tree's in-order iterator).
//   - Iterator(): before the first entry; Next() moves to the next entry in key order and reports
//     whether there is one (false forever once past the last); Value() is the current entry's,
//     and panics when there is none (before the first Next, after the last).
//
// Not claimed: how many times and on which pairs the comparator is called (the tree walks a
// path, the model scans), and a map changed while an iterator over it is in use. Evidence:
// models/internal/tpdifftest (run.sh: random operation sequences against v1.18.1 and the model).
package treemap

import (
	"github.com/emirpasic/gods/utils"
)

// MODEL: an entry of the map (gods: a node of the red-black tree).
type entry struct {
	key   interface{}
	value interface{}
}

// Map holds the elements in a red-black tree
//
// MODEL: in a slice sorted by the comparator, with the comparator (gods: tree *rbt.Tree).
type Map struct {
	comparator utils.Comparator
	entries    []entry
}

// NewWith instantiates a tree map with the custom comparator.
func NewWith(comparator utils.Comparator) *Map {
	return &Map{comparator: comparator, entries: nil}
}

// MODEL: find returns the position of the first entry whose key is not less than key, and whether
// the two compare equal; it compares as the tree does, comparator(key, entry's key).
func (m *Map) find(key interface{}) (int, bool) {
	i := 0
	for i < len(m.entries) {
		c := m.comparator(key, m.entries[i].key)
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
	if len(m.entries) == 0 {
		// Assert key is of comparator's type for initial tree
		m.comparator(key, key)
		m.entries = append(m.entries, entry{key: key, value: value})
		return
	}
	i, found := m.find(key)
	if found {
		m.entries[i] = entry{key: key, value: value}
		return
	}
	m.entries = append(m.entries, entry{})
	copy(m.entries[i+1:], m.entries[i:])
	m.entries[i] = entry{key: key, value: value}
}

// Get searches the element in the map by key and returns its value or nil if key is not found in tree.
// Second return parameter is true if key was found, otherwise false.
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (m *Map) Get(key interface{}) (value interface{}, found bool) {
	// MODEL: rbt.Tree.Get, on the sorted slice.
	i, ok := m.find(key)
	if ok {
		return m.entries[i].value, true
	}
	return nil, false
}
