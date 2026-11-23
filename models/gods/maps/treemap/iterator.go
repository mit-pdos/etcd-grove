// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package treemap

// MODEL: only Iterator, Next and Value (no program here calls Prev, Key, Begin, End, First, Last,
// NextTo, PrevTo; Select and String use the unexported key), and no assertion of
// containers.ReverseIteratorWithKey.

// Iterator holding the iterator's state
//
// MODEL: the map's state, the position in its sorted entries (-1 before the first), and the
// state's change count when the iterator was made (gods: an rbt.Iterator, the tree, a node and a
// position begin/between/end).
type Iterator struct {
	state   *sorted
	index   int
	changes uint64
}

// Iterator returns a stateful iterator whose elements are key/value pairs.
//
// MODEL: reads m (a nil m panics, as gods' m.tree), not m's state (a zero Map's iterator is made,
// as gods'; its Next panics).
func (m *Map) Iterator() Iterator {
	s := m.state
	var changes uint64
	if s != nil {
		changes = s.changes
	}
	return Iterator{state: s, index: -1, changes: changes}
}

// MODEL: check blocks forever (not modelled) if the map changed since the iterator was made
// (after a nil dereference if the iterator has no state, as gods' Next on a zero Map).
func (iterator *Iterator) check() {
	if iterator.state.changes != iterator.changes {
		select {} // MODEL: not modelled (stuck): a change to a map while an iterator over it is in use
	}
}

// Next moves the iterator to the next element and returns true if there was a next element in the container.
// If Next() returns true, then next element's key and value can be retrieved by Key() and Value().
// If Next() was called for the first time, then it will point the iterator to the first element if it exists.
// Modifies the state of the iterator.
func (iterator *Iterator) Next() bool {
	// MODEL: the next position in the slice, staying one past the last (gods' `end`).
	iterator.check()
	if iterator.index < len(iterator.state.entries) {
		iterator.index++
	}
	return iterator.index < len(iterator.state.entries)
}

// MODEL: current is the current entry; with none (before the first Next, past the last), a nil
// dereference, as gods' iterator.node.Value on its nil node.
func (iterator *Iterator) current() *entry {
	iterator.check()
	if iterator.index < 0 || iterator.index >= len(iterator.state.entries) {
		var none *entry
		return none
	}
	return &iterator.state.entries[iterator.index]
}

// Value returns the current element's value.
// Does not modify the state of the iterator.
func (iterator *Iterator) Value() interface{} {
	return iterator.current().value // MODEL: gods: iterator.iterator.Value()
}

// MODEL: key is gods' Key (the current element's key), unexported: only Select and String call it.
func (iterator *Iterator) key() interface{} {
	return iterator.current().key
}
