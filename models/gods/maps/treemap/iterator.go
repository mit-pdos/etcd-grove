// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package treemap

// MODEL: only Iterator, Next and Value (no program here calls Prev, Key, Begin, End, First, Last,
// NextTo, PrevTo; Select uses the unexported key), and no assertion of
// containers.ReverseIteratorWithKey.

// Iterator holding the iterator's state
//
// MODEL: the map and the position in its sorted entries, -1 before the first (gods: an
// rbt.Iterator, a node and a position begin/between/end).
type Iterator struct {
	m     *Map
	index int
}

// Iterator returns a stateful iterator whose elements are key/value pairs.
func (m *Map) Iterator() Iterator {
	return Iterator{m: m, index: -1}
}

// Next moves the iterator to the next element and returns true if there was a next element in the container.
// If Next() returns true, then next element's key and value can be retrieved by Key() and Value().
// If Next() was called for the first time, then it will point the iterator to the first element if it exists.
// Modifies the state of the iterator.
func (iterator *Iterator) Next() bool {
	// MODEL: the next position in the slice, staying one past the last (gods' `end`).
	if iterator.index < len(iterator.m.entries) {
		iterator.index++
	}
	return iterator.index < len(iterator.m.entries)
}

// Value returns the current element's value.
// Does not modify the state of the iterator.
func (iterator *Iterator) Value() interface{} {
	return iterator.m.entries[iterator.index].value // MODEL: gods: iterator.iterator.Value()
}

// MODEL: key is gods' Key (the current element's key), unexported: only Select calls it.
func (iterator *Iterator) key() interface{} {
	return iterator.m.entries[iterator.index].key
}
