// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package treemap

// MODEL: only Select (no program here calls Each, Map, Any, All, Find), and no assertion of
// containers.EnumerableWithKey (the model has neither the containers package nor the rest of the
// interface).

// Select returns a new container containing all elements for which the given function returns a true value.
func (m *Map) Select(f func(key interface{}, value interface{}) bool) *Map {
	newMap := NewWith(m.state.comparator) // MODEL: gods: &Map{tree: rbt.NewWith(m.tree.Comparator)}
	iterator := m.Iterator()
	for iterator.Next() {
		if f(iterator.key(), iterator.Value()) {
			newMap.Put(iterator.key(), iterator.Value())
		}
	}
	return newMap
}
