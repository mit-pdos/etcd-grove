// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package treemap

// MODEL: only the methods encoding/json reaches through its interfaces (json.Marshaler,
// json.Unmarshaler), each blocking forever, not modelled (gods: through the tree's ToJSON and
// FromJSON, utils.ToString and encoding/json of a map[string]interface{}); ToJSON and FromJSON, which
// no interface of Go's reaches, are left out, and so are the assertions of containers' interfaces.

// UnmarshalJSON @implements json.Unmarshaler
func (m *Map) UnmarshalJSON(bytes []byte) error {
	select {} // MODEL: not modelled (stuck): UnmarshalJSON
}

// MarshalJSON @implements json.Marshaler
func (m *Map) MarshalJSON() ([]byte, error) {
	select {} // MODEL: not modelled (stuck): MarshalJSON
}
