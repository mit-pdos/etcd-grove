// Copyright 2016 Google Inc.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package uuid

import (
	"encoding/binary"
)

// MODEL: of v1.3.1's dce.go only ID (no program here makes or inspects DCE Security UUIDs
// otherwise: the Domain type, NewDCESecurity, NewDCEPerson, NewDCEGroup, Domain).

// ID returns the id for a Version 2 UUID. IDs are only defined for Version 2
// UUIDs.
func (uuid UUID) ID() uint32 {
	return binary.BigEndian.Uint32(uuid[0:4])
}
