// Copyright 2016 Google Inc.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package uuid

import (
	"encoding/binary"
)

// MODEL: of v1.3.1's time.go only the Time type and UUID's Time method (no program here makes
// version 1 UUIDs or reads the clock through the package: GetTime, ClockSequence, SetClockSequence,
// Time's UnixTime, the clock's state).

// A Time represents a time as the number of 100's of nanoseconds since 15 Oct
// 1582.
type Time int64

// Time returns the time in 100s of nanoseconds since 15 Oct 1582 encoded in
// uuid.  The time is only defined for version 1 and 2 UUIDs.
func (uuid UUID) Time() Time {
	time := int64(binary.BigEndian.Uint32(uuid[0:4]))
	time |= int64(binary.BigEndian.Uint16(uuid[4:6])) << 32
	time |= int64(binary.BigEndian.Uint16(uuid[6:8])&0xfff) << 48
	return Time(time)
}
