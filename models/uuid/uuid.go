// Copyright 2018 Google Inc.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package uuid

// MODEL: of v1.3.1's uuid.go only the UUID type and Must (no program here calls the rest: Parse,
// ParseBytes, MustParse, FromBytes, String, URN, Variant, Version, the randomness pool, SetRand,
// the invalid length error, the Version and Variant types and constants).

// A UUID is a 128 bit (16 byte) Universal Unique IDentifier as defined in RFC
// 4122.
type UUID [16]byte

// Must returns uuid if err is nil and panics otherwise.
func Must(uuid UUID, err error) UUID {
	if err != nil {
		panic(err)
	}
	return uuid
}
