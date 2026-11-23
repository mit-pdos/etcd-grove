// Copyright 2016 Google Inc.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package uuid

import (
	"encoding/binary"

	"github.com/goose-lang/primitive"
)

// New creates a new random UUID or panics.  New is equivalent to
// the expression
//
//    uuid.Must(uuid.NewRandom())
func New() UUID {
	return Must(NewRandom())
}

// NewRandom returns a Random (Version 4) UUID.
//
// The strength of the UUIDs is based on the strength of the crypto/rand
// package.
//
// Uses the randomness pool if it was enabled with EnableRandPool.
//
// A note about uniqueness derived from the UUID Wikipedia entry:
//
//  Randomly generated UUIDs have 122 random bits.  One's annual risk of being
//  hit by a meteorite is estimated to be one chance in 17 billion, that
//  means the probability is about 0.00000000006 (6 × 10−11),
//  equivalent to the odds of creating a few tens of trillions of UUIDs in a
//  year and having one duplicate.
//
// MODEL: v1.3.1 is NewRandomFromReader(rander) (rander = crypto/rand.Reader; the pool is never
// enabled: the model has no EnableRandPool): io.ReadFull of 16 bytes, which cannot fail (Go >=
// 1.24's crypto/rand.Reader), then the version and variant bits. The model's 16 bytes are two
// primitive.RandomUint64(), big-endian; the bits are set by v1.3.1's code; the error is nil.
func NewRandom() (UUID, error) {
	var uuid UUID
	binary.BigEndian.PutUint64(uuid[0:8], primitive.RandomUint64())
	binary.BigEndian.PutUint64(uuid[8:16], primitive.RandomUint64())
	uuid[6] = (uuid[6] & 0x0f) | 0x40 // Version 4
	uuid[8] = (uuid[8] & 0x3f) | 0x80 // Variant is 10
	return uuid, nil
}
