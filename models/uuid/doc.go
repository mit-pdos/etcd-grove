// Copyright 2016 Google Inc.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package uuid generates and inspects UUIDs.
//
// UUIDs are based on RFC 4122 and DCE 1.1: Authentication and Security
// Services.
//
// A UUID is a 16 byte (128 bit) array.  UUIDs may be used as keys to
// maps or compared directly.
//
// MODEL: this is the model of github.com/google/uuid v1.3.1 (models/README.md, "The
// third-party library models"), the API the dsverify kits call (SwiftPaxos's `client`, in the
// swiftpaxos kit: a client names itself with uuid.New().ID(), its request buffer keys with
// uuid.New().Time()): the UUID and Time types, New, NewRandom, Must, and UUID's ID and Time; and
// the methods Go's standard library reaches through an interface, with what they call: String
// (fmt.Stringer), MarshalText/UnmarshalText (encoding.TextMarshaler/Unmarshaler: encoding/json,
// encoding/xml, ...), MarshalBinary/UnmarshalBinary (encoding.BinaryMarshaler/Unmarshaler:
// encoding/gob), Value/Scan (database/sql's Valuer and Scanner), Parse and ParseBytes. All of these
// are v1.3.1's code but NewRandom; every other exported name is left out (versions 1, 2, 3, 5,
// the randomness pool, SetRand, NullUUID, node ids, URN, Variant, Version, MustParse, FromBytes).
//
// The trusted claim: every behavior of v1.3.1 through this API, as the program observes it, is a
// behavior of the model, provided
//   - the program never assigns crypto/rand.Reader (v1.3.1 reads from the reader it captures at
//     its initialization, `rander = rand.Reader`, and a program package initialized before it
//     could replace that reader by a failing one: NewRandom would return its error and New panic);
//   - the program is not built with boringcrypto (whose default reader panics on a failure);
//   - and the process's fatal error when the kernel's random source fails (crypto/rand's Read
//     since Go 1.24, the toolchain here being Go 1.27.3) is not a behavior the claim covers (a
//     machine crash, which the kits' statement does not model).
// The model's NewRandom is the only change (version4.go): v1.3.1 reads 16 bytes from
// crypto/rand.Reader (which under these premises cannot fail) and sets the version and variant
// bits; the model takes the 16 bytes from two primitive.RandomUint64() calls and sets the same
// bits with v1.3.1's code, and its error is nil. In Goose's semantics primitive.RandomUint64 is
// ArbitraryInt (Perennial's TrustedCode), so every 16 bytes with those bits set is a result of the
// model's NewRandom: the coverage of v1.3.1's results is structural. Nothing models uniqueness (two
// UUIDs may be equal) or the distribution of the bytes.
//
// Evidence: models/internal/tpdifftest (run.sh: ID, Time, String, the text, binary, JSON, gob and
// SQL methods and Parse against v1.3.1 on random, edge and malformed inputs; the version and
// variant bits of New's UUIDs in both builds, an illustration of the structural argument; a
// replaced crypto/rand.Reader, outside the claim, shown to make v1.3.1 fail).
package uuid
