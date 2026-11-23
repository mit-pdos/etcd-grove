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
// third-party library models"), the API the dsverify kits call (SwiftPaxos's `client`, in the swiftpaxos kit: a client
// names itself with uuid.New().ID(), its request buffer keys with uuid.New().Time()): the UUID and
// Time types, New, NewRandom, Must, and UUID's ID and Time. ID, Time and Must are v1.3.1's code;
// New is v1.3.1's code over the model's NewRandom; every other exported name is left out
// (parsing, formatting, versions 1, 2, 3, 5, the randomness pool, SetRand, SQL, JSON, node ids).
//
// The trusted claim: every behavior of v1.3.1's New and NewRandom (the default configuration: the
// reader crypto/rand.Reader, no pool) as the program observes it is a behavior of the model's,
// and ID and Time return what v1.3.1's return on the same UUID. The model's NewRandom is the only
// change (version4.go): v1.3.1 reads 16 bytes from crypto/rand.Reader and sets the version and
// variant bits; the model takes the 16 bytes from two primitive.RandomUint64() calls (random in
// Go, any uint64 in Goose's semantics) and sets the same bits. So each UUID is any 16 bytes with
// the version-4 and variant bits set, as in v1.3.1; nothing models uniqueness (two UUIDs may be
// equal). v1.3.1's NewRandom returns an error when the reader fails: crypto/rand.Reader's Read
// never returns one since Go 1.24 (the toolchain here is Go 1.27.3; a failure of the kernel's
// source is a fatal error of the process, crypto/rand's doc), so the model's error is always nil
// and New never panics. Not claimed: that fatal error of the process (a machine crash, which the
// kits' statement does not model), and anything about the distribution of the bytes.
//
// Evidence: models/internal/tpdifftest (run.sh: ID and Time against v1.3.1 on random and edge
// UUIDs; the version and variant bits and the variability of every other bit of New's UUIDs in
// both builds).
package uuid
