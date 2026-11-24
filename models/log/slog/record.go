// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package slog

// A Record holds information about a log event.
//
// MODEL: opaque (Go: the time, message, level, PC and attributes). Only a Handler's Handle takes
// one, and the model runs no handler but its own (DiscardHandler, the default handler), which do
// not look at it.
type Record struct {
	_ [0]func() // MODEL: not comparable, as Go's (which holds a slice)
}
