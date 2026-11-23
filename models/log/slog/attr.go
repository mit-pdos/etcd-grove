// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package slog

// An Attr is a key-value pair.
//
// MODEL: opaque (Go: Key and Value). Only a Handler's WithAttrs takes them, and the model's
// handlers do not look at them.
type Attr struct {
	_ [0]func()
}
