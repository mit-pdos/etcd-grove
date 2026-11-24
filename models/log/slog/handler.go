// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package slog

import (
	"context"
)

// MODEL: of Go's handler.go the Handler interface, DiscardHandler (Go's code), and the default
// handler reduced to its level check (Go's defaultHandler formats a record and writes it to the
// log package's output; the model's API never enables a record for it, so it never does). The handler options, the text and JSON handlers' common code,
// and the other handlers are left out.

// A Handler handles log records produced by a Logger.
//
// A typical handler may print log records to standard error,
// or write them to a file or database, or perhaps augment them
// with additional attributes and pass them on to another handler.
//
// Any of the Handler's methods may be called concurrently with itself
// or with other methods. It is the responsibility of the Handler to
// manage this concurrency.
//
// Users of the slog package should not invoke Handler methods directly.
// They should use the methods of [Logger] instead.
//
// Before implementing your own handler, consult https://go.dev/s/slog-handler-guide.
type Handler interface {
	// Enabled reports whether the handler handles records at the given level.
	Enabled(context.Context, Level) bool

	// Handle handles the Record.
	Handle(context.Context, Record) error

	// WithAttrs returns a new Handler whose attributes consist of
	// both the receiver's attributes and the arguments.
	WithAttrs(attrs []Attr) Handler

	// WithGroup returns a new Handler with the given group appended to
	// the receiver's existing groups.
	WithGroup(name string) Handler
}

// MODEL: the default handler (Go: defaultHandler, over the log package's output). Enabled is Go's
// check against the log package's level, which is LevelInfo (Go: logLoggerLevel, changed only by
// SetLogLoggerLevel, not in the model). Handle, WithAttrs and WithGroup are not reachable through
// the model's API: only the package-level Debug uses the default handler (Go: Default(), not in
// the model), and Debug is below LevelInfo.
type defaultHandler struct{}

func (defaultHandler) Enabled(_ context.Context, l Level) bool { return l >= LevelInfo }
func (defaultHandler) Handle(context.Context, Record) error    { return nil }
func (h defaultHandler) WithAttrs([]Attr) Handler              { return h }
func (h defaultHandler) WithGroup(string) Handler              { return h }

// DiscardHandler discards all log output.
// DiscardHandler.Enabled returns false for all Levels.
var DiscardHandler Handler = discardHandler{}

type discardHandler struct{}

func (dh discardHandler) Enabled(context.Context, Level) bool  { return false }
func (dh discardHandler) Handle(context.Context, Record) error { return nil }
func (dh discardHandler) WithAttrs(attrs []Attr) Handler       { return dh }
func (dh discardHandler) WithGroup(name string) Handler        { return dh }

// stuck is the model's not-modelled point (MODEL: not in Go's log/slog; models/README.md, "Not modelled:
// stuck"): where the model does not model Go's log/slog's behavior it calls stuck (after a comment
// `MODEL: not modelled (stuck): ...`), which has no behavior. Its Lean model is Perennial's
// internal/gomodel.Stuck, `Panic "not modelled"`: a stuck panic, which no recover catches and no
// WP rule steps, so a proof of the program shows that it never gets here. Not a value panic, which
// a program could recover and so observe a behavior Go's log/slog does not have; not a bare `select {}`,
// whose WP has the precondition True and so would prove anything after it. Its Go body blocks
// forever, which the tests detect (models/internal/stuck).
func stuck() {
	select {}
}
