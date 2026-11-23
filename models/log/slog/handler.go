// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package slog

import (
	"context"
)

// MODEL: of Go's handler.go the Handler interface, DiscardHandler (Go's code), and the default
// handler reduced to its level check (Go's defaultHandler formats a record and writes it to the
// log package's output: dropped). The handler options, the text and JSON handlers' common code,
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
// SetLogLoggerLevel, not in the model). Handle drops the record (Go: formats it and writes it to
// log's output, os.Stderr, which the program does not read). WithAttrs and WithGroup are not
// reachable through the model's API.
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

// MODEL: the models' panic value: what the model does not model (a program-supplied Handler, the
// use of Logger.Handler's result).
type notModelled struct{ what string }

func (e notModelled) Error() string { return "log/slog model: not modelled: " + e.what }

// NotModelled marks the value as the models' panic.
func (notModelled) NotModelled() {}

// MODEL: the handler Logger.Handler returns: every method panics with notModelled.
type notModelledHandler struct{}

func (notModelledHandler) Enabled(context.Context, Level) bool {
	panic(notModelled{"the use of Logger.Handler's result"})
}
func (notModelledHandler) Handle(context.Context, Record) error {
	panic(notModelled{"the use of Logger.Handler's result"})
}
func (notModelledHandler) WithAttrs([]Attr) Handler {
	panic(notModelled{"the use of Logger.Handler's result"})
}
func (notModelledHandler) WithGroup(string) Handler {
	panic(notModelled{"the use of Logger.Handler's result"})
}
