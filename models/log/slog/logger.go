// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package slog

import (
	"context"
)

// MODEL: of Go's logger.go the Logger, New, Handler, the four level methods and their log, and the
// package-level Debug over the default Logger. Go's Logger.log builds a Record (the time, the
// caller's PC, the arguments as attributes) and passes it to the handler once Enabled is true; the
// model's handlers do not look at records, so the model passes an empty one. The default Logger is
// a variable the model never changes (Go: an atomic pointer, changed by SetDefault, not in the
// model). Left out: With, WithGroup, Enabled, Log, LogAttrs, the Context variants, Default,
// SetDefault, SetLogLoggerLevel, NewLogLogger, the other package-level functions.

// MODEL: Go: defaultLogger atomic.Pointer[Logger], set by init to New(newDefaultHandler(...)).
var defaultLogger = &Logger{handler: defaultHandler{}}

// A Logger records structured information about each call to its
// Log, Debug, Info, Warn, and Error methods.
// For each call, it creates a [Record] and passes it to a [Handler].
//
// To create a new Logger, call [New] or a Logger method
// that begins "With".
type Logger struct {
	handler Handler // for structured logging
}

// Handler returns l's Handler.
//
// MODEL: a handler whose every method panics with a NotModelled value (Go: l's handler). It reads
// l's handler first, so that on a nil l it panics as Go's does.
func (l *Logger) Handler() Handler {
	_ = l.handler
	return notModelledHandler{}
}

// New creates a new Logger with the given non-nil Handler.
//
// MODEL: a handler other than DiscardHandler panics with a NotModelled value (after Go's nil check).
func New(h Handler) *Logger {
	if h == nil {
		panic("nil Handler")
	}
	if _, ok := h.(discardHandler); !ok {
		panic(notModelled{"a Handler other than DiscardHandler"})
	}
	return &Logger{handler: h}
}

// Debug logs at [LevelDebug].
func (l *Logger) Debug(msg string, args ...any) {
	l.log(context.Background(), LevelDebug, msg, args...)
}

// Info logs at [LevelInfo].
func (l *Logger) Info(msg string, args ...any) {
	l.log(context.Background(), LevelInfo, msg, args...)
}

// Warn logs at [LevelWarn].
func (l *Logger) Warn(msg string, args ...any) {
	l.log(context.Background(), LevelWarn, msg, args...)
}

// Error logs at [LevelError].
func (l *Logger) Error(msg string, args ...any) {
	l.log(context.Background(), LevelError, msg, args...)
}

// log is the low-level logging method for methods that take ...any.
// It must always be called directly by an exported logging method
// or function, because it uses a fixed call depth to obtain the pc.
//
// MODEL: Go's check (Enabled: l's handler's), then the handler's Handle with an empty Record
// (Go: NewRecord(time.Now(), level, msg, pc) with the arguments added).
func (l *Logger) log(ctx context.Context, level Level, msg string, args ...any) {
	if !l.handler.Enabled(ctx, level) {
		return
	}
	_ = l.handler.Handle(ctx, Record{})
}

// Debug calls [Logger.Debug] on the default logger.
func Debug(msg string, args ...any) {
	defaultLogger.log(context.Background(), LevelDebug, msg, args...)
}
