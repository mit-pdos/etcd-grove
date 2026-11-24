// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package slog provides structured logging.
//
// MODEL: this is the model of Go 1.27.3's log/slog (models/README.md, "The log/slog model"), the
// API the dsverify kits call (go-vsr in the vr kit: its replicas and clients log through
// slog.New(slog.DiscardHandler), its TCP network through the package-level slog.Debug): Level, its
// four constants and its methods (Go's code: String, MarshalJSON, UnmarshalJSON, AppendText,
// MarshalText, UnmarshalText, Level), Handler, Record and Attr (opaque), DiscardHandler, Logger,
// New, Logger.{Debug,Info,Warn,Error,Handler}, and Debug. Every other exported name is left out.
//
// The trusted claim: **logging has no effect the program observes.** For every program that uses
// this API, every behavior of Go 1.27.3's log/slog, as the program observes it, is a behavior of
// the model: the calls return (no results), a nil *Logger's methods and a zero Logger's level
// methods panic (a nil dereference, in both), New(nil) panics with "nil Handler", Handler returns
// the Logger's handler (Go's code: DiscardHandler, or nil for a zero Logger), Level's methods are
// Go's, and no record is ever enabled through the model's API, so nothing reaches a handler's
// output:
//   - a Logger's handler is DiscardHandler (New refuses any other, below), whose Enabled is false at
//     every level (Go's code), so a call returns at once, its arguments untouched;
//   - the package-level Debug goes to the default handler, enabled from the log package's level,
//     LevelInfo unless SetLogLoggerLevel changes it (not in the model), so Debug returns at once.
//     (SetDefault, Default and the other package-level functions are not in the model, so the
//     default handler is never reached otherwise, and log.SetOutput or log.SetFlags change nothing
//     the program observes through this API.)
// Provided the program does not make Record or Attr values of its own (the model's are opaque; a
// zero Record or Attr would print differently) and does not observe the representation
// (reflection, unsafe).
//
// Outside the model, a call is stuck (handler.go's stuck: no behavior; models/README.md, "Not
// modelled: stuck"): a Handler the program
// supplies to New (any but DiscardHandler: its methods run program code, with records the model
// does not build).
//
// Not claimed: the time the calls take.
//
// Evidence: models/internal/slogdifftest (run.sh: the same tests against Go's log/slog and the
// model, an overlay: returns, panic or not and the panic values where Go's are not runtime errors,
// a nil and a zero Logger, Handler's result, Level's formatting and parsing; that no argument
// method is called; that nothing reaches stdout or stderr).
package slog
