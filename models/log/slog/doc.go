// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package slog provides structured logging.
//
// MODEL: this is the model of Go 1.27.3's log/slog (models/README.md, "The log/slog model"), the
// API the dsverify kits call (go-vsr in the vr kit: its replicas and clients log through
// slog.New(slog.DiscardHandler), its TCP network through the package-level slog.Debug): Level and
// its four constants, Handler, Record and Attr (opaque), DiscardHandler, Logger, New,
// Logger.{Debug,Info,Warn,Error,Handler}, and Debug. Every other exported name is left out.
//
// The trusted claim: **logging has no effect the program observes.** For every program that uses
// this API, every behavior of Go 1.27.3's log/slog, as the program observes it, is a behavior of
// the model: the calls return (no results), a nil *Logger's methods panic (a nil dereference, in
// both), New(nil) panics with "nil Handler", and no record reaches anything the program can read.
// The claim holds only for the handlers whose output the program cannot read, the two this API
// can name:
//   - DiscardHandler: Enabled is false at every level, so a Logger over it returns at once, its
//     arguments untouched (Go's code, unchanged).
//   - the default handler, behind the package-level Debug: it is enabled from the log package's
//     level, LevelInfo unless SetLogLoggerLevel changes it (not in the model), so Debug returns at
//     once; were a record handled, it would go to the log package's output, os.Stderr unless
//     log.SetOutput changes it, which the program does not read. The model's default handler drops
//     the record (MODEL); a program that calls log.SetOutput, log.SetFlags or
//     slog.SetLogLoggerLevel is outside the claim.
//
// Outside the model, a panic with a value that has a NotModelled method: a Handler the program
// supplies to New (any but DiscardHandler: its methods run program code, with records the model
// does not build), and the use of Logger.Handler's result (the model's Handler returns a handler
// whose every method panics so; Go's returns the Logger's handler).
//
// Not claimed: the time the calls take, and, for a record the default handler would write,
// effects of the arguments' methods (String, Error, MarshalText, LogValue) that slog calls to
// format it (none for Debug at the default level).
//
// Evidence: models/internal/slogdifftest (run.sh: the same tests against Go's log/slog and the
// model, an overlay; return, panic or not, and the panic values where Go's are not runtime
// errors; that no argument method is called; that nothing reaches stderr).
package slog
