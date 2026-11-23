//go:build !netmodel

package slogdifftest

// model: whether the tests run against the model (go test -overlay, models/goroot.py; tag
// netmodel) or against Go's log/slog.
const model = false
