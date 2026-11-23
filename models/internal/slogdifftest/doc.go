// Package slogdifftest holds the differential tests of the log/slog model (models/log/slog;
// models/README.md): run.sh runs them against Go 1.27.3's log/slog and against the model (an
// overlay of the toolchain's source, models/goroot.py; tag netmodel) and compares the two builds'
// transcripts.
package slogdifftest
