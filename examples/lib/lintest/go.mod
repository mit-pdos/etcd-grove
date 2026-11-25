module github.com/mit-pdos/etcd-grove/examples/lib/lintest

go 1.26

require github.com/anishathalye/porcupine v1.3.1

require github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65

// The vendored copy translated by etc/goose.py (third_party/porcupine/UPSTREAM.md).
replace github.com/anishathalye/porcupine => ../../../third_party/porcupine
