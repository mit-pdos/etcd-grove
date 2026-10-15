module github.com/mit-pdos/etcd-grove/examples/lintest

go 1.26

require github.com/anishathalye/porcupine v1.3.1

// The vendored copy translated by etc/goose.py (third_party/porcupine/UPSTREAM.md).
replace github.com/anishathalye/porcupine => ../../third_party/porcupine
