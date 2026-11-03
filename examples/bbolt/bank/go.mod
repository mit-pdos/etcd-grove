module github.com/mit-pdos/etcd-grove/examples/bbolt/bank

go 1.26

// bbolt: the fork at project bbolttest's pin in etc/goose.py (GO_MOD_PINS checks the two agree).
replace go.etcd.io/bbolt => github.com/upamanyus/bbolt v0.0.0-20261102202309-3207bacf270d

// The driver and the vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated.
replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000
	go.etcd.io/bbolt v1.5.0
)

require golang.org/x/sys v0.45.0 // indirect
