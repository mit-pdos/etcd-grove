module github.com/mit-pdos/etcd-grove/examples/lib/remote

go 1.27

// lintest (the driver: lintest.RunC) and the vendored porcupine (third_party/porcupine/UPSTREAM.md),
// as translated.
replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../lintest
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000
)
