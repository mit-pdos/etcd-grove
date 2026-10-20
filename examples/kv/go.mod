module github.com/mit-pdos/etcd-grove/examples/kv

go 1.26

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lintest v0.0.0-00010101000000-000000000000
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.11
)

replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261020021956-9ed005d46117

// The driver and the vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated.
replace (
	github.com/anishathalye/porcupine => ../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lintest => ../lintest
)
