module github.com/mit-pdos/etcd-grove/examples/raft/kvdurablenoax

go 1.27

// raft: the fork's branch raft37-goose-lean-noax (notes/raft-noax.md), project raft's revision
// with the axiomatized code replaced by hand-written Go.
replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261117222007-91e2ea70f483

// The driver and the vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated, and
// the examples' module, for the durable package (examples/lib/durable).
replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples => ../..
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/gokv v0.1.1
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.12
)
