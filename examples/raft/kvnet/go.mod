module github.com/mit-pdos/etcd-grove/examples/raft/kvnet

go 1.27

// raft: the fork's branch raft37-goose-lean-noax (notes/raft-noax-part.md), as
// examples/raft/kvdurablenoax: the axiom-free raft kvnet's top-level theorem rests on
// (notes/kvnet-proof-plan.md, decision D).
replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261121172512-e98d795867e6

// The driver and the vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated, and
// the examples' module, for the durable package (examples/lib/durable) and the robustness harness
// (examples/lib/robust).
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
