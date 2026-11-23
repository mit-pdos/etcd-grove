// The EPaxos kit (notes/dsv-epaxos.md): dsverify-lab's epaxos-e1nogs-1 fork of
// imdea-software/swiftpaxos (fork commit 71d99d4, the lab's final verified run of EPaxos), the
// packages the kit runs (rpc, dlog, config, state, replica/defs, replica, epaxos, master), its kit
// ported onto examples/lib/remote (examples/epaxosnet). The module path is the fork's with
// "-epaxos" added, so that its translation (the part Dsverify/) does not share module names with
// the swiftpaxos kit's fork of the same repository (examples/dsverify/swiftpaxos). gods is the real
// module (the lab replaced it by a cut-down copy). Translated into the part Dsverify/
// (etc/goose.py, project dsv-epaxos).
module github.com/imdea-software/swiftpaxos-epaxos

go 1.27

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	models.lab => ../../../models
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/emirpasic/gods v1.18.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
)

require github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
