// The swiftpaxos kit (notes/dsv-swiftpaxos.md): dsverify-lab's swift-n2nofast-1 fork of
// imdea-software/swiftpaxos (examples/swiftpaxos/fork/swiftpaxos at lab master 915f964, fork
// commit 66dfc21), the system's packages only; the kit (examples/swiftnet) is not ported onto
// examples/lib/remote yet, and the lab's models of gods, uuid and concurrent-map are not used (the
// real modules). Not translated yet (no etc/goose.py project): see the notes for what blocks.
module github.com/imdea-software/swiftpaxos

go 1.27

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/emirpasic/gods v1.18.1
	github.com/google/uuid v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-20261123015333-2dce8dc601a1
	github.com/orcaman/concurrent-map v1.0.0
	models.lab v0.0.0-00010101000000-000000000000
)

require github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	models.lab => ../../../models
)
