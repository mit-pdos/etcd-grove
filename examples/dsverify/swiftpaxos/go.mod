// The swiftpaxos kit (notes/dsv-swiftpaxos.md): dsverify-lab's swift-n2nofast-1 fork of
// imdea-software/swiftpaxos (examples/swiftpaxos/fork/swiftpaxos at lab master 915f964, fork
// commit 66dfc21), the system's packages only; the kit (examples/swiftnet) is not ported onto
// examples/lib/remote yet, and the lab's models of gods, uuid and concurrent-map are not used (the
// real modules). Not translated yet (no etc/goose.py project): see the notes for what blocks.
module github.com/imdea-software/swiftpaxos

go 1.27

require (
	github.com/emirpasic/gods v1.18.1
	github.com/google/uuid v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/orcaman/concurrent-map v1.0.0
)
