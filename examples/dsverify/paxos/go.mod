// The paxos kit (notes/dsv-paxos.md): dsverify-lab's paxos-net-3 fork of xiang90/paxos
// (examples/paxos/fork/paxos at lab master 7a84fb35), its kit ported onto examples/lib/remote.
// Translated into the part Dsverify/ (etc/goose.py, project dsv-paxos).
module github.com/xiang90/paxos

go 1.27

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	github.com/tchajed/marshal => github.com/upamanyus/marshal v0.0.0-20260212025754-cf86d74f6773
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	github.com/tchajed/marshal v0.6.2
)

require (
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65 // indirect
	github.com/goose-lang/std v0.6.1 // indirect
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
)
