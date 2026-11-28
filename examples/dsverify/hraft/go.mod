// hashicorp/raft (notes/dsv-hraft.md): dsverify-lab's verification fork of hashicorp/raft v1.8.0
// (examples/hraft/fork/raft at lab c39f136, fork commit 02f88d5 on v1.8.0 0f543c0), without the
// lab's in-process harness, and its kit examples/hraftnet (notes/dsv-hraft.md). Translated into the part Dsverify/ (etc/goose.py, project dsv-hraft).
module github.com/hashicorp/raft

go 1.27

retract v1.1.3 // Deleted original tag; module checksum may not be accurate.

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples => ../..
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	models.lab => ../../../models
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	models.lab v0.0.0-00010101000000-000000000000
)

require github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
