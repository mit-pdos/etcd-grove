// The vr kit (notes/dsv-vr.md): dsverify-lab's vsr-bump-1 fork of tangledbytes/go-vsr
// (examples/vr/fork/go-vsr at lab master 915f964, fork commit 9c4be18), its kit ported onto
// examples/lib/remote. Translated into the part Dsverify/ (etc/goose.py, project dsv-vr: not yet,
// notes/dsv-vr.md, "State").
module github.com/tangledbytes/go-vsr

go 1.27

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	models.lab => ../../../models
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
)

require (
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
	models.lab v0.0.0-00010101000000-000000000000
)
