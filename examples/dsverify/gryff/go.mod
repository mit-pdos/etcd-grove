// The gryff kit (notes/dsv-gryff.md): dsverify-lab's gryff-bump-1 fork of Gryff
// (examples/gryff/fork/gryff at lab master 915f964, fork commit ef17c2d), its kit ported onto
// examples/lib/remote. Translated into the part Dsverify/ (etc/goose.py, project dsv-gryff).
module gryff

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
