// The craq kit (notes/dsv-craq.md): dsverify-lab's craq-bump-1 fork of despreston/go-craq
// (examples/craq/fork/go-craq at lab master 915f964, fork commit a0238ac), its kit ported onto
// examples/lib/remote. Translated into the part Dsverify/ (etc/goose.py, project dsv-craq).
module github.com/despreston/go-craq

go 1.27

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	models.lab => ../../../models
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/google/go-cmp v0.7.0
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	models.lab v0.0.0-00010101000000-000000000000
)

require github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
