// The rabia kit (notes/dsv-rabia.md): dsverify-lab's rabia-r1wake-1 fork of Rabia
// (examples/rabia/fork/rabia at lab master 915f964, fork ef2a93b), its kit ported onto
// examples/lib/remote. The lab replaced zerolog, gogo/protobuf and go-redis by its own models
// (harness/rpcmodel); here the real modules, at the fork's versions.
module rabia

go 1.27

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/go-redis/redis/v8 v8.8.2
	github.com/gogo/protobuf v1.3.2
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	github.com/rs/zerolog v1.23.0
)

require (
	github.com/cespare/xxhash/v2 v2.1.1 // indirect
	github.com/dgryski/go-rendezvous v0.0.0-20200823014737-9f7001d12a5f // indirect
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65 // indirect
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
	go.opentelemetry.io/otel v0.19.0 // indirect
	go.opentelemetry.io/otel/metric v0.19.0 // indirect
	go.opentelemetry.io/otel/trace v0.19.0 // indirect
)
