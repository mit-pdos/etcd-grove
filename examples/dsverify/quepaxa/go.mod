// The QuePaxa kit (notes/dsv-quepaxa.md): dsverify-lab's quepaxa-bump-1 fork of QuePaxa
// (examples/quepaxa/fork/quepaxa at lab master 915f964, fork commit 77b5258), its kit ported onto
// examples/lib/remote. Module path the fork's (raxos).
module raxos

go 1.27

replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/go-redis/redis/v8 v8.11.5
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	google.golang.org/grpc v1.84.0
	google.golang.org/protobuf v1.36.12
	gopkg.in/yaml.v2 v2.4.0
)

require (
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/dgryski/go-rendezvous v0.0.0-20200823014737-9f7001d12a5f // indirect
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65 // indirect
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000 // indirect
	golang.org/x/net v0.57.0 // indirect
	golang.org/x/sys v0.47.0 // indirect
	golang.org/x/text v0.40.0 // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260706201446-f0a921348800 // indirect
)
