module github.com/mit-pdos/etcd-grove/examples/raft/tracecheck

go 1.27

// raft: the fork at the pin of etc/goose.py's project raft (as examples/go.mod's), in its `with_tla`
// build: Goose loads this module with `-tags with_tla` (etc/goose.py, RAFT_TAGS), and the Go tests
// run with `-tags with_tla`.
replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261110053807-d2c16c558247

// The vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated.
replace github.com/anishathalye/porcupine => ../../../third_party/porcupine

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.1
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.12
)
