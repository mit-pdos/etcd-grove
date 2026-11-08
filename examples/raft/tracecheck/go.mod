module github.com/mit-pdos/etcd-grove/examples/raft/tracecheck

go 1.27

// raft: the fork with the trace hooks under the goose tag (etc/fork-patches/raft-trace-tags.patch),
// so that Goose (which builds with -tags goose) sees the with_tla build. A local checkout until the
// commit is pushed (etc/fork-patches/README.md); then the fork's pseudo-version, at raft's pin.
replace go.etcd.io/raft/v3 => ../../../.lake/raft-trace

// The vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated.
replace github.com/anishathalye/porcupine => ../../../third_party/porcupine

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.1
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.12
)
