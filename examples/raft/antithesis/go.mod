module github.com/mit-pdos/etcd-grove/examples/raft/antithesis

go 1.27

// raft: the fork at the pin of etc/goose.py's project raft (RAFT_REV, as examples/go.mod's), in its
// main build (no build tags): the raft every theorem outside RaftTla/ is about.
replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261110053807-d2c16c558247

require (
	github.com/goose-lang/primitive v0.2.1
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.12
)
