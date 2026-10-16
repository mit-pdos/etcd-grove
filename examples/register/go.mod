module github.com/mit-pdos/etcd-grove/examples/register

go 1.26

require (
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.11
)

replace go.etcd.io/raft/v3 => /root/etcd-pr/raft-239
