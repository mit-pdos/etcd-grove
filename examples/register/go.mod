module github.com/mit-pdos/etcd-grove/examples/register

go 1.26

require (
	go.etcd.io/raft/v3 v3.7.0
	google.golang.org/protobuf v1.36.11
)

replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261019023206-c8217eb91ae5
