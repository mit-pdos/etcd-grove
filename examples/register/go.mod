module github.com/mit-pdos/etcd-grove/examples/register

go 1.25.0

replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd-raft/v3 v3.0.0-20260311205704-531b20c6251e

require go.etcd.io/raft/v3 v3.0.0-00010101000000-000000000000

require (
	github.com/gogo/protobuf v1.3.2 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	google.golang.org/protobuf v1.33.0 // indirect
)
