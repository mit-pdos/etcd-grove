module github.com/mit-pdos/etcd-grove/examples/register

go 1.26

require go.etcd.io/raft/v3 v3.6.0-beta.0.0.20260415131831-40f8be730b18

require (
	github.com/gogo/protobuf v1.3.2 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	google.golang.org/protobuf v1.33.0 // indirect
)

replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261014191125-0560cb75ad8e
