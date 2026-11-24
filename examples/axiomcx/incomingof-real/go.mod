module github.com/mit-pdos/etcd-grove/examples/axiomcx/incomingofreal

go 1.27

// etcd: the fork at etc/goose.py's etcd pin, as examples/go.mod replaces it.
replace (
	go.etcd.io/etcd/api/v3 => github.com/upamanyus/etcd/api/v3 v3.0.0-20261124035548-c81d630374d5
	go.etcd.io/etcd/client/pkg/v3 => github.com/upamanyus/etcd/client/pkg/v3 v3.0.0-20261124035548-c81d630374d5
	go.etcd.io/etcd/client/v3 => github.com/upamanyus/etcd/client/v3 v3.0.0-20261124035548-c81d630374d5
)

require (
	go.etcd.io/etcd/api/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/client/v3 v3.0.0-00010101000000-000000000000
	google.golang.org/grpc v1.84.0
)

require (
	github.com/Masterminds/semver/v3 v3.5.0 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	github.com/grpc-ecosystem/grpc-gateway/v2 v2.31.0 // indirect
	go.etcd.io/etcd/client/pkg/v3 v3.8.0-alpha.0 // indirect
	go.uber.org/multierr v1.11.0 // indirect
	go.uber.org/zap v1.28.0 // indirect
	golang.org/x/net v0.60.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
	golang.org/x/text v0.42.0 // indirect
	google.golang.org/genproto/googleapis/api v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/protobuf v1.36.12 // indirect
)
