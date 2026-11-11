module github.com/mit-pdos/etcd-grove/examples/sweeprepairs/tracer

go 1.27.1

replace go.etcd.io/etcd/pkg/v3 => github.com/upamanyus/etcd/pkg/v3 v3.0.0-20261107170612-a4d2bb1720b9

replace go.etcd.io/etcd/client/pkg/v3 => github.com/upamanyus/etcd/client/pkg/v3 v3.0.0-20261107170612-a4d2bb1720b9

require (
	go.etcd.io/etcd/pkg/v3 v3.8.0-alpha.0
	go.opentelemetry.io/otel/sdk v1.47.0
	go.opentelemetry.io/otel/trace v1.47.0
)

require (
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/go-logr/logr v1.4.4 // indirect
	github.com/go-logr/stdr v1.2.2 // indirect
	github.com/google/uuid v1.6.0 // indirect
	go.opentelemetry.io/auto/sdk v1.2.1 // indirect
	go.opentelemetry.io/otel v1.47.0 // indirect
	go.opentelemetry.io/otel/log v1.47.0 // indirect
	go.opentelemetry.io/otel/metric v1.47.0 // indirect
	go.uber.org/multierr v1.11.0 // indirect
	go.uber.org/zap v1.28.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
)
