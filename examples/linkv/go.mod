module github.com/mit-pdos/etcd-grove/examples/linkv

go 1.27

replace (
	go.etcd.io/etcd/api/v3 => github.com/upamanyus/etcd/api/v3 v3.0.0-20261018220001-8a24be2a324f
	go.etcd.io/etcd/client/pkg/v3 => github.com/upamanyus/etcd/client/pkg/v3 v3.0.0-20261018220001-8a24be2a324f
	go.etcd.io/etcd/client/v3 => github.com/upamanyus/etcd/client/v3 v3.0.0-20261018220001-8a24be2a324f
	go.etcd.io/etcd/pkg/v3 => github.com/upamanyus/etcd/pkg/v3 v3.0.0-20261018220001-8a24be2a324f
	go.etcd.io/etcd/server/v3 => github.com/upamanyus/etcd/server/v3 v3.0.0-20261018220001-8a24be2a324f
	go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261015121415-509271dac8a4
)

// The driver and the vendored porcupine (third_party/porcupine/UPSTREAM.md), as translated.
replace (
	github.com/anishathalye/porcupine => ../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lintest => ../lintest
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples/lintest v0.0.0-00010101000000-000000000000
	go.etcd.io/etcd/client/pkg/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/client/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/server/v3 v3.0.0-00010101000000-000000000000
	go.uber.org/zap v1.28.0
)

require (
	github.com/Masterminds/semver/v3 v3.5.0 // indirect
	github.com/beorn7/perks v1.0.1 // indirect
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/dustin/go-humanize v1.1.0 // indirect
	github.com/go-logr/logr v1.4.4 // indirect
	github.com/go-logr/stdr v1.2.2 // indirect
	github.com/golang-jwt/jwt/v5 v5.3.1 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	github.com/google/go-cmp v0.7.0 // indirect
	github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus v1.1.0 // indirect
	github.com/grpc-ecosystem/go-grpc-middleware/v2 v2.3.4 // indirect
	github.com/grpc-ecosystem/grpc-gateway/v2 v2.31.0 // indirect
	github.com/jonboulle/clockwork v0.5.0 // indirect
	github.com/munnerz/goautoneg v0.0.0-20191010083416-a7dc8b61c822 // indirect
	github.com/prometheus/client_golang v1.24.1 // indirect
	github.com/prometheus/client_model v0.6.3 // indirect
	github.com/prometheus/common v0.72.0 // indirect
	github.com/prometheus/procfs v0.21.1 // indirect
	github.com/spf13/pflag v1.0.10 // indirect
	github.com/xiang90/probing v0.0.0-20221125231312-a49e3df8f510 // indirect
	go.etcd.io/bbolt v1.5.0 // indirect
	go.etcd.io/etcd/api/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/etcd/pkg/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/raft/v3 v3.7.0 // indirect
	go.opentelemetry.io/auto/sdk v1.2.1 // indirect
	go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc v0.71.0 // indirect
	go.opentelemetry.io/otel v1.47.0 // indirect
	go.opentelemetry.io/otel/log v1.47.0 // indirect
	go.opentelemetry.io/otel/metric v1.47.0 // indirect
	go.opentelemetry.io/otel/trace v1.47.0 // indirect
	go.uber.org/multierr v1.11.0 // indirect
	golang.org/x/crypto v0.57.0 // indirect
	golang.org/x/net v0.59.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
	golang.org/x/text v0.42.0 // indirect
	golang.org/x/time v0.16.0 // indirect
	google.golang.org/genproto/googleapis/api v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/grpc v1.84.0 // indirect
	google.golang.org/protobuf v1.36.12 // indirect
	k8s.io/utils v0.0.0-20260108192941-914a6e750570 // indirect
)
