module github.com/mit-pdos/etcd-grove/examples/premisefix/recordetcdrequest

go 1.27.1

replace go.etcd.io/etcd/api/v3 => github.com/upamanyus/etcd/api/v3 v3.0.0-20261107170612-a4d2bb1720b9

replace go.etcd.io/etcd/client/pkg/v3 => github.com/upamanyus/etcd/client/pkg/v3 v3.0.0-20261107170612-a4d2bb1720b9

replace go.etcd.io/etcd/client/v3 => github.com/upamanyus/etcd/client/v3 v3.0.0-20261107170612-a4d2bb1720b9

replace go.etcd.io/etcd/pkg/v3 => github.com/upamanyus/etcd/pkg/v3 v3.0.0-20261107170612-a4d2bb1720b9

replace go.etcd.io/etcd/server/v3 => github.com/upamanyus/etcd/server/v3 v3.0.0-20261107170612-a4d2bb1720b9

replace go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261028061729-565c2bda9e6d

require (
	google.golang.org/grpc v1.84.0
	k8s.io/apimachinery v0.0.0-20261021173754-0b7d352f711c
	k8s.io/apiserver v0.0.0-20261021221356-9c4ec15b8038
)

require (
	github.com/beorn7/perks v1.0.1 // indirect
	github.com/blang/semver/v4 v4.0.0 // indirect
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/fxamacker/cbor/v2 v2.9.4 // indirect
	github.com/go-logr/logr v1.4.4 // indirect
	github.com/munnerz/goautoneg v0.0.0-20191010083416-a7dc8b61c822 // indirect
	github.com/prometheus/client_golang v1.25.0 // indirect
	github.com/prometheus/client_model v0.6.3 // indirect
	github.com/prometheus/common v0.72.0 // indirect
	github.com/prometheus/procfs v0.22.0 // indirect
	github.com/spf13/pflag v1.0.10 // indirect
	github.com/x448/float16 v0.8.4 // indirect
	go.etcd.io/etcd/api/v3 v3.8.0-alpha.0 // indirect
	go.opentelemetry.io/otel v1.47.0 // indirect
	go.opentelemetry.io/otel/trace v1.47.0 // indirect
	go.yaml.in/yaml/v2 v2.4.4 // indirect
	golang.org/x/net v0.59.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
	golang.org/x/text v0.42.0 // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/protobuf v1.36.12 // indirect
	gopkg.in/inf.v0 v0.9.1 // indirect
	k8s.io/component-base v0.0.0-20261018214756-cd2c1afd246a // indirect
	k8s.io/klog/v2 v2.140.0 // indirect
	k8s.io/utils v0.0.0-20260626114624-be93311217bd // indirect
	sigs.k8s.io/json v0.0.0-20250730193827-2d320260d730 // indirect
	sigs.k8s.io/randfill v1.0.0 // indirect
	sigs.k8s.io/structured-merge-diff/v7 v7.0.0 // indirect
)

replace github.com/anishathalye/porcupine => ../../../third_party/porcupine

replace github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest

replace github.com/mit-pdos/etcd-grove/third_party/bridge => ../../../third_party/bridge

// the examples' shared start (examples/lib/etcdstart), in the examples' module
replace github.com/mit-pdos/etcd-grove/examples => ../..
