module github.com/mit-pdos/etcd-grove/examples/k8s/dist

go 1.27.1

// bbolt: the fork examples/go.mod uses (project bbolt's pin), so that the members run what
// etcd-dist's members run.
replace go.etcd.io/bbolt => github.com/upamanyus/bbolt v0.0.0-20261125221737-2f6fcfff7e4b

// etcd and raft: the forks at the pins of etc/goose.py's projects etcd and raft (as examples/go.mod
// and the other k8s modules).
replace (
	go.etcd.io/etcd/api/v3 => github.com/upamanyus/etcd/api/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/etcd/cache/v3 => github.com/upamanyus/etcd/cache/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/etcd/client/pkg/v3 => github.com/upamanyus/etcd/client/pkg/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/etcd/client/v3 => github.com/upamanyus/etcd/client/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/etcd/pkg/v3 => github.com/upamanyus/etcd/pkg/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/etcd/server/v3 => github.com/upamanyus/etcd/server/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/etcd/tests/v3 => github.com/upamanyus/etcd/tests/v3 v3.0.0-20261126202330-30df685e43e2
	go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261110053807-d2c16c558247
)

// The examples' module (etcd-dist: examples/etcd/dist; etcdstart, robust), the k8s drivers this
// module's copies come from (examples/k8s/etcd3's correctness package is imported as is), Remote,
// lintest, the vendored porcupine and etcd's test bridge, as translated.
replace (
	github.com/anishathalye/porcupine => ../../../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples => ../..
	github.com/mit-pdos/etcd-grove/examples/k8s/compactor => ../compactor
	github.com/mit-pdos/etcd-grove/examples/k8s/etcd3 => ../etcd3
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ../../lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ../../lib/remote
	github.com/mit-pdos/etcd-grove/third_party/bridge => ../../../third_party/bridge
	models.lab => ../../../models
)

require (
	github.com/anishathalye/porcupine v1.3.1
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/mit-pdos/etcd-grove/examples v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/examples/k8s/etcd3 v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/third_party/bridge v0.0.0-00010101000000-000000000000
	go.etcd.io/etcd/client/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/server/v3 v3.8.0-alpha.0
	go.uber.org/zap v1.28.0
	k8s.io/apimachinery v0.0.0-20261021173754-0b7d352f711c
	k8s.io/apiserver v0.0.0-20261021221356-9c4ec15b8038
	k8s.io/utils v0.0.0-20260626114624-be93311217bd
)

require (
	github.com/Masterminds/semver/v3 v3.5.0 // indirect
	github.com/beorn7/perks v1.0.1 // indirect
	github.com/blang/semver/v4 v4.0.0 // indirect
	github.com/cenkalti/backoff/v5 v5.0.3 // indirect
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/davecgh/go-spew v1.1.2-0.20180830191138-d8f796af33cc // indirect
	github.com/dustin/go-humanize v1.1.0 // indirect
	github.com/emicklei/go-restful/v3 v3.14.0 // indirect
	github.com/felixge/httpsnoop v1.1.0 // indirect
	github.com/fxamacker/cbor/v2 v2.9.4 // indirect
	github.com/go-logr/logr v1.4.4 // indirect
	github.com/go-logr/stdr v1.2.2 // indirect
	github.com/go-openapi/jsonpointer v1.0.2 // indirect
	github.com/go-openapi/jsonreference v1.0.2 // indirect
	github.com/go-openapi/swag/conv v0.29.2 // indirect
	github.com/go-openapi/swag/jsonutils v0.29.2 // indirect
	github.com/go-openapi/swag/pools v0.29.2 // indirect
	github.com/go-openapi/swag/typeutils v0.29.2 // indirect
	github.com/golang-jwt/jwt/v5 v5.3.1 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	github.com/google/gnostic-models v0.7.1 // indirect
	github.com/google/go-cmp v0.7.0 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus v1.1.0 // indirect
	github.com/grpc-ecosystem/go-grpc-middleware/v2 v2.3.4 // indirect
	github.com/grpc-ecosystem/grpc-gateway/v2 v2.31.0 // indirect
	github.com/jonboulle/clockwork v0.5.0 // indirect
	github.com/kylelemons/godebug v1.1.0 // indirect
	github.com/munnerz/goautoneg v0.0.0-20191010083416-a7dc8b61c822 // indirect
	github.com/pmezard/go-difflib v1.0.1-0.20181226105442-5d4384ee4fb2 // indirect
	github.com/prometheus/client_golang v1.25.0 // indirect
	github.com/prometheus/client_model v0.6.3 // indirect
	github.com/prometheus/common v0.72.0 // indirect
	github.com/prometheus/procfs v0.22.0 // indirect
	github.com/spf13/pflag v1.0.10 // indirect
	github.com/x448/float16 v0.8.4 // indirect
	github.com/xiang90/probing v0.0.0-20221125231312-a49e3df8f510 // indirect
	go.etcd.io/bbolt v1.5.0 // indirect
	go.etcd.io/etcd/api/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/etcd/cache/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/etcd/client/pkg/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/etcd/pkg/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/raft/v3 v3.7.0 // indirect
	go.opentelemetry.io/auto/sdk v1.2.1 // indirect
	go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc v0.72.0 // indirect
	go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp v0.72.0 // indirect
	go.opentelemetry.io/otel v1.47.0 // indirect
	go.opentelemetry.io/otel/exporters/otlp/otlptrace v1.47.0 // indirect
	go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.47.0 // indirect
	go.opentelemetry.io/otel/log v1.47.0 // indirect
	go.opentelemetry.io/otel/metric v1.47.0 // indirect
	go.opentelemetry.io/otel/sdk v1.47.0 // indirect
	go.opentelemetry.io/otel/trace v1.47.0 // indirect
	go.opentelemetry.io/proto/otlp v1.11.1 // indirect
	go.uber.org/multierr v1.11.0 // indirect
	go.yaml.in/yaml/v2 v2.4.4 // indirect
	go.yaml.in/yaml/v3 v3.0.5 // indirect
	golang.org/x/crypto v0.57.0 // indirect
	golang.org/x/net v0.59.0 // indirect
	golang.org/x/oauth2 v0.37.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
	golang.org/x/term v0.46.0 // indirect
	golang.org/x/text v0.42.0 // indirect
	golang.org/x/time v0.16.0 // indirect
	google.golang.org/genproto/googleapis/api v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/grpc v1.84.0 // indirect
	google.golang.org/protobuf v1.36.12 // indirect
	gopkg.in/evanphx/json-patch.v4 v4.13.0 // indirect
	gopkg.in/inf.v0 v0.9.1 // indirect
	k8s.io/api v0.0.0-20261020174351-067c983ccbc3 // indirect
	k8s.io/client-go v0.0.0-20261021054439-569675c57fa3 // indirect
	k8s.io/component-base v0.0.0-20261018214756-cd2c1afd246a // indirect
	k8s.io/klog/v2 v2.140.0 // indirect
	k8s.io/kube-openapi v0.0.0-20261014044854-ca3452a79603 // indirect
	sigs.k8s.io/json v0.0.0-20250730193827-2d320260d730 // indirect
	sigs.k8s.io/randfill v1.0.0 // indirect
	sigs.k8s.io/structured-merge-diff/v7 v7.0.0 // indirect
	sigs.k8s.io/yaml v1.6.0 // indirect
)

// k8s.io/apimachinery and k8s.io/apiserver at the pins above, from the fork upamanyus/kubernetes,
// branch goose-lean-fmt1 (on Kubernetes 878cfa6c4c): their go.mod/go.sum as published, and
// Preconditions.Check formatting its UIDs as strings (real fmt stage 1, mit-pdos/etcd-grove#9)
replace k8s.io/apimachinery => github.com/upamanyus/kubernetes/staging/src/k8s.io/apimachinery v0.0.0-20261124053658-ef23adaea1b3

replace k8s.io/apiserver => github.com/upamanyus/kubernetes/staging/src/k8s.io/apiserver v0.0.0-20261124053658-ef23adaea1b3
