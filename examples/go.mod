module github.com/mit-pdos/etcd-grove/examples

go 1.27

// etcd and raft: the forks at the pins of etc/goose.py's projects etcd and raft (pseudo-versions;
// `etc/goose.py --check` fails if they differ). tests/v3 is linkvtxn's differential test's
// (robustness's model), test-only.
replace (
	go.etcd.io/etcd/api/v3 => github.com/upamanyus/etcd/api/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/etcd/cache/v3 => github.com/upamanyus/etcd/cache/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/etcd/client/pkg/v3 => github.com/upamanyus/etcd/client/pkg/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/etcd/client/v3 => github.com/upamanyus/etcd/client/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/etcd/pkg/v3 => github.com/upamanyus/etcd/pkg/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/etcd/server/v3 => github.com/upamanyus/etcd/server/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/etcd/tests/v3 => github.com/upamanyus/etcd/tests/v3 v3.0.0-20261125101634-251a430ce042
	go.etcd.io/raft/v3 => github.com/upamanyus/etcd/v3 v3.0.0-20261110053807-d2c16c558247
)

// The driver (a module of its own, which kvwitness shares), Remote (examples/lib/remote, a module
// of its own: etcd-dist's clients on machines of their own), the library models (models/:
// examples/models tests models/protobuf/pbgen.py on etcd's messages), the vendored porcupine
// (third_party/porcupine/UPSTREAM.md) and etcd's test bridge (third_party/bridge/UPSTREAM.md),
// as translated.
replace (
	github.com/anishathalye/porcupine => ../third_party/porcupine
	github.com/mit-pdos/etcd-grove/examples/lib/lintest => ./lib/lintest
	github.com/mit-pdos/etcd-grove/examples/lib/remote => ./lib/remote
	github.com/mit-pdos/etcd-grove/third_party/bridge => ../third_party/bridge
	models.lab => ../models
)

require (
	github.com/Masterminds/semver/v3 v3.5.0
	github.com/anishathalye/porcupine v1.3.1
	github.com/cespare/xxhash/v2 v2.3.0
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus v1.1.0
	github.com/mit-pdos/etcd-grove/examples/lib/lintest v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/examples/lib/remote v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/etcd-grove/third_party/bridge v0.0.0-00010101000000-000000000000
	github.com/mit-pdos/gokv v0.1.1
	github.com/prometheus/client_golang v1.24.1
	github.com/xiang90/probing v0.0.0-20221125231312-a49e3df8f510
	go.etcd.io/bbolt v1.5.0
	go.etcd.io/etcd/api/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/cache/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/client/pkg/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/client/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/pkg/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/server/v3 v3.8.0-alpha.0
	go.etcd.io/etcd/tests/v3 v3.0.0-00010101000000-000000000000
	go.etcd.io/raft/v3 v3.7.0
	go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc v0.71.0
	go.opentelemetry.io/otel v1.47.0
	go.opentelemetry.io/otel/sdk v1.47.0
	go.opentelemetry.io/otel/trace v1.47.0
	go.uber.org/zap v1.28.0
	golang.org/x/crypto v0.57.0
	golang.org/x/net v0.59.0
	golang.org/x/sys v0.48.0
	golang.org/x/time v0.16.0
	google.golang.org/grpc v1.84.0
	google.golang.org/protobuf v1.36.12
	k8s.io/utils v0.0.0-20260108192941-914a6e750570
	models.lab v0.0.0-00010101000000-000000000000
)

require (
	github.com/VividCortex/ewma v1.2.0 // indirect
	github.com/beorn7/perks v1.0.1 // indirect
	github.com/bgentry/speakeasy v0.2.0 // indirect
	github.com/cenkalti/backoff/v5 v5.0.3 // indirect
	github.com/cheggaaa/pb/v3 v3.2.1 // indirect
	github.com/clipperhouse/displaywidth v0.11.0 // indirect
	github.com/clipperhouse/uax29/v2 v2.7.0 // indirect
	github.com/coreos/go-systemd/v22 v22.7.0 // indirect
	github.com/dustin/go-humanize v1.1.0 // indirect
	github.com/fatih/color v1.19.0 // indirect
	github.com/go-logr/logr v1.4.4 // indirect
	github.com/go-logr/stdr v1.2.2 // indirect
	github.com/golang-jwt/jwt/v5 v5.3.1 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	github.com/google/go-cmp v0.7.0 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/gorilla/websocket v1.5.3 // indirect
	github.com/grpc-ecosystem/go-grpc-middleware/v2 v2.3.4 // indirect
	github.com/grpc-ecosystem/grpc-gateway/v2 v2.31.0 // indirect
	github.com/inconshreveable/mousetrap v1.1.0 // indirect
	github.com/jonboulle/clockwork v0.5.0 // indirect
	github.com/mattn/go-colorable v0.1.15 // indirect
	github.com/mattn/go-isatty v0.0.24 // indirect
	github.com/mattn/go-runewidth v0.0.27 // indirect
	github.com/munnerz/goautoneg v0.0.0-20191010083416-a7dc8b61c822 // indirect
	github.com/olekukonko/cat v0.0.0-20250911104152-50322a0618f6 // indirect
	github.com/olekukonko/errors v1.2.0 // indirect
	github.com/olekukonko/ll v0.1.6 // indirect
	github.com/olekukonko/tablewriter v1.1.5 // indirect
	github.com/prometheus/client_model v0.6.3 // indirect
	github.com/prometheus/common v0.72.0 // indirect
	github.com/prometheus/procfs v0.21.1 // indirect
	github.com/sirupsen/logrus v1.10.2 // indirect
	github.com/soheilhy/cmux v0.1.5 // indirect
	github.com/spf13/cobra v1.10.2 // indirect
	github.com/spf13/pflag v1.0.10 // indirect
	github.com/stretchr/testify v1.12.1 // indirect
	github.com/tmc/grpc-websocket-proxy v0.0.0-20220101234140-673ab2c3ae75 // indirect
	go.etcd.io/etcd/etcdctl/v3 v3.8.0-alpha.0 // indirect
	go.etcd.io/gofail v0.2.0 // indirect
	go.opentelemetry.io/auto/sdk v1.2.1 // indirect
	go.opentelemetry.io/otel/exporters/otlp/otlptrace v1.47.0 // indirect
	go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.47.0 // indirect
	go.opentelemetry.io/otel/log v1.47.0 // indirect
	go.opentelemetry.io/otel/metric v1.47.0 // indirect
	go.opentelemetry.io/proto/otlp v1.11.1 // indirect
	go.uber.org/multierr v1.11.0 // indirect
	go.yaml.in/yaml/v2 v2.4.4 // indirect
	go.yaml.in/yaml/v3 v3.0.5 // indirect
	golang.org/x/text v0.42.0 // indirect
	google.golang.org/genproto/googleapis/api v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc // indirect
	gopkg.in/natefinch/lumberjack.v2 v2.2.1 // indirect
	sigs.k8s.io/yaml v1.6.0 // indirect
)

replace go.etcd.io/bbolt => github.com/upamanyus/bbolt v0.0.0-20261124052636-7d335aa3eb23
