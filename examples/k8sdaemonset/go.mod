module github.com/mit-pdos/etcd-grove/examples/k8sdaemonset

go 1.27.1

require (
	github.com/go-logr/logr v1.4.4
	k8s.io/api v0.0.0
	k8s.io/apimachinery v0.0.0
	k8s.io/apiserver v0.0.0
	k8s.io/client-go v0.0.0
	k8s.io/klog/v2 v2.140.0
	k8s.io/kubernetes v1.38.0-alpha.2.0.20261021173803-878cfa6c4cc7
)

require (
	github.com/beorn7/perks v1.0.1 // indirect
	github.com/blang/semver/v4 v4.0.0 // indirect
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/davecgh/go-spew v1.1.2-0.20180830191138-d8f796af33cc // indirect
	github.com/distribution/reference v0.6.0 // indirect
	github.com/fxamacker/cbor/v2 v2.9.4 // indirect
	github.com/go-openapi/jsonpointer v1.0.2 // indirect
	github.com/go-openapi/jsonreference v1.0.2 // indirect
	github.com/go-openapi/swag/conv v0.29.2 // indirect
	github.com/go-openapi/swag/jsonutils v0.29.2 // indirect
	github.com/go-openapi/swag/pools v0.29.2 // indirect
	github.com/go-openapi/swag/typeutils v0.29.2 // indirect
	github.com/google/gnostic-models v0.7.1 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/munnerz/goautoneg v0.0.0-20191010083416-a7dc8b61c822 // indirect
	github.com/opencontainers/go-digest v1.0.0 // indirect
	github.com/pmezard/go-difflib v1.0.1-0.20181226105442-5d4384ee4fb2 // indirect
	github.com/prometheus/client_golang v1.25.0 // indirect
	github.com/prometheus/client_model v0.6.3 // indirect
	github.com/prometheus/common v0.72.0 // indirect
	github.com/prometheus/procfs v0.22.0 // indirect
	github.com/robfig/cron/v3 v3.0.1 // indirect
	github.com/spf13/pflag v1.0.10 // indirect
	github.com/x448/float16 v0.8.4 // indirect
	go.opentelemetry.io/otel v1.47.0 // indirect
	go.opentelemetry.io/otel/trace v1.47.0 // indirect
	go.yaml.in/yaml/v2 v2.4.4 // indirect
	go.yaml.in/yaml/v3 v3.0.5 // indirect
	golang.org/x/net v0.59.0 // indirect
	golang.org/x/oauth2 v0.37.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
	golang.org/x/term v0.46.0 // indirect
	golang.org/x/text v0.42.0 // indirect
	golang.org/x/time v0.16.0 // indirect
	google.golang.org/protobuf v1.36.12 // indirect
	gopkg.in/evanphx/json-patch.v4 v4.13.0 // indirect
	gopkg.in/inf.v0 v0.9.1 // indirect
	k8s.io/apiextensions-apiserver v0.0.0 // indirect
	k8s.io/component-base v0.0.0 // indirect
	k8s.io/component-helpers v0.0.0 // indirect
	k8s.io/controller-manager v0.0.0 // indirect
	k8s.io/kube-openapi v0.0.0-20261014044854-ca3452a79603 // indirect
	k8s.io/kubelet v0.0.0 // indirect
	k8s.io/utils v0.0.0-20260626114624-be93311217bd // indirect
	sigs.k8s.io/json v0.0.0-20250730193827-2d320260d730 // indirect
	sigs.k8s.io/randfill v1.0.0 // indirect
	sigs.k8s.io/structured-merge-diff/v7 v7.0.0 // indirect
	sigs.k8s.io/yaml v1.6.0 // indirect
)

// The DaemonSet controller (dsmain imports it): k8s.io/kubernetes at master 878cfa6c4cc7
// (2026-10-21T17:38Z, kubernetes/kubernetes#143270's merge; notes/k8s-daemonset-goose.md, "The
// pin"). k8s.io/kubernetes requires its staging modules at v0.0.0 (its own go.mod replaces them
// by ./staging), so a module importing it replaces each one it needs by the module's mirror
// (github.com/kubernetes/<name>): the four the repository already pins (examples/k8setcd3/go.mod,
// shared with project k8s-apiserver's translation; etc/goose.py's CLIENT_GO_PINS checks they
// agree), and the others at their mirror's latest commit by 2026-10-21T22:14Z (when the
// apiserver mirror published 878cfa6c4cc7). The Go files of every one are identical to
// staging/src/k8s.io/<name> at 878cfa6c4cc7 (checked by diff, 2026-10-27); ktesting only for
// the tests of k8s.io/kubernetes/pkg/controller, which go mod tidy loads.
replace (
	k8s.io/api => k8s.io/api v0.0.0-20261020174351-067c983ccbc3
	k8s.io/apiextensions-apiserver => k8s.io/apiextensions-apiserver v0.0.0-20261021192051-3da7cab8aae0
	k8s.io/apimachinery => k8s.io/apimachinery v0.0.0-20261021173754-0b7d352f711c
	k8s.io/apiserver => k8s.io/apiserver v0.0.0-20261021221356-9c4ec15b8038
	k8s.io/client-go => k8s.io/client-go v0.0.0-20261021054439-569675c57fa3
	k8s.io/component-base => k8s.io/component-base v0.0.0-20261018214756-cd2c1afd246a
	k8s.io/component-helpers => k8s.io/component-helpers v0.20.0-alpha.2.0.20261014064534-e0a714b31fcd
	k8s.io/controller-manager => k8s.io/controller-manager v0.20.0-alpha.1.0.20261016223050-ad0db927ba11
	k8s.io/ktesting => k8s.io/ktesting v0.38.0-alpha.2.0.20261015021345-0c9393b43e6d
	k8s.io/kubelet => k8s.io/kubelet v0.0.0-20261014232747-e715b5d84f6c
)
