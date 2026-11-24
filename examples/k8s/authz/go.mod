module github.com/mit-pdos/etcd-grove/examples/k8s/authz

go 1.27.1

require (
	k8s.io/apimachinery v0.0.0
	k8s.io/apiserver v0.0.0
)

require (
	github.com/fxamacker/cbor/v2 v2.9.4 // indirect
	github.com/go-logr/logr v1.4.4 // indirect
	github.com/x448/float16 v0.8.4 // indirect
	go.yaml.in/yaml/v2 v2.4.4 // indirect
	k8s.io/klog/v2 v2.140.0 // indirect
	k8s.io/utils v0.0.0-20260626114624-be93311217bd // indirect
	sigs.k8s.io/json v0.0.0-20250730193827-2d320260d730 // indirect
	sigs.k8s.io/structured-merge-diff/v7 v7.0.1 // indirect
)

// k8s.io/apiserver with conditional authorization (KEP-5681): the fork github.com/upamanyus/kubernetes
// at project k8s-authz's pinned revision (etc/goose.py; GO_MOD_PINS checks the two agree), branch
// goose-lean-authz-fmt2 (github.com/luxas/kubernetes c67a81026c8b, branch
// impl-conditional-authz-review, plus one commit: three %v of a slice spelled out, byte-identical
// output, mit-pdos/etcd-grove#9). Its staging modules require each other at v0.0.0 (the Kubernetes
// repository resolves them with its go.work), so every staging module in the build is replaced by
// the fork's at the same commit, fetched through the module proxy as a subdirectory module.
replace k8s.io/api => github.com/upamanyus/kubernetes/staging/src/k8s.io/api v0.0.0-20261124153932-5b30dab1b141

replace k8s.io/apimachinery => github.com/upamanyus/kubernetes/staging/src/k8s.io/apimachinery v0.0.0-20261124153932-5b30dab1b141

replace k8s.io/apiserver => github.com/upamanyus/kubernetes/staging/src/k8s.io/apiserver v0.0.0-20261124153932-5b30dab1b141

replace k8s.io/client-go => github.com/upamanyus/kubernetes/staging/src/k8s.io/client-go v0.0.0-20261124153932-5b30dab1b141

replace k8s.io/component-base => github.com/upamanyus/kubernetes/staging/src/k8s.io/component-base v0.0.0-20261124153932-5b30dab1b141

replace k8s.io/kms => github.com/upamanyus/kubernetes/staging/src/k8s.io/kms v0.0.0-20261124153932-5b30dab1b141

replace k8s.io/streaming => github.com/upamanyus/kubernetes/staging/src/k8s.io/streaming v0.0.0-20261124153932-5b30dab1b141
