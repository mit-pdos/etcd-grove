// Package k8setcd3 pins the Kubernetes API server's etcd3 storage backend
// (k8s.io/apiserver/pkg/storage/etcd3) over this repository's etcd fork, for its Goose
// translation (project k8s-apiserver of etc/goose.py; notes/k8s-etcd3-goose.md).
package k8setcd3

import (
	_ "go.etcd.io/etcd/client/v3/kubernetes"
	_ "k8s.io/apiserver/pkg/storage/etcd3"
)
