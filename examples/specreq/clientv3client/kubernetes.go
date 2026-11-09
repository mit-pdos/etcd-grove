package clientv3client

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
)

// REQ clientv3client/kube-new: kubernetes.New gives a client whose Kubernetes field is itself, whose
// KV the caller may wrap before sharing it.
// Users: Kubernetes' storagebackend/factory/etcd3.go:352, its test server.
// Assumes: ep serves the cluster.
// Specs: Kubernetes.New.spec, clientMut_KV, clientMut_freeze (W0), kubeClient_kubeAt.
func ReqKubeNew(ep string, lg *zap.Logger) *kubernetes.Client {
	kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{ep}, Logger: lg})
	if err != nil {
		if kc != nil {
			panic("kube-new: client with an error")
		}
		return nil
	}
	kc.Client.KV = wrapKV{kc.Client.KV}
	if kc.Kubernetes == nil {
		panic("kube-new: no interface")
	}
	return kc
}

// REQ clientv3client/kube-cas: OptimisticPut at the key's current mod revision succeeds (nobody
// else writes it), at a stale one fails and, with GetOnFailure, returns the current key-value.
// Users: Kubernetes' etcd3 store (Create with 0, GuaranteedUpdate's retry on conflict).
// Assumes: key is written by no other principal and attached to no lease.
// Specs: Kubernetes.Client.{Get,OptimisticPut}.spec (Kube.methods through kubeAt).
func ReqKubeCAS(ctx context.Context, kc *kubernetes.Client, key string) {
	g, err := kc.Kubernetes.Get(ctx, key, kubernetes.GetOptions{})
	if err != nil {
		return
	}
	var rev int64
	if g.KV != nil {
		rev = g.KV.ModRevision
	}
	p, err := kc.Kubernetes.OptimisticPut(ctx, key, []byte("v"), rev, kubernetes.PutOptions{GetOnFailure: true})
	if err != nil {
		return
	}
	if !p.Succeeded {
		panic("kube-cas: CAS at the current revision failed")
	}
	q, err := kc.Kubernetes.OptimisticPut(ctx, key, []byte("w"), rev, kubernetes.PutOptions{GetOnFailure: true})
	if err != nil {
		return
	}
	if q.Succeeded {
		panic("kube-cas: CAS at a stale revision succeeded")
	}
	if q.KV == nil || q.KV.ModRevision != p.Revision {
		panic("kube-cas: failure did not return the current key-value")
	}
}

// REQ clientv3client/kube-list: a List page at a revision returns at most the limit, its count and
// revision; a Get at the list's revision sees the listed value.
// Users: Kubernetes' etcd3 store (GetList's pages, a consistent read at the list's revision).
// Assumes: limit > 0; nothing compacts below the list's revision (the owner's invariant).
// Specs: Kubernetes.Client.{List,Get}.spec; model: RangeReq.answers.
func ReqKubeList(ctx context.Context, kc *kubernetes.Client, prefix string, limit int64) {
	l, err := kc.Kubernetes.List(ctx, prefix, kubernetes.ListOptions{Limit: limit})
	if err != nil {
		return
	}
	if int64(len(l.Kvs)) > limit {
		panic("kube-list: page above the limit")
	}
	if len(l.Kvs) == 0 {
		return
	}
	g, err := kc.Kubernetes.Get(ctx, string(l.Kvs[0].Key), kubernetes.GetOptions{Revision: l.Revision})
	if err != nil {
		return
	}
	if g.KV == nil || string(g.KV.Value) != string(l.Kvs[0].Value) {
		panic("kube-list: a read at the list's revision differs")
	}
}
