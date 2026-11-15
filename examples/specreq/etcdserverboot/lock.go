package etcdserverboot

import (
	"context"
	"time"

	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3client"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3lock"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3lock/v3lockpb"
)

// REQ etcdserverboot/lock-in-proc: the Lock service over the in-process client acquires a lock under
// its name, with the key it returns under the name, and releases it.
// Users: embed's gRPC registration (embed/serve.go:149-150: v3lock.NewLockServer(v3client.New(s))),
// etcdctl lock.
// Assumes: s serves a cluster with auth off (the call's principal: ctx carries no token, so the
// in-process client's default, none); a thread token for the session.
// Specs: v3client.New (1c, requested), v3lock.NewLockServer.spec, lockServer.Lock.spec,
// lockServer.Unlock.spec (the key under name ++ "/": verify round, A8-provability F6).
func ReqLockOverInProc(s *etcdserver.EtcdServer) {
	c := v3client.New(s)
	ls := v3lock.NewLockServer(c)
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := ls.Lock(ctx, &v3lockpb.LockRequest{Name: []byte("lk")})
	if err != nil {
		return
	}
	k := resp.GetKey()
	if len(k) < 3 || string(k[:3]) != "lk/" { // name + "/" (NewMutex works on pfx + "/")
		panic("lock-in-proc: the lock's key is not under its name")
	}
	_, _ = ls.Unlock(ctx, &v3lockpb.UnlockRequest{Key: k})
}
