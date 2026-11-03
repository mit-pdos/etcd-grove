---
upstream: unchecked
checked: 2026-11-03
links: []
---

# server/etcdserver: a read still running when the server stops crashes the process (nil pointer in the closed backend's read transaction)

- **Status**: a crash. Reproduced through etcd's public client API on an embedded server (below).
  The server closes its store and backend (`Cleanup`) while gRPC handlers may still be reading
  them; a read that reaches the backend after it closed dereferences a nil bbolt transaction, and
  the panic, in a gRPC handler goroutine, kills the process.
- **Where** (the etcd pin, `etc/goose.py`, `249d76bea`):
  - `server/etcdserver/server.go:812-830`: `run()`'s deferred stop closes `s.stopping`, waits for
    the server's own goroutines (`s.wg`), stops raft, then `Cleanup()` (`:942-958`): `s.kv.Close()`,
    `s.be.Close()`. gRPC handlers are not among `s.wg`'s goroutines.
  - `server/etcdserver/v3_server.go:138-150`: `Range` waits for the read index only when the
    request is linearizable; a serializable `Range` goes to `txn.Range(..., s.KV(), ...)` directly,
    with no check that the server is stopping. `server/etcdserver/api/v3rpc/interceptor.go:47-75`
    checks nothing of the kind either.
  - `server/storage/backend/batch_tx.go:381-404`, `read_tx.go:133-137`: the backend's last commit
    (`CommitAndStop`) resets the shared read transaction to `tx = nil` and begins none; a read that
    misses the buffer calls `tx.Bucket(...)` on it (`read_tx.go:103`).
  - Who stops the server while its gRPC server still serves: the server itself when this member is
    removed from the cluster or on a fatal error (its run loop returns; the gRPC listeners stay
    until the embedding program calls `embed.Etcd.Close`, or `etcdmain` exits); and
    `embed.Etcd.Close` itself (`server/embed/etcd.go:413-470, 487-520`), which stops the gRPC servers
    first but with `grpc.Server.Stop` after a timeout (open watch streams keep `GracefulStop` from
    finishing) or at once (TLS with HTTP on the same port): grpc-go v1.84's `Stop` does not wait for
    running handlers unless `WaitForHandlers` is set (`google.golang.org/grpc@v1.84.0/server.go:1721`),
    which etcd does not set. A handler still in a read then reads after `Cleanup`.
- **What happens** (reproduction; panics in 5 runs out of 5 at the pin): an embedded single-member
  server, 8 goroutines issuing serializable prefix `Get`s, and `e.Server.Stop()` (the state a
  removed member is in: the server stopped, gRPC serving):

  ```
  panic: runtime error: invalid memory address or nil pointer dereference
    storage/backend/read_tx.go:103
    storage/mvcc/kvstore_txn.go:126, :70; storage/mvcc/metrics_txn.go:41
    etcdserver/txn/range.go:71, :55; etcdserver/v3_server.go:149
    etcdserver/api/v3rpc/key.go:53; etcdserver/api/v3rpc/interceptor.go:75
  ```

  ```go
  package shutdownread

  import (
  	"context"
  	"fmt"
  	"net/url"
  	"testing"
  	"time"

  	clientv3 "go.etcd.io/etcd/client/v3"
  	"go.etcd.io/etcd/server/v3/embed"
  )

  func TestSerializableReadsDuringServerStop(t *testing.T) {
  	cfg := embed.NewConfig()
  	cfg.Dir = t.TempDir()
  	cfg.LogLevel = "error"
  	cu, _ := url.Parse("http://127.0.0.1:23790")
  	pu, _ := url.Parse("http://127.0.0.1:23800")
  	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = []url.URL{*cu}, []url.URL{*cu}
  	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = []url.URL{*pu}, []url.URL{*pu}
  	cfg.InitialCluster = cfg.Name + "=" + pu.String()
  	e, err := embed.StartEtcd(cfg)
  	if err != nil {
  		t.Fatal(err)
  	}
  	<-e.Server.ReadyNotify()
  	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{cu.String()}})
  	if err != nil {
  		t.Fatal(err)
  	}
  	for i := 0; i < 2000; i++ {
  		if _, err := cli.Put(context.TODO(), fmt.Sprintf("k%05d", i), "v"); err != nil {
  			t.Fatal(err)
  		}
  	}
  	stop := make(chan struct{})
  	for g := 0; g < 8; g++ {
  		go func() {
  			for {
  				select {
  				case <-stop:
  					return
  				default:
  				}
  				ctx, cancel := context.WithTimeout(context.TODO(), time.Second)
  				cli.Get(ctx, "k", clientv3.WithPrefix(), clientv3.WithSerializable())
  				cancel()
  			}
  		}()
  	}
  	time.Sleep(200 * time.Millisecond)
  	e.Server.Stop() // the server stops; the gRPC server is still serving
  	time.Sleep(2 * time.Second)
  	close(stop)
  	cli.Close()
  	e.Close()
  }
  ```

  (Run from a module with `examples/go.mod`'s `replace` pins and `go mod tidy`: `embed` needs
  modules the examples module does not list.) At mvcc's level alone the same: reads in a loop while
  `kv.Close()` then `be.Close()` run (`Cleanup`'s order) panic with the same nil dereference, and,
  if the panic is recovered, `be.Close()` then hangs (the panicking reader held the read
  transaction's `txMu`; the other readers wait on it, the final rollback waits on them, bbolt's
  `Close` on the rollback).
- **Expected**: a stopping server rejects new reads and waits for those in flight before closing
  its store and backend, or a read on a closed backend fails with an error.
- **How the proof handles it**: mvcc's candidate API (round 13, `notes/mvcc-api-candidate.md`):
  `Close` gives back no part of the backend's open token, since a read may still hold part of it;
  so no proof can close the backend after the store, which is the step this race breaks. etcd's
  linked results do not reach `Cleanup` or the stop path.
- **Possible fixes**: in the server, a gate in front of the store (reads take it shared, `Cleanup`
  exclusively after marking the server stopped, a read after that failing with `ErrStopped`); or
  `grpc.WaitForHandlers(true)` on etcd's gRPC servers together with stopping them before the
  server, which does not cover the self-stop on removal; or the backend's reads checking that it is
  open (an error instead of a nil dereference).
- **Found**: 2026-11-03, designing the specs of mvcc's `Close` (a client cannot close the backend
  after the store while reads may run), at the user's question whether etcd's shutdown is buggy;
  reproduced the same day.
