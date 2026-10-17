---
upstream: unchecked
checked: 2026-10-17
links:
---

# A user or role name longer than bbolt's `MaxKeySize` makes every member exit while applying it

- **Status**: a bug (a reachable process exit). `UserAdd` and `RoleAdd` check only that the name is
  not empty; the name becomes a bbolt key, and bbolt refuses keys above `MaxKeySize = 32768`
  bytes, which the backend treats as fatal. Nothing on the request path bounds the name below the
  request size limit (1.5 MiB by default). With auth disabled (the default) any client can send
  the request; with auth enabled, an admin.
- **Where**: at the etcd pin of `etc/goose.py` (`09669450f`): `server/auth/store.go:423`
  (`authStore.UserAdd`: `len(r.Name) == 0` is the only check, then `tx.UnsafePutUser(newUser)`
  at line 459, the key `[]byte(user.Name)`), `server/auth/store.go:764` (`RoleAdd`, likewise,
  `tx.UnsafePutRole(newRole)` at line 782); `server/storage/backend/batch_tx.go:169`
  (`batchTx.unsafePut`: any error of `bucket.Put` is `lg.Fatal("failed to write to a bucket")`);
  bbolt v1.5.0 `bucket.go` (`Put` returns `ErrKeyTooLarge` above `MaxKeySize`). The request
  side (`server/etcdserver/v3_server.go` `EtcdServer.UserAdd`/`RoleAdd`,
  `server/etcdserver/api/v3rpc/auth.go`) does not check the name's length; the apply side
  (`server/etcdserver/apply/backend.go:166`, `applierV3backend.UserAdd`) passes the request on.
- **What happens**: the request is proposed, committed and applied; the apply reaches
  `bucket.Put` with a key longer than 32768 bytes, bbolt returns `ErrKeyTooLarge`, and the
  backend's `Fatal` exits the process. Every member applies the same entry, so every member
  exits; on restart each replays the entry from the WAL and exits again. Reproduced at the pin
  with the test below (in package `server/storage/schema`; its logger turns `Fatal` into a panic
  so the test observes it): it logs `{"level":"fatal","msg":"failed to write to a bucket",
  "bucket-name":"authUsers","error":"key too large"}`.

  ```go
  package schema

  import (
  	"strings"
  	"testing"
  	"time"

  	"go.uber.org/zap"
  	"go.uber.org/zap/zapcore"
  	"golang.org/x/crypto/bcrypt"

  	"go.etcd.io/etcd/api/v3/authpb"
  	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
  	"go.etcd.io/etcd/server/v3/auth"
  	"go.etcd.io/etcd/server/v3/storage/backend"
  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  )

  func TestAuthUserAddLongNameFatal(t *testing.T) {
  	lg := zap.NewExample(zap.WithFatalHook(zapcore.WriteThenPanic))
  	bcfg := backend.DefaultBackendConfig(lg)
  	bcfg.Path = t.TempDir() + "/db"
  	bcfg.BatchInterval = time.Hour
  	bcfg.BatchLimit = 10000
  	be := backend.New(bcfg)
  	defer betesting.Close(t, be)

  	tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} {
  		c := make(chan struct{})
  		close(c)
  		return c
  	}, time.Minute)
  	if err != nil {
  		t.Fatal(err)
  	}
  	as := auth.NewAuthStore(lg, NewAuthBackend(lg, be), tp, bcrypt.MinCost)
  	defer func() {
  		if r := recover(); r == nil {
  			t.Fatalf("UserAdd with a 40000-byte name returned without a fatal error")
  		}
  	}()
  	as.UserAdd(&pb.AuthUserAddRequest{
  		Name:    strings.Repeat("a", 40000),
  		Options: &authpb.UserAddOptions{NoPassword: true},
  	})
  }
  ```
- **Expected**: the name's length checked like its emptiness, with an error (at `UserAdd`/
  `RoleAdd`, or where the request enters, before it is proposed), or the bound stated.
- **How the proof handles it**: not yet. The apply package's contract of the auth store
  (`apply.isAuthStore`'s `authReqContract`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/
  Contracts.lean`) says `UserAdd` and `RoleAdd` return for any request, which is false of the
  Go code for such a name; it was a hypothesis (the auth store is names-only), and it cannot
  become `auth.NewAuthStore`'s axiom as stated (unit N4, 2026-10-17, `notes/STATUS.md`). The fix
  in the proof: the request model records the two names (`IRRModel.authUserAdd`/`authRoleAdd`, now
  `Bool`), the workload clause (`rqOk`) bounds them by `maxKeySize`, and the contract's two
  clauses take the bound.
- **Possible fixes**: in `authStore.UserAdd` and `RoleAdd`, return an error (a new
  `ErrUserNameTooLong`/`ErrRoleNameTooLong`, or `ErrUserEmpty`'s kind) when `len(r.Name) >
  bolt.MaxKeySize`; better, reject it in `EtcdServer.UserAdd`/`RoleAdd` before proposing, so the
  entry never reaches the log.
- **Found**: 2026-10-17, writing `auth.NewAuthStore`'s contract as an axiom true of the Go code
  (unit N4, D14d): the auth store's admin writes reach `batchTx.UnsafePut`, whose key bound the
  backend's spec states (`batchTxBuffered.UnsafePut.spec`, `kb.length ≤ maxKeySize`).
