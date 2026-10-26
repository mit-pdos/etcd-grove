---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#10907 pr merged: related, not this bug (added RoleAdd's empty-name check, the only name check besides UserAdd's; no length bound)
candidate: issues/upstream/etcd-auth-useradd-long-name-fatal/
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
  "bucket-name":"authUsers","error":"key too large"}`. Confirmed end to end through gRPC below.

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
- **Through gRPC, end to end** (2026-10-18, upstream `main` at `22cc5d9`, `etcd` and `etcdctl`
  built with `go build` from `server/` and `etcdctl/`): a three-member cluster on localhost with
  the default configuration (auth disabled), then

  ```sh
  etcdctl --endpoints=$EP user add "$(head -c 40000 /dev/zero | tr '\0' a)" --no-password
  ```

  The client gets `rpc error: code = Unavailable desc = error reading from server: EOF`, and all
  three members exit at once, each logging `{"level":"fatal","caller":"backend/batch_tx.go:184",
  "msg":"failed to write to a bucket","bucket-name":"authUsers","error":"key too large"}`.
  Restarting all three: they re-form a quorum, apply the entry again and all exit with the same
  line, on each of two full restarts (30 s observed each time); the cluster stays down. A member
  restarted alone stays up (it does not reach the entry without a quorum). `etcdctl role add
  <name>` does the same (`"bucket-name":"authRoles"`): with a 32769-byte name all three exit; with
  32768 bytes (`MaxKeySize`) the role is created and the cluster is fine. The script (members on
  ports 23791-23793 / 23801-23803, data in a fresh directory):

  ```sh
  B=./bin; W=./run; mkdir -p $W
  CL=m1=http://127.0.0.1:23801,m2=http://127.0.0.1:23802,m3=http://127.0.0.1:23803
  start() { i=$1; $B/etcd --name m$i --data-dir $W/m$i.etcd \
      --listen-client-urls http://127.0.0.1:2379$i --advertise-client-urls http://127.0.0.1:2379$i \
      --listen-peer-urls http://127.0.0.1:2380$i --initial-advertise-peer-urls http://127.0.0.1:2380$i \
      --initial-cluster $CL --initial-cluster-state new --initial-cluster-token authrepro \
      >> $W/m$i.log 2>&1 & }
  EP=http://127.0.0.1:23791,http://127.0.0.1:23792,http://127.0.0.1:23793
  for i in 1 2 3; do start $i; done; sleep 5
  $B/etcdctl --endpoints=$EP endpoint health
  $B/etcdctl --endpoints=$EP user add "$(head -c 40000 /dev/zero | tr '\0' a)" --no-password
  sleep 3; grep '"level":"fatal"' $W/m*.log      # all three
  for i in 1 2 3; do start $i; done; sleep 15
  grep -c '"level":"fatal"' $W/m*.log            # 2 each: they exit again
  ```

  For upstream this should become an e2e test (`tests/e2e`, which runs the members as processes:
  an integration test's in-process members would take the test binary down with them).
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
  bolt.MaxKeySize`; or reject it in `EtcdServer.UserAdd`/`RoleAdd` before proposing, so the
  entry never reaches the log. The upstream candidate (`issues/upstream/etcd-auth-useradd-long-name-fatal/`,
  2026-10-23) takes the first: it is where the empty-name check is, and only an apply-time check lets a
  cluster whose WAL already holds such an entry restart (checked: the base's crashed data directories
  restart healthy with the fixed `etcd`).
- **Found**: 2026-10-17, writing `auth.NewAuthStore`'s contract as an axiom true of the Go code
  (unit N4, D14d): the auth store's admin writes reach `batchTx.UnsafePut`, whose key bound the
  backend's spec states (`batchTxBuffered.UnsafePut.spec`, `kb.length ≤ maxKeySize`).
