package schema

// The restated read contract (etcd-grove's auth.authReadTxOk after the second refutation of
// authSchemaSrv, Q1 (a)): a read transaction sees, per auth bucket, a recorded state (the `auth`
// bucket's flag and revision at one, `authUsers` at one, `authRoles` at one), and the users'
// state is not later than the revision's. This holds when the writer, as the auth store's admin
// steps do, never puts and deletes in one bucket in one batch (the write contract's session
// discipline, auth.AuthSess). The one-state reading (the text before the restatement) is the
// control: it fails here, as in zz_authschema_window_test.go.
//
// Copy into server/storage/schema of etcd at the fork pin and run
//   go test ./storage/schema/ -run TestAuthSchemaReadPerBucket -count=1 -v

import (
	"fmt"
	"sort"
	"strings"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"golang.org/x/crypto/bcrypt"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/auth"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

var pbRoles = []string{"r1", "r2"}

type pbObs struct {
	rev   uint64
	en    bool
	users string
	roles string
}

// pbRead reads the three auth buckets in one read transaction, as the store's readers do.
func pbRead(abe auth.AuthBackend) pbObs {
	tx := abe.ReadTx()
	tx.RLock()
	defer tx.RUnlock()
	var o pbObs
	o.en = tx.UnsafeReadAuthEnabled()
	o.rev = tx.UnsafeReadAuthRevision()
	var us []string
	for _, u := range tx.UnsafeGetAllUsers() {
		rs := append([]string(nil), u.Roles...)
		sort.Strings(rs)
		us = append(us, string(u.Name)+":"+strings.Join(rs, ","))
	}
	sort.Strings(us)
	o.users = strings.Join(us, ";")
	var rs []string
	for _, n := range pbRoles {
		if r := tx.UnsafeGetRole(n); r != nil {
			rs = append(rs, fmt.Sprintf("%s:%d", n, len(r.KeyPermission)))
		}
	}
	o.roles = strings.Join(rs, ";")
	return o
}

func TestAuthSchemaReadPerBucket(t *testing.T) {
	lg := zap.NewNop()
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	abe := NewAuthBackend(lg, be)
	tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} {
		ch := make(chan struct{})
		close(ch)
		return ch
	}, 300*time.Second)
	if err != nil {
		t.Fatal(err)
	}
	as := auth.NewAuthStore(lg, abe, tp, bcrypt.MinCost)
	defer as.Close()

	// hist[i]: the i-th recorded state (each admin step bumps the revision by one; the writer
	// reads the state back after the step, when no batch is open).
	var mu sync.Mutex
	hist := []pbObs{pbRead(abe)}
	base := hist[0].rev
	record := func() {
		o := pbRead(abe)
		mu.Lock()
		if o.rev != base+uint64(len(hist)) {
			t.Errorf("revision %d after step %d", o.rev, len(hist))
		}
		hist = append(hist, o)
		mu.Unlock()
	}

	var obsMu sync.Mutex
	var obs []pbObs
	stop := make(chan struct{})
	var wg sync.WaitGroup
	for r := 0; r < 4; r++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			var local []pbObs
			for {
				select {
				case <-stop:
					obsMu.Lock()
					obs = append(obs, local...)
					obsMu.Unlock()
					return
				default:
				}
				local = append(local, pbRead(abe))
			}
		}()
	}
	failed := false
	must := func(_ any, err error) {
		if err != nil && !failed {
			failed = true
			t.Error(err)
		}
	}
	noPw := &authpb.UserAddOptions{NoPassword: true}
	perm := &authpb.Permission{PermType: authpb.READ, Key: []byte("k")}
	deadline := time.Now().Add(30 * time.Second)
	for i := 0; i < 3000 && time.Now().Before(deadline) && !failed; i++ {
		// every step of the cycle: puts only, or deletes in one bucket and puts in others
		must(as.RoleAdd(&pb.AuthRoleAddRequest{Name: "r1"}))
		record()
		must(as.RoleAdd(&pb.AuthRoleAddRequest{Name: "r2"}))
		record()
		must(as.UserAdd(&pb.AuthUserAddRequest{Name: "u", Options: noPw}))
		record()
		must(as.UserAdd(&pb.AuthUserAddRequest{Name: "v", Options: noPw}))
		record()
		must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "u", Role: "r1"}))
		record()
		must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "v", Role: "r1"}))
		record()
		must(as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "r1", Perm: perm}))
		record()
		must(as.UserDelete(&pb.AuthUserDeleteRequest{Name: "v"})) // users: delete; auth: put
		record()
		must(as.RoleDelete(&pb.AuthRoleDeleteRequest{Role: "r1"})) // roles: delete; users, auth: put
		record()
		must(as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "u", Role: "r2"}))
		record()
		must(as.RoleDelete(&pb.AuthRoleDeleteRequest{Role: "r2"}))
		record()
		must(as.UserDelete(&pb.AuthUserDeleteRequest{Name: "u"}))
		record()
	}
	close(stop)
	wg.Wait()
	if failed {
		return
	}

	usersAt := map[string][]int{}
	rolesAt := map[string][]int{}
	whole := map[pbObs]bool{}
	for i, h := range hist {
		usersAt[h.users] = append(usersAt[h.users], i)
		rolesAt[h.roles] = append(rolesAt[h.roles], i)
		whole[h] = true
	}
	var bad, oneStateBad int
	for _, o := range obs {
		ia := int(o.rev - base)
		okA := ia >= 0 && ia < len(hist) && hist[ia].en == o.en
		okU := false
		for _, iu := range usersAt[o.users] {
			if iu <= ia {
				okU = true
			}
		}
		okR := len(rolesAt[o.roles]) > 0
		if !(okA && okU && okR) {
			if bad < 5 {
				t.Errorf("per-bucket contract violated: revision %d users %q roles %q", o.rev, o.users, o.roles)
			}
			bad++
		}
		if !whole[o] {
			oneStateBad++
		}
	}
	t.Logf("steps %d, reads %d; per-bucket violations %d; reads of no single recorded state "+
		"(the old one-state text, the control) %d", len(hist)-1, len(obs), bad, oneStateBad)
	if oneStateBad == 0 {
		t.Logf("control: no mixed read this run (the window is narrow; rerun)")
	}
}

// TestAuthSchemaReadMixedBucketSession: why the write contract needs the session discipline. A
// batch that puts one user and deletes another (one bucket, one batch; no admin step of the store
// does this) leaves readers a users bucket of neither state: the put is written back before the
// delete is committed.
func TestAuthSchemaReadMixedBucketSession(t *testing.T) {
	lg := zap.NewNop()
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	abe := NewAuthBackend(lg, be)
	abe.CreateAuthBuckets()
	put := func(tx auth.AuthBatchTx, n string) {
		tx.UnsafePutUser(&authpb.User{Name: []byte(n), Options: &authpb.UserAddOptions{NoPassword: true}})
	}
	tx := abe.BatchTx()
	tx.Lock()
	put(tx, "b")
	tx.Unlock()
	abe.ForceCommit()

	var obsMu sync.Mutex
	var both int
	stop := make(chan struct{})
	var wg sync.WaitGroup
	for r := 0; r < 4; r++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			n := 0
			for {
				select {
				case <-stop:
					obsMu.Lock()
					both += n
					obsMu.Unlock()
					return
				default:
				}
				rt := abe.ReadTx()
				rt.RLock()
				a, b := rt.UnsafeGetUser("a"), rt.UnsafeGetUser("b")
				rt.RUnlock()
				// recorded states alternate {b} and {a}; {a, b} is neither
				if a != nil && b != nil {
					n++
				}
			}
		}()
	}
	cur, other := "b", "a"
	deadline := time.Now().Add(20 * time.Second)
	for i := 0; i < 100000 && time.Now().Before(deadline); i++ {
		tx := abe.BatchTx()
		tx.Lock()
		put(tx, other)
		tx.UnsafeDeleteUser(cur)
		tx.Unlock()
		cur, other = other, cur
	}
	close(stop)
	wg.Wait()
	t.Logf("reads of a users bucket in neither recorded state: %d", both)
	if both > 0 {
		t.Errorf("a put and a delete in one bucket in one batch: readers saw both users %d times", both)
	}
}
