package auth

import (
	"errors"
	"time"

	"go.uber.org/zap"

	etcdauth "go.etcd.io/etcd/server/v3/auth"
)

// REQ auth/boot: the server's boot builds a provider from --auth-token (an error for options it
// does not accept, which NewServer returns) and a store over the member's backend; the store is
// at the backend's auth state, with revision 1 for a fresh backend, and serves checks at once.
// Users: server/etcdserver/server.go:~360-369 (NewServer: NewTokenProvider, NewAuthStore).
// Assumes: be's auth buckets hold a state the cluster reached (a fresh backend: the initial
// state; a restart: the state at the consistent index), its permissions valid and its records
// fitting; waiter is the server's applyWait.Wait; a jwt kind's keys are the cluster's
// (jwtTokOk).
// Specs: NewTokenProvider.spec, NewAuthStore.spec, authStore.Revision.spec, IsAuthEnabled.spec.
func ReqBoot(lg *zap.Logger, be etcdauth.AuthBackend, opts string, waiter func(uint64) <-chan struct{},
	ttl time.Duration, cost int) (etcdauth.AuthStore, error) {
	tp, err := etcdauth.NewTokenProvider(lg, opts, waiter, ttl)
	if err != nil {
		if !errors.Is(err, etcdauth.ErrInvalidAuthOpts) && opts != "jwt" && (len(opts) < 4 || opts[:4] != "jwt,") {
			panic("boot: a provider error other than invalid options, for a non-JWT kind")
		}
		return nil, err
	}
	as := etcdauth.NewAuthStore(lg, be, tp, cost)
	if as.Revision() == 0 {
		panic("boot: a store at revision 0")
	}
	_ = as.IsAuthEnabled()
	return as, nil
}

// REQ auth/recover: installing a snapshot moves the store to the snapshot backend's state, a
// successor of its own: the revision does not go back.
// Users: server.go:1127 (applySnapshot: s.authStore.Recover(schema.NewAuthBackend(lg, newbe))).
// Assumes: the apply thread (authCur); newbe's auth state follows the store's (AuthReach: the
// snapshot is at a later index of the committed log), is reached, its permissions valid.
// Specs: authStore.Recover.spec, Revision.spec; laws: authCur_at, authAt_le, authAt_reach.
func ReqRecover(as etcdauth.AuthStore, newbe etcdauth.AuthBackend) {
	r0 := as.Revision()
	as.Recover(newbe)
	if as.Revision() < r0 {
		panic("recover: the auth revision went back")
	}
}

// REQ auth/close: the server's cleanup closes the store, which never fails; a token check after
// it is refused or finds auth off, never a panic.
// Users: server.go:953 (Cleanup).
// Specs: authStore.Close.spec, IsAuthEnabled.spec.
func ReqCloseAfterStop(as etcdauth.AuthStore) {
	if err := as.Close(); err != nil {
		panic("close: Close returned an error")
	}
	_ = as.IsAuthEnabled()
}
