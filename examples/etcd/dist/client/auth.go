package client

import (
	"context"
	"time"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The users' passwords (authkv's SetUp's; unexported there).
const (
	rootPw = "root-pw"
	uPw    = "u-pw"
	vPw    = "v-pw"
)

// newUserClient (authN's, copied) connects a client of addr that authenticates as user name with
// password pw (clientv3.New calls Authenticate when it dials; the token is sent with every
// request).
func newUserClient(addr string, name string, pw string) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints:            []string{addr},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Username:             name,
		Password:             pw,
		Logger:               zap.NewNop(),
	})
}

// barrier (authN's, copied) makes root's linearizable read of z/barrier through a new client of
// addr (its read index is at least the set-up's AuthEnable, so the member has applied it when the
// read returns), and reports whether it succeeded.
func barrier(addr string) bool {
	root, err := newUserClient(addr, "root", rootPw)
	if err != nil {
		return false
	}
	defer root.Close()
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = root.Get(ctx, "z/barrier")
	cancel()
	return err == nil
}

// barriers runs barrier at every endpoint, and reports whether every one succeeded (authlease's
// barriers, copied).
func barriers(eps []string) bool {
	for _, a := range eps {
		if !barrier(a) {
			return false
		}
	}
	return true
}

// collectFor reads wch with etcdstart.Collect up to upTo, giving up (its context cancelled, an
// end, not a check) after readTimeout.
func collectFor(wch clientv3.WatchChan, cancel context.CancelFunc, upTo int64) ([]etcdstart.Event, bool) {
	t := time.AfterFunc(readTimeout, cancel)
	evs, ok := etcdstart.Collect(wch, upTo)
	t.Stop()
	cancel()
	return evs, ok
}

// RunAuth is the auth workload (authN's run minus its members' gRPC serving, copied; Lean:
// Workload.auth; alone in its deployment, which has the token provider): through a client of
// eps[0], authkv's set-up (auth.SetUp: the auth state set up and auth enabled); root's barrier at
// every member; then the four principals' workloads at once, each at its own machine (nodes[c] is
// auth.Principals()[c]'s: remotePrincipals, NodeMain) through its own client (auth.Work): the
// client with no token through eps[0], u and the client with an invalid token through eps[1 mod k],
// v through eps[2 mod k] (principalClient); then root's Put of z/end, root's
// watch of everything from revision 1 up to it, checked by auth.CheckHistory (every write one its
// principal was permitted), and u's watch of [a, b), whose events must all be keys u may read.
// Every refusal the checks expect is any error (auth.Work's refused): an error never counts as a
// write not applied, since the history check reads what was applied.
func RunAuth(eps []string, nodes []string, ready func()) Result {
	k := len(eps)
	a0, au := eps[0], eps[1%k]
	cli, err := newClient([]string{a0})
	if err != nil {
		return ended("auth: a client failed to connect")
	}
	if !auth.SetUp(cli) {
		return ended("auth: the set-up failed")
	}
	if !barriers(eps) {
		return ended("auth: a barrier failed")
	}
	root, err := newUserClient(a0, "root", rootPw)
	if err != nil {
		return ended("auth: root's client failed to connect")
	}
	ucli, err := newUserClient(au, "u", uPw)
	if err != nil {
		return ended("auth: u's client failed to connect")
	}
	if !AwaitAccept(nodes) {
		return ended("auth: a principal's machine never answered")
	}
	ready()
	remotePrincipals(nodes)
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	end, err := root.Put(ctx, "z/end", "end")
	cancel()
	if err != nil {
		return ended("auth: root's last Put failed")
	}
	hctx, hcancel := context.WithCancel(context.Background())
	hch := root.Watcher.Watch(hctx, "", clientv3.WithPrefix(), clientv3.WithRev(1))
	evs, ok := collectFor(hch, hcancel, end.Header.Revision)
	if !ok {
		return ended("auth: root's watch ended")
	}
	auth.CheckHistory(evs, "z/end")
	uctx, ucancel := context.WithCancel(context.Background())
	uch := ucli.Watcher.Watch(uctx, "a", clientv3.WithRange("b"), clientv3.WithRev(1))
	uevs, ok := collectFor(uch, ucancel, auth.LastIn(evs))
	if !ok {
		return ended("auth: u's watch ended")
	}
	for _, e := range uevs {
		if !auth.Permitted("u", e.Key) {
			panic("dist auth: u's watch reported a key u may not read")
		}
	}
	return checked()
}
