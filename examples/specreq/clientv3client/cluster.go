package clientv3client

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3client/memberlist-linearizable: a linearizable member list contains a member the
// caller added (an acknowledged MemberAdd), unless it was removed since (by another principal).
// Users: client.go's Sync (the endpoints), etcdctl member list, the e2e tests.
// Assumes: no principal removes members (the owner's invariant); the caller holds the peer-URL
// right urlsRight γ [peerURL] (from 2e's urls_reserve, which reserves the URL's host and spends a
// share of urlsReserve).
// Specs: cluster.MemberAdd.spec, cluster.MemberList.spec; model: clusterStep; laws: 3h's unfold of
// replyOwn for .memberAdd and .memberList (req/go_etcd_io_etcd_api_v3_etcdserverpb.md, from 1c).
func ReqMemberAddThenList(ctx context.Context, cli *clientv3.Client, peerURL string) {
	add, err := cli.Cluster.MemberAdd(ctx, []string{peerURL})
	if err != nil {
		return
	}
	if add.Member == nil {
		panic("memberlist: no member in MemberAdd's reply")
	}
	l, err := cli.Cluster.MemberList(ctx)
	if err != nil {
		return
	}
	for _, m := range l.Members {
		if m.ID == add.Member.ID {
			return
		}
	}
	panic("memberlist: added member missing")
}

// (No snippet for Sync or auto-sync: out of the top-level workloads, the coordinator's decision on
// issues/etcd-client-resolver-build-race.md; Client.Sync.spec takes resolverIdle, which no caller
// after New holds.)
