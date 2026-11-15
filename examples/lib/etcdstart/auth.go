package etcdstart

import (
	"net"
	"net/http"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"
)

// StartMemberAuth starts member name of a new cluster with auth on (examples/etcd/auth3's
// startMember at any token and snapshot settings): its configuration authkv's (the simple token
// provider, etcd's default token TTL of 300 seconds), the cluster's initial members' peer URLs
// cluster and token token, its peer URLs peer (the one URL http://peerAddr), its one client URL
// http://client, the snapshot settings snapCount and catchUp, no auto-compactor; it serves the
// member's raft handler on a listener at peerAddr, then starts the member.
func StartMemberAuth(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, token string, snapCount uint64, catchUp uint64,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:                   name,
		DataDir:                name + ".etcd",
		InitialPeerURLsMap:     cluster,
		PeerURLs:               peer,
		ClientURLs:             types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken:    token,
		NewCluster:             true,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          snapCount,
		SnapshotCatchUpEntries: catchUp,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		AuthToken:              "simple",
		TokenTTL:               300,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate(name, lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return nil, err
	}
	// the member's peer URL is served by its own transport (D21b's deployment fact)
	l, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	go http.Serve(l, s.RaftHandler())
	s.Start()
	return s, nil
}

// StartMembersAuth is StartMembers with auth on: the members ms of a new cluster with token token
// and the snapshot settings snapCount and catchUp, the initial cluster's map (each member's name to
// its one peer URL http://Peer), then StartMemberAuth for each member in order. It returns the
// started servers, in the members' order, or the first error (the members started before it keep
// running).
func StartMembersAuth(ms []Member, token string, snapCount uint64, catchUp uint64,
	lg *zap.Logger) ([]*etcdserver.EtcdServer, error) {
	cluster := types.URLsMap{}
	for _, m := range ms {
		cluster[m.Name] = types.URLs{{Scheme: "http", Host: m.Peer}}
	}
	srvs := make([]*etcdserver.EtcdServer, len(ms))
	for j, m := range ms {
		s, err := StartMemberAuth(m.Name, cluster[m.Name], m.Peer, m.Client, cluster, token,
			snapCount, catchUp, lg)
		if err != nil {
			return nil, err
		}
		srvs[j] = s
	}
	return srvs, nil
}
