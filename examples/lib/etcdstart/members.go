package etcdstart

import (
	"strconv"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"
)

// Member is one member of a new cluster: its name, its peer address (its one peer URL is
// http://Peer, served by its raft handler) and its client address (a plain host:port).
type Member struct {
	Name   string
	Peer   string
	Client string
}

// Members returns the k members of a new cluster named pfx: member i (from 0) is named
// pfx-i, with peer address 127.0.0.1:(peerBase+i) and client address 127.0.0.1:(clientBase+i),
// the numbers in decimal (strconv.FormatUint).
func Members(pfx string, k uint64, peerBase uint64, clientBase uint64) []Member {
	ms := make([]Member, k)
	for i := uint64(0); i < k; i++ {
		ms[i] = Member{
			Name:   pfx + "-" + strconv.FormatUint(i, 10),
			Peer:   "127.0.0.1:" + strconv.FormatUint(peerBase+i, 10),
			Client: "127.0.0.1:" + strconv.FormatUint(clientBase+i, 10),
		}
	}
	return ms
}

// StartMembers starts the members ms of a new cluster with token token and the snapshot settings
// snapCount and catchUp (NewMember's; NoSnapCount and NoSnapCatchUp for an example that does not
// exercise snapshots): the initial cluster's map (each member's name to its one peer URL
// http://Peer), then, for each member in order, NewMember and the server started (StartMember's
// steps, at the given snapshot settings). It returns the started servers, in the members' order,
// or the first error (the members started before it keep running).
func StartMembers(ms []Member, token string, snapCount uint64, catchUp uint64,
	lg *zap.Logger) ([]*etcdserver.EtcdServer, error) {
	cluster := types.URLsMap{}
	for _, m := range ms {
		cluster[m.Name] = types.URLs{{Scheme: "http", Host: m.Peer}}
	}
	srvs := make([]*etcdserver.EtcdServer, len(ms))
	for j, m := range ms {
		s, err := NewMember(m.Name, cluster[m.Name], m.Peer, m.Client, cluster, token, snapCount,
			catchUp, lg)
		if err != nil {
			return nil, err
		}
		s.Start()
		srvs[j] = s
	}
	return srvs, nil
}
