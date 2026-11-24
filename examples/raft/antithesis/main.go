package antithesis

import "github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"

// Main is the closed program (notes/antithesis-check-design.md §1): it runs a cluster of
// DefaultConfig (its random choices primitive.RandomUint64's), checks its stream against
// Antithesis's model of raft (check.Run: EtcdBinding.tla with EtcdBindingEmpty.cfg's constants:
// the nodes are the servers and the voters, logs start empty), and panics unless the stream is
// accepted. check.Run panics itself where TLC would stop with an evaluation error.
func Main() {
	c := RunCluster(DefaultConfig())
	cfg := &check.Config{Server: c.Servers(), InitVoters: c.Servers(), Bootstrapped: false}
	if check.Run(cfg, c.Events()).Kind != check.Accepted {
		panic("antithesis: the stream is not accepted by Antithesis's model of raft")
	}
}
