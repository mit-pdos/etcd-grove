package antithesis

import "github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"

// Main is the closed program (notes/antithesis-check-design.md §1): it draws the run's mode
// (DrawMode within MainScope: the binding's constants and every simulator flag the scope allows,
// primitive.RandomUint64's choices), runs a cluster in it with DefaultConfig's pacing, checks its
// stream against Antithesis's model of raft (check.Run: EtcdBinding.tla with the run's Server, InitVoters and Bootstrapped), and
// panics unless the stream is accepted. check.Run panics itself where TLC would stop with an
// evaluation error.
func Main() {
	c := RunCluster(DefaultConfig(), DrawMode(MainScope()))
	if check.Run(c.CheckConfig(), c.Events()).Kind != check.Accepted {
		panic("antithesis: the stream is not accepted by Antithesis's model of raft")
	}
}
