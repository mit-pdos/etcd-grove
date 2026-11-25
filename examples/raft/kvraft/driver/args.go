package driver

import (
	"flag"
	"fmt"
	"strconv"

	"github.com/mit-pdos/etcd-grove/examples/raft/kvraft"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvraft/kvcheck"
)

// The processes the harness starts: a replica (kvraft.RunNode) and the checking client
// (kvcheck.Check), each the first argument of its command line, the rest its flags.
const (
	RoleNode   = "node"
	RoleClient = "client"
)

// The replicas' transports for their raft messages (NodeArgs' -transport flag; the clients' requests
// always go over TCP).
const (
	TransportTCP = "tcp" // kvraft.RunNode: a TCP connection per peer (the default)
	TransportUDP = "udp" // kvraft.RunNodeUDP: datagrams (kvraft-udp)
)

// NodeArgs is the command line of replica id's process: kvraft.RunNode's arguments as flags.
func NodeArgs(id uint64, addrs, dir string, o kvraft.Options) []string {
	return []string{
		RoleNode, "-id", strconv.FormatUint(id, 10), "-addrs", addrs, "-dir", dir,
		"-voters", strconv.FormatUint(o.Voters, 10), fmt.Sprintf("-prevote=%v", o.PreVote),
		fmt.Sprintf("-checkquorum=%v", o.CheckQuorum), fmt.Sprintf("-stepdown=%v", o.StepDownOnRemoval),
		"-maxsize", strconv.FormatUint(o.MaxSizePerMsg, 10),
		"-maxcommitted", strconv.FormatUint(o.MaxCommittedSizePerReady, 10),
		"-maxinflight", strconv.Itoa(o.MaxInflightMsgs),
	}
}

// ClientArgs is the command line of the checking client's process: kvcheck.Check's arguments.
func ClientArgs(addrs string, voters uint64) []string {
	return []string{RoleClient, "-addrs", addrs, "-voters", strconv.FormatUint(voters, 10)}
}

// RunProcess runs the process args describe (NodeArgs, ClientArgs: the role first): it calls
// kvraft.RunNode or kvcheck.Check with the arguments the flags give, and returns only if the
// process's work is over (the client's check passed) or the command line is bad (an error).
func RunProcess(args []string) error {
	if len(args) < 1 {
		return fmt.Errorf("kvraft: no role")
	}
	fs := flag.NewFlagSet(args[0], flag.ContinueOnError)
	addrs := fs.String("addrs", "", "every replica's address, comma-separated (replica i at the i-th)")
	voters := fs.Uint64("voters", 0, "the bootstrap configuration's voters (ids 1 to voters)")
	switch args[0] {
	case RoleNode:
		id := fs.Uint64("id", 0, "the replica's id")
		dir := fs.String("dir", "", "the directory of its durable file")
		preVote := fs.Bool("prevote", false, "raft's PreVote")
		checkQuorum := fs.Bool("checkquorum", false, "raft's CheckQuorum")
		stepDown := fs.Bool("stepdown", false, "raft's StepDownOnRemoval")
		maxSize := fs.Uint64("maxsize", 0, "raft's MaxSizePerMsg")
		maxCommitted := fs.Uint64("maxcommitted", 0, "raft's MaxCommittedSizePerReady")
		maxInflight := fs.Uint64("maxinflight", 256, "raft's MaxInflightMsgs")
		transport := fs.String("transport", TransportTCP, "the raft messages' transport: tcp (kvraft.RunNode) or udp (kvraft.RunNodeUDP)")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		if *transport == TransportUDP {
			kvraft.RunNodeUDP(*id, *addrs, *dir, *voters, *preVote, *checkQuorum, *stepDown, *maxSize, *maxCommitted, *maxInflight)
			return nil
		}
		if *transport != TransportTCP {
			return fmt.Errorf("kvraft: unknown transport %q", *transport)
		}
		kvraft.RunNode(*id, *addrs, *dir, *voters, *preVote, *checkQuorum, *stepDown, *maxSize, *maxCommitted, *maxInflight)
		return nil
	case RoleClient:
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		kvcheck.Check(*addrs, *voters)
		return nil
	}
	return fmt.Errorf("kvraft: unknown role %q", args[0])
}
