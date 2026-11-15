package kvnet

import (
	"flag"
	"fmt"
	"strconv"
	"strings"
)

// NodeArgs is cfg as the command-line arguments of a node's process (ParseNodeArgs reads them
// back).
func NodeArgs(cfg NodeConfig) []string {
	var addrs []string
	for id, a := range cfg.Addrs {
		addrs = append(addrs, fmt.Sprintf("%d=%s", id, a))
	}
	o, f := cfg.Opts, cfg.Faults
	return []string{
		"-id", itoa(cfg.ID), "-dir", cfg.Dir, "-addrs", strings.Join(addrs, ","),
		"-voters", itoa(o.Voters), fmt.Sprintf("-prevote=%v", o.PreVote),
		fmt.Sprintf("-checkquorum=%v", o.CheckQuorum), fmt.Sprintf("-stepdown=%v", o.StepDownOnRemoval),
		"-maxsize", itoa(o.MaxSizePerMsg), "-maxcommitted", itoa(o.MaxCommittedSizePerReady),
		"-maxinflight", strconv.Itoa(o.MaxInflightMsgs),
		"-drop", itoa(f.Drop), "-delay", itoa(f.Delay), "-dup", itoa(f.Duplicate), "-cut", itoa(f.Cut),
	}
}

// ParseNodeArgs reads back what NodeArgs wrote.
func ParseNodeArgs(args []string) (NodeConfig, error) {
	var cfg NodeConfig
	fs := flag.NewFlagSet("node", flag.ContinueOnError)
	fs.Uint64Var(&cfg.ID, "id", 0, "the replica's id")
	fs.StringVar(&cfg.Dir, "dir", "", "the directory of its durable file")
	addrs := fs.String("addrs", "", "every replica's address: id=host:port,...")
	fs.Uint64Var(&cfg.Opts.Voters, "voters", 0, "the bootstrap configuration's voters (ids 1 to voters)")
	fs.BoolVar(&cfg.Opts.PreVote, "prevote", false, "raft's PreVote")
	fs.BoolVar(&cfg.Opts.CheckQuorum, "checkquorum", false, "raft's CheckQuorum")
	fs.BoolVar(&cfg.Opts.StepDownOnRemoval, "stepdown", false, "raft's StepDownOnRemoval")
	fs.Uint64Var(&cfg.Opts.MaxSizePerMsg, "maxsize", 0, "raft's MaxSizePerMsg")
	fs.Uint64Var(&cfg.Opts.MaxCommittedSizePerReady, "maxcommitted", 0, "raft's MaxCommittedSizePerReady")
	fs.IntVar(&cfg.Opts.MaxInflightMsgs, "maxinflight", 256, "raft's MaxInflightMsgs")
	fs.Uint64Var(&cfg.Faults.Drop, "drop", 0, "drop a message one time in N (0: never)")
	fs.Uint64Var(&cfg.Faults.Delay, "delay", 0, "delay a message one time in N")
	fs.Uint64Var(&cfg.Faults.Duplicate, "dup", 0, "duplicate a message one time in N")
	fs.Uint64Var(&cfg.Faults.Cut, "cut", 0, "close a connection after a message one time in N")
	if err := fs.Parse(args); err != nil {
		return cfg, err
	}
	cfg.Addrs = make(map[uint64]string)
	for _, kv := range strings.Split(*addrs, ",") {
		id, a, ok := strings.Cut(kv, "=")
		n, err := strconv.ParseUint(id, 10, 64)
		if !ok || err != nil {
			return cfg, fmt.Errorf("kvnet: bad -addrs entry %q", kv)
		}
		cfg.Addrs[n] = a
	}
	if cfg.ID == 0 || cfg.Dir == "" || cfg.Addrs[cfg.ID] == "" || cfg.Opts.Voters == 0 {
		return cfg, fmt.Errorf("kvnet: -id, -dir, -voters and the replica's own address are required")
	}
	if cfg.Opts.MaxSizePerMsg == 0 && cfg.Opts.MaxCommittedSizePerReady == 0 {
		return cfg, fmt.Errorf("kvnet: -maxsize and -maxcommitted both 0 (raft panics)")
	}
	return cfg, nil
}
