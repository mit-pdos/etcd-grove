// Package kvnet is kvdurable's replicated key-value store on raft (examples/raft/kvdurable),
// with every replica a process of its own and the replicas connected by a real network: each
// replica listens on a TCP address and talks to its peers and its clients over net.Conn. Its test
// (package driver, command cmd/kvnet) crashes replicas for real.
//
// What it keeps from kvdurable: the store, its operations (Put and Get through the log, Read by a
// read index), its durable state (the raft storage written whole to one file of the durable
// package, by the replica's own image of it), every durability choice raft leaves the application
// made at random, snapshots and compaction in their own goroutine, configuration changes of every
// kind, leadership disruptions, and the restart's Config.Applied chosen at random.
//
// What changes:
//
//   - A replica is a process (RunNode), started with its id, every replica's address (one
//     comma-separated string, replica i at the i-th), its directory and the cluster's options, all
//     scalars and strings (the top-level theorem's programs: notes/kvnet-robust-goal.md). An
//     incarnation ends when the process is killed, or its machine loses power, or when a client
//     asks the replica to restart (ReqDisrupt): the process then stops it cleanly (its loop, clock
//     and snapshot goroutine, then raft's Node.Stop, then its transport) and starts the next one
//     from the file (Node.restart), as kvdurable's restarts do. A failed Listen is retried, never
//     a panic.
//   - Messages go over TCP (Transport): one connection per peer, dialed when needed, one frame
//     per message (a length, then the message encoded by hand, putMsg: no proto.Marshal); a
//     message that cannot be written is dropped and reported to raft (ReportUnreachable,
//     ReportSnapshot), never retried. The transport makes no fault of its own: the network's (a
//     connection refused while its target is down, reset when it crashes or by a middlebox,
//     stalled by a partition, a frame half written, packets delayed, lost, duplicated, reordered)
//     are the test environment's (examples/lib/robust).
//   - Clients are other processes: a request is one frame on a connection of its own, answered by
//     one frame (ReqPropose, ReqRead, ReqConf, ReqDisrupt, ReqStatus). The clients choose the
//     operations' ids and the reads' sequence numbers, and never reuse one. The checking client,
//     the test's driver and the theorem's, is package kvcheck.
//
// The faults the test makes (package driver, over the harness examples/lib/robust), all from
// outside the program: every replica on a machine of its own (a network namespace), the network
// partitioned (both ways or one way, by drops or resets) and degraded (delay, loss, duplication,
// reordering) by the kernel in a router namespace; a replica's process killed (SIGKILL) at any
// point of its work, and then either its filesystem synced before it restarts (the restart the
// Linux file extension's semantics allows: notes/decisions.md, "One file semantics, fsExt; power
// loss only"), or its machine's disk losing power (an ext4 filesystem of its own on a dm-flakey
// device that drops what was not durable). At the end, the whole cluster crashes at once.
//
// Not yet verified: the proof waits for a semantics of the network (net.Listen, Accept,
// DialTimeout, a Conn's Read, Write, deadlines and Close; branch net-tcp). Its statement is
// stated: Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Robust.lean's kvnetRobust,
// over the Lean library Robustness (notes/robustness.md).
package kvnet
