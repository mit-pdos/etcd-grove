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
//   - A replica is a process (RunNode), started with its id, its directory, every replica's
//     address and the cluster's options (NodeConfig, NodeArgs). An incarnation is a process: it
//     never stops itself; it ends when the process is killed, or its machine loses power.
//   - Messages go over TCP (Transport): one connection per peer, dialed when needed, one frame
//     per message (a length, then the message encoded by hand, putMsg: no proto.Marshal); a
//     message that cannot be written is dropped and reported to raft (ReportUnreachable,
//     ReportSnapshot), never retried. On top of the real network's faults (a connection refused
//     while its target is down, reset when it crashes, a frame half written), the transport may
//     drop, delay, duplicate messages and cut connections at random (Faults).
//   - Clients are other processes: a request is one frame on a connection of its own, answered by
//     one frame (ReqPropose, ReqRead, ReqConf, ReqDisrupt, ReqStatus). The clients choose the
//     operations' ids and the reads' sequence numbers, and never reuse one.
//
// The crashes the test makes (package driver): a replica's process is killed (SIGKILL) at any
// point of its work, and then either its filesystem is synced before it restarts (the restart the
// Linux file extension's semantics allows: notes/decisions.md, "One file semantics, fsExt; power
// loss only"), or its machine's disk loses power (an ext4 filesystem of its own on a dm-flakey
// device that drops what was not durable). At the end, the whole cluster crashes at once.
//
// Not yet verified: the proof waits for a semantics of the network (net.Listen, Accept,
// DialTimeout, a Conn's Read, Write, deadlines and Close) and of processes
// (notes/kvnet.md).
package kvnet
