// Package robust runs a distributed program's robustness test the way the program runs for real,
// with the environment, not the program, making the faults. The program under test is its own
// binary, unchanged: no fault injection in its code, no hooks to make interesting executions more
// likely. This package makes everything around it:
//
//   - Machines (Network, Machine): each a network namespace with its own address, joined by a
//     router namespace that is the network. Processes are started on a machine (Machine.Start)
//     and clients dial from one (Machine.Dial), so every byte between two machines crosses the
//     router.
//   - The network's faults, made in the router by the kernel: partitions, both ways or one way,
//     whose packets are dropped (connections stall and time out) or refused with TCP resets
//     (Network.SetBlocks, Partition); and link faults, tc netem's delay, jitter, loss,
//     duplication and reordering of the packets to a machine (Network.SetLink). NetNemesis makes
//     them at random.
//   - Crashes: a process killed with SIGKILL at any point (Proc.Kill), then either its machine's
//     filesystem synced before the restart (SyncFS: the restart the Linux file extension's
//     "Restarts" assumption allows), or its machine's disk losing power (Disk: an ext4 of its own
//     on dm-flakey, which loses whatever was not durable).
//   - Process management: a process that ends without being killed is a failure of the
//     program (Start's onExit).
//   - A deployment's run (Run, run.go): its processes started on their machines, each with its
//     log; the processes of machines that crash (Restartable, in Groups) killed at random and
//     restarted on the same directory; the processes of machines that never crash (Client):
//     those that serve until killed, and orchestrators, each marking its set-up done by a file,
//     whose end the run waits for; the faults started only once every orchestrator's set-up is
//     done (RunClients, RunFaults); the run's first failure (Fail, Err, Failed) and what it made
//     (Stats, NetStats). Config says which faults, how often, and the deadline.
//   - Small helpers for a deployment's tests (util.go): the network or the local mode
//     (NewNetworkOrLocal), a test run again where it can make namespaces (RerunTest), Symlink,
//     Tail. Nothing here is for the machines' programs, which never import this package.
//
// What a run checks (linearizability of the clients' operations, convergence, durability across
// a whole-cluster crash) is the program's business (its orchestrators' checks, which panic); the
// faults are this package's.
//
// The faults are the ones the robustness theorems' executions allow (Lean library Robustness,
// notes/robustness.md): a machine's crash at any step, its restart with the same program, the
// network's nondeterminism (a TCP direction cut at any read or write, any delay), and clients
// that are arbitrary programs on other machines.
//
// Root. Namespaces, iptables, tc and disks need root: a test or command re-executes itself as
// root (RerunAsRoot, sudo -n), as examples/net/semantics' namespace tests do on branch net-tcp.
// Without root, a LocalNetwork puts every machine on one loopback address, with no network
// faults (kills only).
package robust
