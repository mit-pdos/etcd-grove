// Package robust runs a distributed program's robustness test the way the program runs for real,
// with the environment, not the program, making the faults. The program under test is its own
// binary, unchanged: no fault injection in its code, no hooks to make interesting executions more
// likely. The harness owns everything around it:
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
//   - Process management: a process that ends without the harness killing it is a failure of
//     the program (Start's onExit).
//
// What the harness checks (linearizability of the clients' operations, convergence, durability
// across a whole-cluster crash) is the program's driver's business; the faults are this
// package's.
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
