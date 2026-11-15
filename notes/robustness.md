# Robustness theorems and robustness tests (2026-11-15)

**Goal** (the user's): one framework, reused across programs, for (1) testing a distributed program
the way it runs for real -- real processes, a real network, real file systems -- with every fault made
by the environment, never by hooks in the program; and (2) stating what a proof of the program
establishes about exactly those runs. First user: `examples/raft/kvnet`. Branch `robustness`.

## The two halves

| | Go (test) | Lean (statement) |
|---|---|---|
| where | `examples/lib/robust` | lean_lib `Robustness` (`Robustness/*.lean`) |
| the system's nodes | the program's unchanged binary, a process per machine (`Machine.Start`) | `Deployment.sys`: each node's boot program (its Goose translation) and initial local state |
| clients, other hosts | goroutines dialing from client machines (`Machine.Dial`) | `Deployment.env`: **any** programs on other nodes; nothing proved of them |
| crashes | `Proc.Kill` (SIGKILL) then `SyncFS`, or `Disk.PowerLoss` (dm-flakey) | `RunStep.crash`: any node, any step, restart with its boot program from a state the extensions' crash relations allow (the file extension's power loss; a kill plus sync is one by its "Restarts" assumption) |
| network faults | the kernel, in a router namespace: iptables partitions (both ways or one way, drops or resets), tc netem (delay, jitter, loss, duplication, reordering); `NetNemesis` | the network semantics' nondeterminism (TCP: a direction cut at any read or write, any delay, a dial failing); `World.move` for a network whose semantics lacks a fault (none for TCP) |
| scheduling | the OS | any interleaving (a node started late is one not scheduled before) |
| what is checked | the driver's (kvnet: porcupine on the clients' history, convergence, the final whole-cluster crash) | `Robust`'s conclusion: every system node fine (`NodeOk`: no stuck thread, no unrecovered panic), and `Guarantee` of the observed trace |

## The Lean statement (`Robustness/`)

- `Run.lean` (trusted): `RunStep` = a thread step of any node | a crash of any node | a world move;
  `Run` collects the **trace**: for each step, the events `World.obs g g'` of its change of the shared
  state, stamped with the step's index and who made it (`Timed`, `Who`). Events come from the change
  of the shared state, not from a history kept in it: the network semantics of branch `net-tcp` keeps
  only observable state (the user's principle), and a step's change is observable.
- `Statement.lean` (trusted): `Robust W d bound Assume Guarantee`. **`Assume` sees only the
  environment's events** (`Deployment.envEvents`: those of the environment's nodes and of world
  moves, in order, without times), so it can constrain the clients and never what the system
  answers: the premise cannot be made false by the system's behavior (no vacuity through it).
- `Linearizability.lean` (trusted): `LinearizableTrace M h` for timed call/return events keyed by an
  operation's identity: well formed (a return follows a call; one input and one output per key:
  retries are one operation and its answers agree) and porcupine's `Theory.Linearizable` of the
  history with each operation from its first call to its first return, plus a chosen subset of the
  operations that never returned, open to the end (Herlihy and Wing's pending operations).
- `Stream.lean` (trusted): `StreamEv` (bytes written into a connection, by which end, to which
  address); the class `StreamNet` a network semantics instantiates (`obs`, `host`, `fresh`,
  `freshNode`; the header says how the TCP extension of `net-tcp` would); `World.ofStream` (no world
  moves); `ReqResp` and `opEvents`: a call when the dialer's bytes first decode as a complete request,
  a return when the acceptor's bytes first decode as a complete answer.

## kvnet's statement (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Robust.lean`)

`kvnetRobust prog : Prop`, a `def` (no proof, no `sorry`, no axiom): for every deployment of replica
processes running `prog cfg` (fresh directories, a fresh network whose plan puts each replica's
address at its host), with any environment nodes on other hosts, every run of fewer than `2^61` steps
whose environment satisfies `ClientsOk` -- no client speaks the peer protocol to a replica
(`NoPeerClaim`, the closed world: replicas do not authenticate raft messages) and no two read
requests share a sequence number (`ReadSeqsFresh`: a replica matches read answers to waiters by it)
-- leaves every replica fine and has a linearizable client history (`kvModel`, `kvProto`).

Decisions (the agent's, for review):
- **Proposals are identified by their whole payload**, which is what the replicas deduplicate on
  (`Replica.applyOp`'s `applied[string(data)]`): so no premise on proposal ids is needed. A client
  that sends one payload twice as two "different" operations gets one operation, answered alike.
- **A `Put`'s answer must be its value** (the replica answers a proposal with the key's value once
  applied). kvnet's Go model ignores a `Put`'s output; the statement is stronger.
- **Times**: a call at the client's last request byte, a return at the server's last answer byte:
  an interval inside what the client observes, so the guarantee is at least the client's.
- **Status, configuration changes and disruptions** are allowed from any client at any time and are
  not operations of the history (`ReqStatus` reads a replica's local state, stale by design).
- **`prog` is a parameter**: kvnet is not translated (`net` is names-only at this pin; its semantics
  is on branch `net-tcp`). The theorem to prove is `kvnetRobust (fun cfg => <the translation>)`. So is
  the network: `[StreamNet]`; the files: `[HasExt Fs.fsExt]` (durable's reimplementation over `os`,
  `notes/decisions.md`, "One file semantics, fsExt; power loss only").
- **Replicas started later** (the driver's ids 4-9) are nodes of the deployment from the start that
  the scheduler does not run before; **removed replicas** keep running, as in the test.

## The harness (`examples/lib/robust`)

The design follows `net-tcp`'s namespace tests (`examples/net/semantics/netns_helpers_test.go` on that
branch): every machine a network namespace with one veth to a **router namespace**, where every fault
is made (iptables `FORWARD`, tc netem on the router's interfaces), never in a machine's own chains (a
DROP in OUTPUT fails sends locally with EPERM: not a network fault); nothing is made in the host's
namespace. Root: a test or command re-executes itself with `sudo -n` (`RerunAsRoot`); without root,
`LocalNetwork` (one loopback address, no network faults). `TestNetworkFaults` checks the mechanism
(drop partitions stall, reset partitions refuse at once, one-way blocks, heal, a netem delay delays);
`TestPowerLoss` the disks.

kvnet: `go run ./raft/kvnet/cmd/kvnet check -rounds N` (from `examples/`; `-net auto` is namespaces when
`sudo -n` works, `-crash auto` mixed kills and power losses); `KVNET_NETNS=1 go test
./raft/kvnet/driver -run TestNetns`. The transport's random drops, delays, duplicates and cuts
(`Faults`) are gone. What stays in the program: the choices raft leaves the application, made at
random (durability orderings, snapshot and compaction points, `Config.Applied` at a restart, the tick):
they are the program's own nondeterminism, which the proof covers, not fault injection.

Results (2026-11-15): 10 rounds, namespaces, mixed crashes: porcupine `Ok` and convergence every
round; e.g. a round of 127 kills, 131 power losses, 127 partitions (36 one way, 44 isolating a
machine, 27 by resets) and 47 link-fault episodes.

## Next

- Instantiate `StreamNet` for the TCP extension when `net-tcp` lands, and check that `obs` gives one
  event per `"Write"` step (a write's suffix), none for reads, cuts and dials.
- A distributed adequacy theorem for `Run` (`goose_dist_crash_adequacy` plus world moves, plus an
  observation-preserving invariant connecting the trace to ghost state), then `kvnetRobust`'s proof
  from kvdurable's.
- A mutation check that only the network finds (e.g. a `Read` served without a read index: a stale
  read from a partitioned old leader).
- Other programs: the harness takes any binary; their statements reuse `Robust` with their own
  protocol (`ReqResp`) and model.
