# Robustness theorems and robustness tests (2026-11-15)

**Goal** (the user's): one framework, reused across programs, for (1) testing a distributed program
the way it runs for real -- real processes, a real network, real file systems -- with every fault made
by the environment, never by hooks in the program; and (2) stating what a proof of the program
establishes about exactly those runs. First user: `examples/raft/kvnet`. Branch `robustness`.

## The two halves

| | Go (test) | Lean (statement) |
|---|---|---|
| where | `examples/lib/robust` | lean_lib `Robustness` (`Robustness/*.lean`) |
| the system's nodes | the program's unchanged binary, a process per machine (`Machine.Start`) | `Robust`'s `sys`: each node's boot program (its Goose translation) and initial local state |
| clients, other hosts | goroutines dialing from client machines (`Machine.Dial`) | `Robust`'s `env`: **any** programs on other nodes of the same distributed system; nothing proved of them |
| crashes | `Proc.Kill` (SIGKILL) then `SyncFS`, or `Disk.PowerLoss` (dm-flakey) | `DistCrashStep.crash`: any node, any step, restart with its boot program from a state the extensions' crash relations allow (the file extension's power loss; a kill plus sync is one by its "Restarts" assumption) |
| network faults | the kernel, in a router namespace: iptables partitions (both ways or one way, drops or resets), tc netem (delay, jitter, loss, duplication, reordering); `NetNemesis` | the TCP semantics' nondeterminism (a direction cut at any read or write, any delay, a dial failing) |
| scheduling | the OS | any interleaving (a node started late is one not scheduled before) |
| what is checked | the driver's (kvnet: porcupine on the clients' history, convergence, the final whole-cluster crash) | `Robust`'s conclusion: every system node fine (`NodeOk`: no stuck thread, no unrecovered panic), and `Guarantee` of the shared state over time |

## The Lean statement (`Robustness/`)

Redone 2026-11-15 (the user's: the first version introduced concepts it did not need, a "world"
among them; use GooseLang's existing transition relation; keep the trust base small). The statement
has **no semantics of its own**: the transition relation is Perennial's `DistCrashStep`
(`DistLang.lean`: a thread step of a node, or a node's crash and restart), the one
`goose_dist_crash_adequacy` is about.

- `Statement.lean` (trusted, four definitions):
  - `IsRun boots cs`: `cs[j+1]` is a `DistCrashStep` from `cs[j]`. Proved equal to the executions of
    `DistCrashNsteps` with the intermediate configurations kept (`IsRun.nsteps`, `IsRun.of_nsteps`,
    not trusted), so `NodeOk` at a run's end is the adequacy theorem's conclusion as it stands.
  - `envSteps k cs`: the changes `(g, g')` of the shared state by the steps that leave the first `k`
    nodes (the system's) as they were. This is how a step is attributed without labels:
    `DistCrashStep` does not say which node stepped. (A system node's step that changed neither its
    threads nor its local state would be counted as the environment's: only an extension's stutter
    does that, and it changes nothing.)
  - `NodeOk`, and `Robust sys env g bound Assume Guarantee`: for every run of `sys ++ env` from `g`
    of fewer than `bound` steps, `Assume (envSteps …)` implies `NodeOk` of every system node at the
    end and `Guarantee` of the run's global states (the index is the time). **`Assume` sees only the
    environment's steps**, so it can constrain the clients and cannot mention a step the system took.
- `Linearizability.lean` (trusted, unchanged): `LinearizableTrace M h` for timed call/return events
  keyed by an operation's identity: well formed (a return follows a call; one input and one output
  per key: retries are one operation and its answers agree) and porcupine's `Theory.Linearizable` of
  the history with each operation from its first call to its first return, plus a chosen subset of
  the operations that never returned, open to the end (Herlihy and Wing's pending operations).
- `Stream.lean` (trusted): over the TCP extension's state (`GooseLang/Ext/Tcp/Impl.lean`), not a
  class. `StreamEv` (bytes written into a connection, by which end, to which address); `tcpObs g g'`:
  the events of a change of the network, read off the state because it keeps only what is
  observable (the user's principle: no history): a direction whose unread bytes grew by a suffix had
  that suffix written (`appended`; a read removes a prefix, a cut keeps one: `appended_write`,
  `appended_read`); `streamTrace` (the events of a run's global states, with their step's index),
  `envStream` (those of the environment's steps); `ReqResp` and `opEvents` as before: a call when
  the dialer's bytes first decode as a complete request, a return when the acceptor's bytes first
  decode as a complete answer.

What went away, and why it was not needed: `World` (`move`: empty for TCP, whose semantics has every
fault; `obs`: now `tcpObs`, applied by the instance), `Who` and `Timed` (a time is an index; who
stepped is `envSteps`), `RunStep`/`Run` (a copy of `DistCrashStep` with labels and a trace),
`Deployment` and its five functions (two lists and a global state), the class `StreamNet` (`obs`,
`host`, `fresh`, `freshNode`: an instance to be trusted later; now the extension's own fields).

## kvnet's statement (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Robust.lean`)

`kvnetRobust prog : Prop`, a `def` (no proof, no `sorry`, no axiom): for every deployment of replica
processes running `prog cfg` (fresh directories, no listener, a fresh network -- `FreshNet`: a
well-formed plan, `Tcp.PlanWellFormed`, and no connection -- whose plan puts each replica's
address at its host), with any environment nodes on other hosts with no listener at the start
(`EnvStart`; without that, an environment node could start with an open listener at a replica's
address and accept its clients and peers: the first version's statement allowed it), every run of
fewer than `2^61` steps
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
- **`prog` is a parameter**: kvnet is not translated. The theorem to prove is
  `kvnetRobust (fun cfg => <the translation>)`. The extensions are any list with the TCP extension
  (`[HasExt Tcp.tcpExt]`) and the files' (`[HasExt Fs.fsExt]`: durable's reimplementation over `os`,
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

- A sanity lemma that a `Tcp.WriteStep` into an open direction has exactly one event, its bytes, and
  every other step of the extension none (`tcpObs` over `GMap.toList` of `setConn`).
- A distributed adequacy theorem with unverified nodes: `goose_dist_crash_adequacy` asks a WP of
  every node; `Robust` needs the environment's nodes to run any program, constrained only through
  `Assume` on their steps' changes of the network, plus an invariant connecting the network's state
  over time to ghost state (the trace is not in the state). Then `kvnetRobust`'s proof from
  kvdurable's. This is where the statement's shape will be tested; nothing is proved of it yet.
- Whether `DistStep` should carry the stepping node's index in Perennial (it would make `envSteps`
  a filter on labels): a general change, to propose there on its own.
- A mutation check that only the network finds (e.g. a `Read` served without a read index: a stale
  read from a partitioned old leader).
- Other programs: the harness takes any binary; their statements reuse `Robust` with their own
  protocol (`ReqResp`) and model.
