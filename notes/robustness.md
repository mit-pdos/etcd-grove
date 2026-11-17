# Robustness theorems and robustness tests (2026-11-15)

**Goal** (the user's): one framework, reused across programs, for (1) testing a distributed program
the way it runs for real -- real processes, a real network, real file systems -- with every fault made
by the environment, never by hooks in the program; and (2) stating what a proof of the program
establishes about exactly those runs. First user: `examples/raft/kvnet`. Branch `robustness`.

## The two halves

| | Go (test) | Lean (statement) |
|---|---|---|
| where | `examples/lib/robust` | lean_lib `Robustness` (`Robustness/Statement.lean`) |
| the system's nodes | the program's unchanged binary, a process per machine (`Machine.Start`) | `Robust`'s `crashing`: each machine's program (its Goose translation) and initial local state |
| clients | goroutines dialing from client machines (`Machine.Dial`) | `Robust`'s `stable`: programs on machines that never crash (a client that records its history and checks it) |
| crashes | `Proc.Kill` (SIGKILL) then `SyncFS`, or `Disk.PowerLoss` (dm-flakey) | `DistCrashStep.crash`: any machine of `crashing`, any step, restart with its program from a state the extensions' crash relations allow (the file extension's power loss; a kill plus sync is one by its "Restarts" assumption) |
| network faults | the kernel, in a router namespace: iptables partitions (both ways or one way, drops or resets), tc netem (delay, jitter, loss, duplication, reordering); `NetNemesis` | the plugged-in extension's nondeterminism (TCP: a direction cut at any read or write, any delay, a dial failing) |
| scheduling | the OS | any interleaving (a machine started late is one not scheduled before) |
| what is checked | the driver's (kvnet: porcupine on the clients' history, convergence, the final whole-cluster crash) | no thread of any machine stuck or with a top-level panic; so whatever a program checks before panicking |

## The Lean statement (`Robustness/Statement.lean`)

One trusted definition (2026-11-17, the user's: "if you run machines running code [e1, ..., en] on
machines that never crash and [e1', ..., em'] on machines that crash and restart (and with whatever
extensions you choose to plug in), then there will never be a top-level panic"; no linearizability
in the top-level theorem, no reading bytes off the network):

    Fresh lctx σ := σ.goState.goLctx = lctx ∧ σ.goState.packageState = ∅ ∧ σ.threads = 1

    Robust crashing stable g bound :=
      (∀ m ∈ crashing ++ stable, Fresh lctx m.2) →
      ∀ n κs c, DistCrashNsteps (crashing.map Prod.fst) n (distInit (crashing ++ stable) g) κs c →
        n < bound → ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
          ∀ e ∈ tp, RealNotStuck e (σ, c.global) ∧ ¬ UnrecoveredPanic e

- **No semantics of its own.** The executions are Perennial's `DistCrashNsteps`
  (`DistLang.lean`), the relation `goose_dist_crash_adequacy` is about; the extensions are the
  instances `[GooseExts] [GooseSemantics]`.
- **Every machine is a fresh Go process** (`Fresh`, a premise inside `Robust`; 2026-11-17, the
  user's: the hypotheses `Hlctx` and `Hinit` of every closed theorem are generic, fold them in; the
  agent added `Hthreads`, as generic): the Go context the theorem's `go.Semantics` is about (the
  instance `[GoLocalContext]`, one for all machines, as echo's), no package initialized, one thread.
  An instance states only what is its own (kvdurable: none of its files exists; kvnet: no listener,
  the plan, the directories).
- **A machine that never crashes is one with no boot program**: `DistCrashStep`'s crash needs
  `boots[i]? = some e`, and the boot list is `crashing`'s, so the machines of `stable`, listed after
  them, never crash (`distCrashStep_cases`, proved).
- **Stuck as well as panicking** (the agent's, for review): the conclusion is the adequacy theorems',
  not only "no top-level panic". An invalid operation is stuck in GooseLang (its builtin `Panic`,
  which the TCP extension's invalid uses step to), so without `RealNotStuck` those would be allowed.
- **The step bound stays** (the agent's): kv's and kvdurable's closed theorems hold below `2^61`
  steps, and kvnet's proof reuses theirs.
- Proved, not trusted: `Robust.of_all_crashing` (robust with every machine crashing implies robust
  with only some: what `goose_dist_crash_adequacy` gives as it stands).

A property of a system is a `Robust` statement about a deployment with a program that checks it
and panics. Linearizability of a store: a client on a machine of `stable` records its history and
panics unless porcupine accepts it, as `Main` of kv, kvdurable and kvwitness does in one process.

**First instance proved** (2026-11-17): `raft_kvdurable_robust`
(`Proof/.../examples/raft/kvdurable/AdequacyLinked.lean`; restated as
`raft_kvdurable_porcupine_robust` in its `Results.lean`): `Robust [] [(kvdurableProgram dir, σ)] g
(2^61)`, under `raft_kvdurable_adequate`'s hypotheses on the start state (only `Hfiles` is the theorem's;
`Robust` has the rest) and on the same 328 axioms,
no `sorry`. One machine that never crashes and none that does: kvdurable's replicas are goroutines
of one process and its crashes are the program's own (`Cluster.Crash`, restarts from the files).
- `Robust.of_single` (`Statement.lean`): the single-node adequacy conclusion gives `Robust [] [(e,
  σ)] g bound`, since a single machine with no boot program runs as `RealNsteps`
  (`distCrashNsteps_single`). Every closed single-process theorem of the examples can be restated
  the same way.
- The conclusion is stronger than `raft_kvdurable_adequate`'s "no thread has ended in a panic":
  `¬ UnrecoveredPanic` also excludes a thread still unwinding a panic nothing will recover. Perennial's
  `goose_adequacy` proves it; the examples' wrappers weakened it (`adequate_of_unrecovered`). They
  now have unweakened variants (`init_adequate_start_unrecovered`, `durable_init_adequate_unrecovered`,
  `kvdurable_unrecovered_of`), the old ones corollaries with unchanged statements.

**History.** Version 1 (2026-11-15) had a semantics of its own (`Run.lean`: `World`, `Who`, `Timed`,
`RunStep`/`Run`), a `Deployment`, an abstract network class `StreamNet`, arbitrary environment nodes
under an `Assume` on their events and a `Guarantee` on the trace. Version 2 (2026-11-15, the user's:
no world, use GooseLang's relation) put it over `DistCrashStep` but kept `Assume`/`Guarantee`, with
the events read off the TCP extension's state (`Stream.lean`) and `Linearizability.lean`
(`LinearizableTrace`). Version 3 (this one) deleted both files and everything but `Robust`: the
trusted Lean went from about 430 lines of definitions (plus kvnet's wire decoders, model and
`ClientsOk`) to one definition.

## kvnet's statement (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Robust.lean`)

`kvnetRobust replica client : Prop`, a `def` (no proof, no `sorry`, no axiom): for every deployment
of replica machines, which may crash, each running `replica cfg` (`ReplicaStart`: fresh directory,
no listener, no package initialized), and one client machine, which never crashes, running
`client addrs` on another host (`ClientStart`), on a fresh network (`FreshNet`: a well-formed plan,
`Tcp.PlanWellFormed`, that puts each replica's address at its host, and no connection),
`Robust … (2^61)`.

- **Both programs are parameters**: kvnet is not translated, and the checking client does not exist
  as a program of its own (the driver runs the clients inside the harness that kills processes and
  partitions the network). The theorem to prove is `kvnetRobust` of the two translations.
- **Gone with version 2**: the wire decoders in Lean (`frame`, `kvProto`, a second copy of kvnet's
  codec to trust), `kvModel`, `OpKey`, and the environment's discipline `ClientsOk` (`NoPeerClaim`,
  `ReadSeqsFresh`): the deployment is closed, every machine runs a given program, so nobody forges
  peer messages and the client's own code picks its sequence numbers.
- **Replicas started later** (the driver's ids 4-9) are machines of the deployment from the start
  that the scheduler does not run before; **removed replicas** keep running, as in the test.

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

- The checking client as a Go program (`examples/raft/kvnet/cmd/...`): the clients' traffic and
  configuration changes, the history, porcupine, a panic unless `Ok`; no fault injection. Then
  translate it and the replica (`net` through the TCP extension, `NetTcp/`).
- Adequacy for machines that never crash: `goose_dist_crash_adequacy` lets every node crash, so
  through `Robust.of_all_crashing` the client's proof would have to survive its own crash, losing
  its history. A version with a boot list for some nodes only (no crash obligation for the others)
  is a general Perennial change, to propose there on its own (`notes/perennial-changes.md`).
- A mutation check that only the network finds (e.g. a `Read` served without a read index: a stale
  read from a partitioned old leader).
- Other programs: the harness takes any binary; their statements are `Robust` of their machines.
