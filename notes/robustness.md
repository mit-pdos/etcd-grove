# Robustness theorems and robustness tests (2026-11-15)

**Goal** (the user's): one framework, reused across programs, for (1) testing a distributed program
the way it runs for real -- real processes, a real network, real file systems -- with every fault made
by the environment, never by hooks in the program; and (2) stating what a proof of the program
establishes about exactly those runs. First user: `examples/raft/kvraft`. Branch `robustness`.

## The two halves

| | Go (test) | Lean (statement) |
|---|---|---|
| where | `examples/lib/robust` | lean_lib `Robustness` (`Robustness/Statement.lean`) |
| the system's nodes | the program's unchanged binary, a process per machine (`Machine.Start`) | `Robust`'s `crashing`: each machine's program (its Goose translation) and initial local state |
| clients | goroutines dialing from client machines (`Machine.Dial`) | `Robust`'s `stable`: programs on machines that never crash (a client that records its history and checks it) |
| crashes | `Proc.Kill` (SIGKILL) then `SyncFS`, or `Disk.PowerLoss` (dm-flakey) | `DistCrashStep.crash`: any machine of `crashing`, any step, restart with its program from a state the extensions' crash relations allow (the file extension's power loss; a kill plus sync is one by its "Restarts" assumption) |
| network faults | the kernel, in a router namespace: iptables partitions (both ways or one way, drops or resets), tc netem (delay, jitter, loss, duplication, reordering); `NetNemesis` | the plugged-in extension's nondeterminism (TCP: a direction cut at any read or write, any delay, a dial failing) |
| scheduling | the OS | any interleaving (a machine started late is one not scheduled before) |
| what is checked | the driver's (kvraft: porcupine on the clients' history, convergence, the final whole-cluster crash) | no thread of any machine stuck or with a top-level panic; so whatever a program checks before panicking |

## The Lean statement (`Robustness/Statement.lean`)

One trusted definition (2026-11-17, the user's: "if you run machines running code [e1, ..., en] on
machines that never crash and [e1', ..., em'] on machines that crash and restart (and with whatever
extensions you choose to plug in), then there will never be a top-level panic"; no linearizability
in the top-level theorem, no reading bytes off the network):

    Fresh lctx σ := σ.goState.goLctx = lctx ∧ σ.goState.packageState = ∅ ∧ σ.threads = 1

    Robust crashing stable g threads bound :=
      (∀ m ∈ crashing ++ stable, Fresh lctx m.2) →
      extsInitGlobal g → (∀ m ∈ crashing ++ stable, extsInitLocal m.2 g) →
      ∀ n κs c, DistCrashNstepsBelow (crashing.map Prod.fst) threads n
                  (distInit (crashing ++ stable) g) κs c →
        n < bound → ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
          ∀ e ∈ tp, RealNotStuck e (σ, c.global) ∧ ¬ UnrecoveredPanic e

- **Every machine and the network start in their extensions' initial states** (2026-11-21, for
  kvraft's statement): Perennial's trusted `ExtSemantics.initLocal`/`initGlobal` (Perennial
  `c0ec40070`, `extsInitLocal`/`extsInitGlobal`), premises inside `Robust` as `Fresh` is, so that no
  instance states an extension's start conditions itself. The bridges (`of_single`,
  `of_single_crashing`, `of_all`, `of_all_crashing`, the kits') take the same hypotheses as before
  and drop the new premises; no example's proof changed.
- **The thread bound** (2026-11-20, the user's: "we need to have the thread bounds NOT be imposing
  the step bounds (2^28 is a joke)"; branch `robust-threads`): the executions are those along which
  every machine keeps fewer than `threads` live threads (Perennial's `DistCrashNstepsBelow`), a premise
  about the run, so an instance's step bound is its proofs' (receipts), not its thread bound. Until
  then `Robust` had none, and every instance whose proof needs a constant thread bound (the etcd
  server's `2^28`) had its step bound below it. An instance with no thread bound of its own states
  `threads := bound + 1`, its statement without one (`Robust.toAll`). The header of
  `Robustness/Statement.lean` says what it excludes (reviewed twice by a subagent, 2026-11-20).
- **No semantics of its own.** The executions are Perennial's `DistCrashNsteps`
  (`DistLang.lean`), the relation `goose_dist_crash_adequacy` is about; the extensions are the
  instances `[GooseExts] [GooseSemantics]`.
- **Every machine is a fresh Go process** (`Fresh`, a premise inside `Robust`; 2026-11-17, the
  user's: the hypotheses `Hlctx` and `Hinit` of every closed theorem are generic, fold them in; the
  agent added `Hthreads`, as generic): the Go context the theorem's `go.Semantics` is about (the
  instance `[GoLocalContext]`, one for all machines, as echo's), no package initialized, one thread.
  An instance states only what is its own (kvdurable: none of its files exists; kvraft: no listener,
  the plan, the directories).
- **A machine that never crashes is one with no boot program**: `DistCrashStep`'s crash needs
  `boots[i]? = some e`, and the boot list is `crashing`'s, so the machines of `stable`, listed after
  them, never crash (`distCrashStep_cases`, proved).
- **Stuck as well as panicking** (the agent's, for review): the conclusion is the adequacy theorems',
  not only "no top-level panic". An invalid operation is stuck in GooseLang (its builtin `Panic`,
  which the TCP extension's invalid uses step to), so without `RealNotStuck` those would be allowed.
- **The step bound stays** (the agent's): kv's and kvdurable's closed theorems hold below `2^61`
  steps, and kvraft's proof reuses theirs.
- Proved, not trusted: `Robust.of_all_crashing` (robust with every machine crashing implies robust
  with only some: what `goose_dist_crash_adequacy` gives as it stands).

A property of a system is a `Robust` statement about a deployment with a program that checks it
and panics. Linearizability of a store: a client on a machine of `stable` records its history and
panics unless porcupine accepts it, as `Main` of kv, kvdurable and kvwitness does in one process.

**An exit is a safe run, so a checker panics** (2026-11-24, the user's approval of Perennial's
model of Go's process exit, on the condition that it is documented; `notes/decisions.md`, "Go's
process exit stays angelic, and checkers panic"). `syscall.Exit` (so `os.Exit`, `log.Fatal`, zap's
and klog's `Fatal`) is `AngelicExit` (Perennial `ca6df841b`, Perennial's and this repository's
`TrustedCode/syscall.lean`): the exiting goroutine steps to itself forever, which is neither stuck
nor a panic, and the machine's other goroutines keep running, where Go ends the process. So under
`Robust` an exit of any status, 0 or 1, ends nothing and violates nothing: a program that reports a
violation with `os.Exit(1)` or `log.Fatal` is checked by nothing, and its theorem says nothing about
the property. Go's run of a machine that exits is, up to the exit, one of the model's executions,
and after it is like a machine the scheduler stops picking (an execution `Robust` covers); the model
also lets the other goroutines run on, which the proof must show safe too (more executions than Go:
sound). `etc/exit-check.py` (in `etc/gates.sh` and CI) lists the exits in the own code (under
`examples/`) of every program a `TopLevelDefs.lean` boots, type-checked by `etc/exitcheck`; each needs
an entry in `etc/exit-allow.txt` with its reason (a usage error of a command line, before any check
runs), so no check of a robustness theorem's program exits on a violation.

## Every closed example is an instance (2026-11-18)

Each closed theorem of the examples has a restatement `…_robust` (the same hypotheses but the
generic ones `Robust` states itself), in two files named `TopLevelRobustness.lean` per example
directory (2026-11-18, the user's: easy to find, and a statement to audit apart from its proof):

- `Spec/<example>/TopLevelRobustness.lean` only **states** the results, one
  `def <name>.spec : Prop` each (every hypothesis, then `Robustness.Robust …`);
- `Proof/<example>/TopLevelRobustness.lean` only **proves** them, `theorem <name> : <name>.spec`,
  from the example's closed theorem (in its `Results.lean`, or `Adequacy.lean` for lintest's and
  `mvccrand`).

- `Proof/<example>/TopLevelDefs.lean` holds the definitions the statement is written in that
  used to sit in `Adequacy.lean`/`Results.lean` (the program; for the etcd-server examples also the
  ghost-state bundle, its heap helper and the lists of names and addresses), moved unchanged, so
  that the Spec file imports no proof: "specs never import proofs" (CLAUDE.md, "Import tiers",
  which landed the same day). `etc/tier-check.py` counts the `Proof/` side's
  `TopLevelRobustness` as a linking module.

(The parts have theirs under `Net/`, `RaftWitness/`, `RaftTla/` and, as copies, `RaftNoAx/`.
`etc/proof_roots.py` counts the proof files as results files, so the trust-base report covers
them. `find . -name TopLevelRobustness.lean` lists them all.)

| shape | bridge (`Robustness/Statement.lean`) | `Robust` form | examples |
|---|---|---|---|
| one process, `RealNsteps` | `Robust.of_single` (`distCrashNsteps_single`) | `Robust [] [(prog, σ)] g bound` | the etcd-server examples (`etcd/*`, `k8s/*`, `mvccfull`, `mvccrand`), raft's (`kv`, `kvdurable`, `kvreconf` and their `N` forms; `RaftNoAx/`'s copy of kvdurable; `RaftWitness/`'s kvwitness; `RaftTla/`'s tracecheck), lintest's six, `goose/prophkv` |
| one process with crashes, `RealCrashNsteps` | `Robust.of_single_crashing` (`distCrashNsteps_single_crashing`) | `Robust [(boot, σ)] [] g bound` | `osfs/crashlog`, `osfs/walfs` (three) |
| one process with crashes, thread bound along it, `RealCrashNstepsBelow` (2026-11-24) | `Robust.of_single_crashing_below` (`Robustness/CrashBelow.lean`: `distCrashNstepsBelow_single_crashing`, then Perennial's `goose_crash_adequacy_below`) | `Robust [(boot, σ)] [] g threads bound` | `osfs/bboltfs` |
| several machines, `DistCrashNsteps` | `Robust.of_all` | `Robust (system …) [] g bound` | the seven TCP examples (`Net/…/net/*`) |
| several machines that never crash, `DistNsteps` (2026-11-19) | `robust_of_distBoot`, `robust_of_distProto` (`Net/Statement/DistBridge.lean`: `distNsteps_of_crash_nil`, then `goose_dist_adequacy`), under the deployment premise `DistDeploy plan hosts nodes g` (`Net/Statement/DistDeploy.lean`) | `DistDeploy … → Robust [] nodes g bound` | the network kits (`notes/dsverify-net-port-plan.md`, phases 4 and 6); `echo_dist_robust` (`Net/…/net/echo/RobustLinked.lean`), the non-vacuity check |

- **The bound** is the example's own: `2^61` or `2^63` (raft's, lintest's; `logkvrw` `2^63` at `2^30`
  threads since 2026-11-22), `2^48` at `2^28` threads (the 22 `etcd/*` examples and `k8s/all`,
  since 2026-11-22, #30 step 2: the request ids' receipt bound, `idutil`'s; the backend's buffered
  entries are paid by time receipts, so its write-back budget, `2^62`, no longer binds; from
  2026-11-20 `2^40 - 11`, that budget; before, `2^28 - 1`, their proofs' thread bound `n + 2`),
  `2^48` at `2^28` threads (`mvccfull`, `mvccrand`, since 2026-11-23, #30: mvcc's own receipt
  bound, `ReceiptBoundLe GF (2 ^ 48)` of `mvcc.New`; from 2026-11-22 `2^38`, a convention the
  examples' specs passed along), `2^61 - 3` at `2^31` threads (tracecheck),
  `2^63` at `2^30` threads (`bboltfs`, since 2026-11-24, #30 1b: crash adequacy along the
  execution, Perennial's `goose_crash_adequacy_below`, perennial#690; before, `2^30 - 1`, the thread
  bound derived from the step count), and any `bound` (a parameter) where the theorem had none (the
  TCP and `osfs` examples, `prophkv`). The plan to raise the etcd bounds further (`K` receipts per request id,
  toward `K · 2^48`; the id suffix's wrap, `nonissues/etcd-request-id-suffix-wrap-dup-panic.md`, is
  the real ceiling): claim issue mit-pdos/etcd-grove#30.
- **A hypothesis that mentioned the execution's length** (`Hprem`: the etcd examples' boot
  premises at `n`) is assumed at every `n` within the bound.
- **`RealCrashNsteps` does not count a crash as a step**, `DistCrashNsteps` does: a run of `n`
  steps of `Robust` is one of at most `n` steps there.
- **The examples' theorems now conclude `¬ UnrecoveredPanic`** (no thread has a panic that nothing
  recovers, finished or still unwinding) where they said "no thread has ended in a panic"
  (`v.isPanic = false`): `Robust` needs the former, Perennial's adequacy theorems prove it, and the
  examples' wrappers (`init_adequate`, `etcd_adequate…`, `init_adequate_start`,
  `durable_init_adequate`) weakened it (`adequate_of_unrecovered`, no longer used). Strengthened in
  place, statements and wrappers; no proof changed otherwise.
- **What `Robust` does not say**: the main thread's result. Nothing is lost: every example's
  check is a panic. The etcd and k8s examples panic on a bad verdict (`Main` panics when porcupine
  answers `Illegal`; the auth, cache and watch checks are panics), and the result their old
  theorems state (`"Ok"` or `"Unknown"`; a status code `0`, `1`, `2`, ...) only lists how far the
  run got (a failed start, a porcupine timeout). `goose/prophkv` was the exception (its program
  was `Test()`, its guarantee the result, `"a"` or `"b"`); fixed 2026-11-18 (the user's): the
  program is now `Main()`, which panics unless `Test`'s answer is `"a"` or `"b"`
  (`examples/goose/prophkv/prophkv.go`, `Main.spec`, `goose_prophkv_safe` with the result `#()`).
- Generated once by a script (not kept: the theorems are ordinary text now); `RaftNoAx/`'s copies
  by `etc/copy-part.py` (kvdurable's `TopLevelRobustness` is one of its roots).

**History.** Version 1 (2026-11-15) had a semantics of its own (`Run.lean`: `World`, `Who`, `Timed`,
`RunStep`/`Run`), a `Deployment`, an abstract network class `StreamNet`, arbitrary environment nodes
under an `Assume` on their events and a `Guarantee` on the trace. Version 2 (2026-11-15, the user's:
no world, use GooseLang's relation) put it over `DistCrashStep` but kept `Assume`/`Guarantee`, with
the events read off the TCP extension's state (`Stream.lean`) and `Linearizability.lean`
(`LinearizableTrace`). Version 3 (this one) deleted both files and everything but `Robust`: the
trusted Lean went from about 430 lines of definitions (plus kvraft's wire decoders, model and
`ClientsOk`) to one definition.

## kvraft's statement (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/Robust.lean`)

`kvraftRobust replica client : Prop`, a `def` (no proof, no `sorry`, no axiom): for every deployment
of replica machines, which may crash, each running `replica cfg` (`ReplicaStart`: fresh directory,
no listener, no package initialized), and one client machine, which never crashes, running
`client addrs` on another host (`ClientStart`), on a fresh network (`FreshNet`: a well-formed plan,
`Tcp.PlanWellFormed`, that puts each replica's address at its host, and no connection),
`Robust … (2^61)`.

- **Both programs are parameters**: kvraft is not translated, and the checking client does not exist
  as a program of its own (the driver runs the clients inside the harness that kills processes and
  partitions the network). The theorem to prove is `kvraftRobust` of the two translations.
- **Gone with version 2**: the wire decoders in Lean (`frame`, `kvProto`, a second copy of kvraft's
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

kvraft: `go run ./raft/kvraft/cmd/kvraft check -rounds N` (from `examples/`; `-net auto` is namespaces when
`sudo -n` works, `-crash auto` mixed kills and power losses); `KVRAFT_NETNS=1 go test
./raft/kvraft/driver -run TestNetns`. The transport's random drops, delays, duplicates and cuts
(`Faults`) are gone. What stays in the program: the choices raft leaves the application, made at
random (durability orderings, snapshot and compaction points, `Config.Applied` at a restart, the tick):
they are the program's own nondeterminism, which the proof covers, not fault injection.

Results (2026-11-15): 10 rounds, namespaces, mixed crashes: porcupine `Ok` and convergence every
round; e.g. a round of 127 kills, 131 power losses, 127 partitions (36 one way, 44 isolating a
machine, 27 by resets) and 47 link-fault episodes.

## Next

- The checking client as a Go program (`examples/raft/kvraft/cmd/...`): the clients' traffic and
  configuration changes, the history, porcupine, a panic unless `Ok`; no fault injection. Then
  translate it and the replica (`net` through the TCP extension, `Net/`).
- Adequacy for machines that never crash: `goose_dist_crash_adequacy` lets every node crash, so
  through `Robust.of_all_crashing` the client's proof would have to survive its own crash, losing
  its history. A version with a boot list for some nodes only (no crash obligation for the others)
  is a general Perennial change, to propose there on its own (`notes/perennial-changes.md`).
  The no-crash bridge (`Net/Statement/DistBridge.lean`, 2026-11-19) covers only the case where **every**
  machine is stable (`Robust [] nodes`: no boot program, so the executions are `DistNsteps` and
  `goose_dist_adequacy` applies); a deployment with both kinds (kvraft's) still needs that change.
  (2026-11-22: Perennial has it, `goose_dist_mixed_crash_adequacy`; its bridge for `[netExt, fsExt]`,
  `robust_of_netFsBoot` (`Net/Statement/NetFsBridge.lean`, etcd-dist D3, `notes/dist-crash-bridge.md`),
  with echo's server crashing and its client stable as the instance, branch `dist-crash-bridge`.)
- A mutation check that only the network finds (e.g. a `Read` served without a read index: a stale
  read from a partitioned old leader).
- Other programs: the harness takes any binary; their statements are `Robust` of their machines.
