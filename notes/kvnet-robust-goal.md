# kvnet's top-level robustness theorem: the goal and the plan (2026-11-20)

Agreed with the user, interactively, 2026-11-20; revised the same day after a fresh-agent review
(below). Status: **statement drafted, nothing implemented, not type-checked**. Supersedes the
statement in `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Robust.lean` (2026-11-15/17),
which goes away (item 7).

## The goal

`theorem raft_kvnet_robust : raft_kvnet_robust.spec` and its corollary
`theorem raft_kvnet_robust_example : raft_kvnet_robust_example.spec`, no `sorry`, no axiom beyond the
existing trust base (Lean's axioms, the Goose translation, the trusted `net` model, the net and fs
extensions' semantics, the trusted package-assumption instances). Both statements, in one file to
audit, `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/TopLevelRobustness.lean`; the proofs
in `Proof/.../raft/kvnet/TopLevelRobustness.lean`:

```lean
/-- Raft's options for the cluster. -/
structure ClusterConfig where
  voters : w64                      -- bootstrap configuration: replicas 1..voters
  preVote checkQuorum stepDownOnRemoval : Bool
  maxSizePerMsg maxCommittedSizePerReady maxInflightMsgs : w64

/-- Options raft and kvnet accept, for a cluster of `n` replicas (`raft.Config.validate`;
`newRaft` refuses both size limits 0; `MaxInflightMsgs` below raft's `RestartNode`'s `2^62`). -/
def ClusterConfig.Ok (cl : ClusterConfig) (n : Nat) : Prop :=
  1 ≤ cl.voters.toNat ∧ cl.voters.toNat ≤ n ∧
  ¬ (cl.maxSizePerMsg = 0 ∧ cl.maxCommittedSizePerReady = 0) ∧
  0 < cl.maxInflightMsgs.toNat ∧ cl.maxInflightMsgs.toNat < 2 ^ 62

/-- Replica `id`'s process: kvnet's package initialization, then `RunNode`; `addrs` the replicas'
addresses joined by commas (replica `i` at the `i`-th), `dir` the directory of its durable state. -/
def kvnetReplicaProgram (cl : ClusterConfig) (addrs dir : GoString) (id : w64) : Expr :=
  kvnet.initialize' #() ;;
  (@! kvnet.RunNode) #id #addrs #dir #cl.voters #cl.preVote #cl.checkQuorum
    #cl.stepDownOnRemoval #cl.maxSizePerMsg #cl.maxCommittedSizePerReady #cl.maxInflightMsgs

/-- The checking client's process: its package initialization, then `Check`. The driver: it runs
the clients' Put/Get/Read operations (retrying across replicas, fresh operation ids and read
sequence numbers), configuration changes and leadership disruptions, records the history with a
counter clock, and panics unless porcupine (no timeout) answers `Ok`. A reply that does not
decode counts as no answer. -/
def kvcheckProgram (cl : ClusterConfig) (addrs : GoString) : Expr :=
  kvcheck.initialize' #() ;;
  (@! kvcheck.Check) #addrs #cl.voters

-- The extensions are fixed: the net extension and the Linux file extension, and nothing else.
attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExts_hasNet kvnetExts_hasFs

abbrev fsOf (σ : state) : Fs.OsState := extLocal Fs.fsExt σ.world

/-- **kvnet is robust.** Replica `i+1` listens at `replicas[i].1` and runs on the machine
`replicas[i].2`. -/
def raft_kvnet_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [<trusted package instances>],
  ∀ (cl : ClusterConfig) (dir : GoString) (replicas : List (GoString × state)) (σc : state)
    (g : GlobalState),
    cl.Ok replicas.length →
    replicas.length < 2 ^ 32 →
    (replicas.map (·.1)).Nodup →
    (∀ a σ, (a, σ) ∈ replicas →
      Net.addrOk a ∧                                      -- canonical a.b.c.d:p
      dir ∈ (fsOf σ).fs.roots.map (·.1) ∧                 -- dir is an empty root
      ∀ c, (fsOf σ).lookup (joinPath dir [c]) = none) →
    let addrs := List.intercalate go!"," (replicas.map (·.1))
    Robust (replicas.mapIdx fun i (_, σ) => (kvnetReplicaProgram cl addrs dir (i + 1), σ))
           [(kvcheckProgram cl addrs, σc)]
           g (2 ^ 61)

/-- The example deployment: 5 replicas, 3 of them bootstrap voters (the driver adds the others). -/
def exampleConfig : ClusterConfig :=
  { voters := 3, preVote := true, checkQuorum := true, stepDownOnRemoval := true,
    maxSizePerMsg := 1048576, maxCommittedSizePerReady := 1048576, maxInflightMsgs := 256 }

/-- **kvnet is robust, an example**: replicas 1..5 at 10.0.0.1:7001 .. 10.0.0.5:7001, durable state
in /var/lib/kvnet. A corollary of `raft_kvnet_robust`. -/
def raft_kvnet_robust_example.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [<trusted package instances>],
  ∀ (σ₁ σ₂ σ₃ σ₄ σ₅ σc : state) (g : GlobalState),
    (∀ σ ∈ [σ₁, σ₂, σ₃, σ₄, σ₅],
      go!"/var/lib/kvnet" ∈ (fsOf σ).fs.roots.map (·.1) ∧
      ∀ c, (fsOf σ).lookup (joinPath go!"/var/lib/kvnet" [c]) = none) →
    let addrs := go!"10.0.0.1:7001,10.0.0.2:7001,10.0.0.3:7001,10.0.0.4:7001,10.0.0.5:7001"
    let dir := go!"/var/lib/kvnet"
    Robust [(kvnetReplicaProgram exampleConfig addrs dir 1, σ₁),
            (kvnetReplicaProgram exampleConfig addrs dir 2, σ₂),
            (kvnetReplicaProgram exampleConfig addrs dir 3, σ₃),
            (kvnetReplicaProgram exampleConfig addrs dir 4, σ₄),
            (kvnetReplicaProgram exampleConfig addrs dir 5, σ₅)]
           [(kvcheckProgram exampleConfig addrs, σc)]
           g (2 ^ 61)
```

The header of the Spec file states, in prose, the environment the extensions assume: the fs
extension's (`Fs/Impl.lean:21-79`: one replica per file system, nothing else touches its tree, a
killed process's file system synced before it restarts) and the net extension's closed world
(restated without the plan: no process outside the deployment listens at or dials the replicas'
addresses).

Decisions behind it (the user's, 2026-11-20):
- One file per statement, audited alone; `Robust.lean` was written before the `TopLevelRobustness`
  convention.
- The programs are named directly, not parameters. Only scalars and strings cross into them (no
  Lean encoding of Go structs or maps in the TCB): the addresses as one comma-separated string,
  split in Go; the directory; the options as `w64`/`Bool` (Go types, so no wrap-around).
- **The configuration's validity is a Lean premise** (`cl.Ok`, `addrOk`, the length bound), and both
  programs **panic** on an invalid configuration (the review: a validate-and-return would make every
  configuration it rejects trivially robust, so the theorem's coverage would be decided by Go code;
  this reverses the earlier "any configuration" choice).
- The directory is a parameter (with the concrete one in the corollary).
- Replicas are identified by position: replica `i+1` listens at `replicas[i].1` on machine
  `replicas[i].2`. So every address has a machine. `replicas.length < 2^32` keeps `(i + 1) : w64`
  and Go's lengths from wrapping.
- **kvcheck decides the workload** (clients, operation counts, keys): it is the driver, and the
  driver is part of the trusted theorem (its source is part of the theorem's meaning: kvcheck's
  `Check`, `lintest`, kvnet's model and request encodings, porcupine's `Ok` meaning linearizable).
  It must use porcupine with no timeout and panic unless `Ok` (an `Unknown` would be a loophole), a
  counter clock (`lintest.CounterClock`), and have no "aborted" path returning a made-up result.
  The test harness calls exactly `kvcheck.Check`, with mutation tests showing it panics.
- Full client traffic from the start (Put/Get/Read, configuration changes, disruptions).
- The client's machine never crashes (`Robust`'s `stable`); whether the adequacy theorem covers a
  deployment where only some machines crash is to be sorted out later.
- The extensions' initial states are not premises of the instance: `Robust` requires them
  (items 1-2). The network has no plan or host labels (item 3).
- A concrete corollary (`raft_kvnet_robust_example`): 5 replicas, 3 voters, fixed addresses and
  directory, proved from the main theorem (its premises by `decide`/computation).
- Safety only: the driver's convergence, deadline and final-crash content checks are not in the
  theorem (losing an acknowledged write is still caught, by a later Read failing porcupine).

## The review (fresh agent, 2026-11-20)

Verdict: the shape is right; not auditor-ready as first drafted. Taken: the configuration's validity
back as Lean premises with Go panics; kvcheck's porcupine/clock/abort requirements; the length
bound; `go!` literals, `List.intercalate`, `joinPath`; a non-vacuity lemma (item 14); the
environment assumptions in the header; the trusted instances listed (item 13). Not taken: naming the
premise groups (the user prefers them inline); the workload as Lean parameters (kvcheck decides it).
Confirmed fine: the crash and network models against the driver, one client machine instead of the
driver's four, the bound `2^61`, the soundness of change (b) (its argument to be written in the net
extension's notes).

## The plan

**Semantics (with the user's sign-off on the trusted parts)**
1. Perennial: `ExtSemantics` gets `init : E.LocalState → Prop` and `globalInit : E.GlobalState →
   Prop` (default `True`); generic `ExtsInit`/`ExtsGlobalInit` over the extension tuple; a lemma per
   extension that a crash preserves `init`; a non-vacuity example per extension. Record in
   `notes/perennial-changes.md`.
2. `Robust` requires `ExtsInit σ.world` of every machine (with `Fresh`) and
   `ExtsGlobalInit g.globalWorld`.
3. The net extension without plan and host labels:
   - state: per machine, its listeners; shared, the connections. `init`: no listener; `globalInit`:
     no connection;
   - an address is valid if canonical `a.b.c.d:p` (IPv4 unicast, port nonzero and outside the
     ephemeral range: today's `addrOk`, `Deploy.lean:63`); `Listen`/`Dial` of an invalid address is
     a panic (D22);
   - `Listen` of a valid address: a new listener, or `sys` (only `sys` if this machine has an open
     one at it). Any machine may listen at any valid address; `Accept` takes any connection pending
     at its address. `Dial`, `Read`, `Write`, `Close`, deadlines, crashes as now (a crash drops the
     listeners);
   - wildcard `Listen(":p")`: a listener that accepts connections pending at any address with port
     `p` (only adds behaviours), or unsupported;
   - only adds behaviours: a program robust under the old model is robust under the new (every new
     behaviour starts from a step that was a panic). Exclusivity ("only one machine listens at `a`")
     moves into each proof (a ghost token per address, allocated at initialization). The soundness
     argument against Linux (EADDRNOTAVAIL is a failure; a real connection reaches the owner, one of
     the listeners the model allows) and the closed world are written in the extension's notes;
   - update: the seven TCP examples (drop their plan-at-host premises), the kits and `KitDeploy`,
     `Tests.lean:500-510`, `Replay.lean:346`, `Decide.lean:283-296` (`listenAtB`),
     `Proto.lean:519-529` (`addrTok_listenAt`), the D6/D13/D20/D21 notes, `Net/TrustedCode/net.lean`.
4. Fs extension: `init := FsInit`, `globalInit := True`.
5. Optional: the generic `fsOf` (and `netOf`) next to their extensions.

**Lean, kvnet**

6. Check the literal syntax (`go!"…"`) and `List.intercalate` on `GoString` (a byte string,
   `Perennial/Std/ByteString.lean:18`); whether `GooseInterp` is needed in the statement.
7. Delete `Proof/.../raft/kvnet/Robust.lean`; create the Spec file above (with the header's
   environment assumptions); update `notes/kvnet.md`, `notes/robustness.md`.

**Go**

8. **Done (2026-11-20).** `kvnet.RunNode(id, addrs, dir, voters, preVote, checkQuorum,
   stepDownOnRemoval, maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs)` (`node.go`): splits
   the addresses (`addrs.go`: `SplitAddrs`, `AddrOk` = the net extension's `addrOk`, unit-tested on
   its edge cases, `ValidAddrs`, `ValidCluster`); **panics** on an invalid configuration or
   `id ∉ 1..len(addrs)` (unreachable under the premises); then `Run(NodeConfig)`, the former
   `RunNode`.
9. **Done.** `listen` retries forever: a failed `Listen` is never a panic.
10. **Done.** `stats.go`: a mutex and a plain array (no array of atomics); `args.go` (`flag`) moved
    to the driver (`driver/args.go`: `NodeArgs`, `ClientArgs`, `RunProcess`). `fmt` stays (kvdurable,
    translated, uses it too).
11. **Done.** Package `kvcheck` (`examples/raft/kvnet/kvcheck`), `Check(addrs string, voters uint64)`
    (the raft options are not the client's business): panics unless `kvnet.ValidAddrs`; 4 clients ×
    100 operations of `kvnet.Gen`, each retried at random members until answered (fresh operation id
    per operation, fresh read sequence number per attempt; an exhausted counter spins rather than
    reuses, as kvdurable's); 1-3 configuration-change proposers and leadership disruptions until the
    clients are done; `lintest.Run` with `CounterClock` and timeout 0; a panic unless `Ok`. A reply
    that does not decode counts as no answer (no obligation on the replicas' replies beyond the
    history). kvdurable's `Run` over the network.
12. **Done.** The harness (`driver.Run`) starts all 9 replicas at once (the theorem's replicas all
    run from the start; the client's configuration changes add and remove them), runs `kvcheck` as a
    process of the same binary on a client machine (`RunProcess`, roles `node`/`client`), and keeps
    only fault injection (kills, power losses, the network nemesis) and its own post-run checks
    (convergence, the final whole-cluster crash; its reads use sequence numbers from 2^63). Local
    mode's addresses are now below the ephemeral range (`AddrOk`). `TestKill` passes (porcupine
    `Ok`, 51 kills). To do: a mutation test showing `Check` panics.

**Translation and linking**

13. Goose-translate `kvnet`, `kvcheck` and their dependencies (`durable` reimplemented over `os` per
    `notes/decisions.md`, "One file semantics, fsExt; power loss only"; `net` through the net
    extension; porcupine, from kv's if reusable; cite PorcupineDag if it proves porcupine's `Ok`
    meaning linearizable). That fixes the trusted package instances, listed in the statement.
14. A non-vacuity lemma: the example deployment's premises (and `Robust`'s, with the new `init`
    predicates) hold of concrete machine states.
15. `raft_kvnet_robust_example` from `raft_kvnet_robust`.

16. The bundle `kvnetExts := ⟨[Net.netExt, Fs.fsExt]⟩` with its semantics, interpretation, crash
    interpretation, `HasExt` instances and adequacy (today only `netExts := ⟨[netExt]⟩`,
    `GooseLang/Ext/Net/Adequacy.lean:52`, and the fs extension's own bundles exist).

Decided (the user's, 2026-11-20): the extensions are fixed in the statement, `kvnetExts` (net and
fs, nothing else): the theorem names the extensions it trusts. Net changes needed are relayed to the
agent working on net (2026-11-20).
