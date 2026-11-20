# kvnet's top-level robustness theorem: the goal and the plan (2026-11-20)

Agreed with the user, interactively, 2026-11-20. Status: **statement drafted, nothing implemented**.
Supersedes the statement in `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Robust.lean`
(2026-11-15/17), which goes away (item 7).

## The goal

`theorem raft_kvnet_robust : raft_kvnet_robust.spec`, no `sorry`, no axiom beyond the existing trust
base (Lean's axioms, the Goose translation, the trusted `net` model, the net and fs extensions'
semantics, the trusted package-assumption instances). The statement, in one file to audit,
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/TopLevelRobustness.lean`:

```lean
/-- Raft's options for the cluster. Any values: the programs validate them. -/
structure ClusterConfig where
  voters : w64                      -- bootstrap configuration: replicas 1..voters
  preVote checkQuorum stepDownOnRemoval : Bool
  maxSizePerMsg maxCommittedSizePerReady maxInflightMsgs : w64

/-- Replica `id`'s process, `addrs` the replicas' addresses joined by commas. -/
def kvnetReplicaProgram (cl : ClusterConfig) (addrs : GoString) (id : w64) : Expr :=
  kvnet.initialize' #() ;;
  (@! kvnet.RunNode) #id #addrs #cl.voters #cl.preVote #cl.checkQuorum #cl.stepDownOnRemoval
    #cl.maxSizePerMsg #cl.maxCommittedSizePerReady #cl.maxInflightMsgs

/-- The checking client's process. -/
def kvcheckProgram (cl : ClusterConfig) (addrs : GoString) : Expr :=
  kvcheck.initialize' #() ;;
  (@! kvcheck.Check) #addrs #cl.voters #cl.preVote #cl.checkQuorum #cl.stepDownOnRemoval
    #cl.maxSizePerMsg #cl.maxCommittedSizePerReady #cl.maxInflightMsgs

abbrev fsOf (σ : state) : Fs.OsState := extLocal Fs.fsExt σ.world

def raft_kvnet_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [<trusted package instances>],
  ∀ (cl : ClusterConfig) (replicas : List (GoString × state)) (σc : state) (g : GlobalState),
    (replicas.map (·.1)).Nodup →
    (∀ a σ, (a, σ) ∈ replicas →
      "/kvnet" ∈ (fsOf σ).fs.roots.map (·.1) ∧
      ∀ c, (fsOf σ).lookup ("/kvnet/" ++ c) = none) →
    let addrs := GoString.intercalate "," (replicas.map (·.1))
    Robust (replicas.mapIdx fun i (_, σ) => (kvnetReplicaProgram cl addrs (i + 1), σ))
           [(kvcheckProgram cl addrs, σc)]
           g (2 ^ 61)
```

Decisions behind it (the user's, 2026-11-20):
- One file per statement, audited alone; `Robust.lean` was written before the `TopLevelRobustness`
  convention.
- The programs are named directly, not parameters. Only scalars and one string cross into them
  (no Lean encoding of Go structs or maps in the TCB): the addresses as one comma-separated string,
  split in Go; the options as `w64`/`Bool` (Go types, so no wrap-around).
- No validity premise on the configuration: both programs validate it and return at once if it is
  invalid (a normal return is robust).
- Replicas are identified by position: replica `i+1` listens at `replicas[i].1` on machine
  `replicas[i].2`. So every address has a machine.
- Full client traffic from the start (Put/Get/Read, configuration changes, disruptions).
- The client's machine never crashes (`Robust`'s `stable`); whether the adequacy theorem covers a
  deployment where only some machines crash is to be sorted out later.
- The extensions' initial states are not premises of the instance: `Robust` requires them
  (items 1-2). The network has no plan or host labels (item 3).
- Safety only: the driver's convergence and final-crash checks are not in the theorem (data lost by
  a crash is still caught, by a later Read failing porcupine).

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
     ephemeral range: today's `addrOk`); `Listen`/`Dial` of an invalid address is a panic (D22);
   - `Listen` of a valid address: a new listener, or `sys` (only `sys` if this machine has an open
     one at it). Any machine may listen at any valid address; `Accept` takes any connection pending
     at its address. `Dial`, `Read`, `Write`, `Close`, deadlines, crashes as now (a crash drops the
     listeners);
   - wildcard `Listen(":p")`: a listener that accepts connections pending at any address with port
     `p` (only adds behaviours), or unsupported;
   - only adds behaviours: a program robust under the old model is robust under the new (every new
     behaviour starts from a step that was a panic). Exclusivity ("only one machine listens at `a`")
     moves into each proof (a ghost token per address, allocated at initialization);
   - update: the seven TCP examples (drop their plan-at-host premises), the kits and `KitDeploy`,
     `Tests.lean:500-510`, `Replay.lean:346`, `Decide.lean:283-296` (`listenAtB`),
     `Proto.lean:519-529` (`addrTok_listenAt`), the D6/D13/D20/D21 notes, `Net/TrustedCode/net.lean`.
4. Fs extension: `init := FsInit`, `globalInit := True`.
5. Optional: the generic `fsOf` (and `netOf`) next to their extensions.

**Lean, kvnet**

6. Check that `GoString.intercalate` exists (else a list function on bytes).
7. Delete `Proof/.../raft/kvnet/Robust.lean`; create the Spec file above; update `notes/kvnet.md`,
   `notes/robustness.md`.

**Go**

8. `kvnet.RunNode(id, addrs string, voters, options…)`: split the addresses; the directory is the
   constant `/kvnet`; return at once on an invalid configuration (an address not canonical, voters
   not in `1..len(addrs)`, both size limits 0, `maxInflightMsgs` not positive) or
   `id ∉ 1..len(addrs)`. `NodeConfig` and the address map stay internal.
9. `RunNode` never panics on a failed `Listen` (today `node.go:98-110` retries 5 s, then panics:
   reachable, since `Listen` may fail every time); retry forever.
10. Translatable: replace the array of atomics in `stats.go`; keep `args.go` (`flag`) and `cmd/` out
    of the translated package.
11. New package `kvcheck`, `Check(addrs string, voters, options…)`: validates the configuration as
    `RunNode`; Put/Get/Read clients retrying across replicas, with fresh operation ids and read
    sequence numbers; configuration-change proposers; disruptions; the history; a panic if
    porcupine answers `Illegal` or a reply is malformed.
12. The driver runs `kvcheck` as its client; only fault injection stays in the harness.

**Translation**

13. Goose-translate `kvnet`, `kvcheck` and their dependencies (`durable` reimplemented over `os` per
    `notes/decisions.md`, "One file semantics, fsExt; power loss only"; `net` through the net
    extension; porcupine, from kv's if reusable). That fixes the trusted package instances.

**Open**: generic extensions (any list with net and fs) or a fixed bundle; the bound `2^61`
(kvdurable's); the trusted package instances (item 13).
