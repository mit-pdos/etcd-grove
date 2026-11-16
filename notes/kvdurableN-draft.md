# Draft: `raft_kvdurableN_porcupine_safe` (kvraftN, R2; for the user's review)

Status: **draft, not linked**. Scope: `notes/kvraftN-scope.md`, "kvreconf and kvdurable: two options",
(R2). Modeled on `raft_kvreconfN_porcupine_safe` (approved 2026-11-16, `notes/kvreconfN-draft.md`) and on
`raft_kvdurable_porcupine_safe` (kvdurable's `Results.lean`), whose text stays unchanged.

## The Lean text

To be added to `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Adequacy.lean` (the program,
`kdMainNSpec` and `kvdurableN_adequate_of` from `MainN.spec`), `AdequacyLinked.lean`
(`raft_kvdurableN_adequate`, from `MainN`'s linked result) and `Results.lean` (the closed statement
below). The program and `kvdurableN_adequate_of` are already checked (a scratch module, 0 errors: the
adequacy goes through from `MainN.spec`); only the linking is left.

```lean
/-- The store's program on `k` voters, its replicas' files in `dir`: the package's initialization,
then `MainN(dir, k)`. -/
def kvdurableProgramN [GoSemanticsFunctions] (dir : GoString) (k : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.MainN) #dir #(W64 (k : Int))

/-- **The durable store's randomized linearizability test never fails, on any number of voters**
(`raft_kvdurableN_adequate`, `AdequacyLinked.lean`; kvraftN): for every member count `1 ≤ k ≤ 1000`,
every real execution of `kvdurableProgramN dir k` -- the store package's initialization, then
`MainN(dir, k)`: a cluster of random options on the bootstrap voters `1 … k`, which may start up to
`k + 4` replicas, with its files in `dir`, 4 clients of 100 random `Put`s, `Get`s and `Read`s, one to
three proposers of configuration changes, leadership disruptions, crashes with restarts from the
files, porcupine's check of the trace, and a panic unless it answers `Ok` -- from a fresh state with
one thread whose files hold none of the files of the replicas `1 … k + 4` in `dir`, of `n < 2^61`
steps, has no stuck thread and no thread that ended in a panic: porcupine always answers `Ok`.
`raft_kvdurable_porcupine_safe` is `Main(dir)` (one to five voters drawn at random, up to 9
replicas); nothing below `2^59` bounds `k` in the proof (`MainN.spec`), `1000` is the bound of the
paper's figure. -/
theorem raft_kvdurableN_porcupine_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]
    [hLog : log.NewModel] (dir : GoString)
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (Hfiles : ∀ i ∈ raft_kvreconf.bootVoters (k + 4),
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvdurableProgramN dir k], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  raft_kvdurableN_adequate dir k hk1 hk σ g Hlctx Hinit Hthreads Hfiles n Hn κs t2 σ2 Hsteps

#print axioms raft_kvdurableN_porcupine_safe
```

(It sits in a `section closedN` with the local instances `durableExts …` and `[go_gctx : GoGlobalContext]`,
as `raft_kvdurable_porcupine_safe`.)

## In plain English

**What it says.** Pick any directory name `dir` and any number of voters `k` from 1 to 1000. Start the
Go program "initialize the `kvdurable` package, then call `MainN(dir, k)`" from a fresh machine with one
thread whose file system holds none of the files the replicas `1 … k + 4` would use in `dir`. Run it
for any number of steps below `2^61`, under any interleaving the scheduler picks and any outcome of the
random choices, the simulated network and the crashes. Then at every point: if the main thread has
finished it returned normally (`()`), no thread is stuck, and no thread has panicked. Since `MainN`
panics exactly when porcupine rejects the history it recorded, porcupine always answers `Ok`: every
history the clients observe is linearizable against a sequential key-value map, crashes included.

**The program, `MainN(dir, k)`** (`examples/raft/kvdurable/check.go`). It builds `RandomConfigN(k)`:
`RandomOptionsN(k)` -- `RandomOptions()`' random raft options (pre-vote, check-quorum,
step-down-on-removal, message size and inflight limits), with `Voters = k` and `MaxReplicas = k + 4` --
4 clients of 100 operations each, 1 to 3 configuration-change proposers, and crashes every 40 ms on
average. `Run` starts a cluster of raft nodes bootstrapped with voters `1 … k`, each replica's raft
storage in a file `dir/replica-<id>`, connected in process by a network that drops, duplicates, delays
and reorders messages; replicas snapshot and compact at random. Concurrently: clients issue random
`Put`s, `Get`s (through the log) and `Read`s (by read index) on keys `a`, `b`, `c`; proposers propose
random configuration changes (add a voter or a learner, remove, through joint configurations or not; a
fresh id starts a new replica, up to `k + 4` started in all); a disrupter moves leadership; a crasher
crashes a random replica and restarts it from its file. When the
clients are done, porcupine checks the trace; `MainN` panics unless it says `Ok`, then stops the
cluster.

**Every premise.**
- `dir`: any directory name; `Hfiles`: the initial file system holds no file `kdFileName dir i` for the
  ids `i = 1 … k + 4` (every replica the run may start; the program's precondition "`dir` holds none of
  the replicas' files"). The 3-member theorem's premise is the same over the fixed ids `1 … 9`.
- `k`, `1 ≤ k ≤ 1000`: the member count. `1000` is the figure's bound, as kvN's and kvreconfN's; the
  proof's own bound is `k < 2^59`.
- `[go.Semantics]`, `[package_sem : …kvdurable.Assumptions]`, `[hLog : log.NewModel]`, `lctx`, the
  durable-file extension's instances: as in `raft_kvdurable_porcupine_safe`. Nothing new.
- `σ`, `g`, `IsInit σ`, `σ.threads = 1`, `σ.goState.goLctx = lctx`: a fresh state, one thread. As before.
- `n < 2^61`, `RealNsteps n …`: any real execution of fewer than `2^61` steps. As before.

No new kind of premise, no axiom, `sorry` or trusted text: `MainN`'s proof is over the same trust base
as `Main`'s (`etc/tcb-collections/kvdurable.txt`), checked at linking.

**How it differs from `raft_kvreconfN_porcupine_safe`.** Same `k` and conclusion, and the same workload
plus durability: the replicas' raft storage lives in files, a crasher crashes and restarts replicas
from them, so the program takes a directory `dir` and the theorem a premise that the files of the
replicas `1 … k + 4` are absent at the start (a premise that depends on `k`, as restartN's
`dataDirsAbsent`).

**How it differs from `raft_kvdurable_porcupine_safe`.** That theorem is about `Main(dir)`, which draws
its voters at random (1 to 5) and may start up to 9 replicas; its files premise is over the ids
`1 … 9`. This one fixes the voter count to the caller's `k`, allows `k + 4` replicas (at `k = 5`,
`Main`'s 9), and its files premise is over `1 … k + 4`. The existing theorem's text is unchanged; its
program's Go code changed (the constant `maxReplicas = 9` became `Options.MaxReplicas`, which
`RandomOptions` sets to 9), so `Main(dir)` behaves as before.

## Evidence

- Build (2026-11-16): every kvdurable module (the 229 of `/shared/tmp/kvraftN/targets.txt` and the new
  `RandomOptionsN`, `RandomConfigN`, `MainN`) builds, and so do the existing `Link`, `Adequacy*`,
  `Results` (`raft_kvdurable_porcupine_safe` unchanged) and `etcdstart.DurableExt`; no `sorry` or
  `axiom` added.
- Go: `TestMainN` (k from {1, 3, 5}, `KVDURABLE_MEMBERS` overrides) 20 runs under the 32G cap:
  **stopped at run 8** (`/shared/tmp/kvraftN/kvdurable-runs20.txt`, logs `kd-run<i>.log`). Runs 1-7 PASS
  (k = 1 ×1, 3 ×1, 5 ×5; 12 s to 473 s). Run 8 (k = 3, options `Voters 3, MaxReplicas 7, PreVote, CheckQuorum,
  MaxSizePerMsg 0, MaxCommittedSizePerReady 4096, MaxInflightMsgs 1`) hit `go test`'s 60-minute timeout
  (`panic: test timed out`, `kd-run8.log`): the clients were still running (`lintest.RunLin2` waiting on them,
  their `Get`s in `node.Propose`), the replicas' files still being rewritten (~0.45 to 1.4 MB each, growing); no
  porcupine verdict, no panic of the program's. A liveness/performance observation (the theorem is about safety;
  these options are among `Main`'s too), not a refutation.

## Forms decided by the agent (reviewed at the checkpoint)

- The replica bound as a field `KdNames.max` of the ghost names (decided by etcd-grove-02), tied to the
  options by `isClusterC` (`uint.nat o.MaxReplicas' = γ.max`): `readSeqsInv`, `isReplica`'s id bound,
  `clusterLockInv`, and the specs `Cluster.start`, `newReplica`, `readSeqs.next` (`id ≤ γ.max`, was `≤ 9`),
  `StartCluster` (premise `γ.max = uint.nat o.MaxReplicas'`), `Run` (the files of `1 … cfg.MaxReplicas`).
- `kdOptsOk` as kvreconf's `OptsOk` (`Voters ≤ MaxReplicas < 2^60`); `RandomOptions`/`RandomConfig`'s posts
  add `MaxReplicas = 9` (what `Main`'s files premise over `1 … 9` needs).
- `kdFileNamesM_nodup` by `decimalB_inj` (the probe's, in `Main.lean`); `kdFileNames_nodup` its instance at 9.
- `MainN.lean` (proof) imports `Main.lean`'s proof module for `kdClockN`, `kdStorInv_alloc` and the file
  lemmas.
