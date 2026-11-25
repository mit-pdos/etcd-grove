# kvraft: a decent statement

`KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/TopLevelRobustness.lean` (origin/lean,
2026-11-24); Upamanyu: "a decent theorem". Its header (not copied) says in a few paragraphs what it
means, the premises, the extensions with their environment assumptions in prose, and what is trusted.

**Good:**
- premises are start state (`dir` an empty root), environment (distinct addresses) and config validity only;
- no Hoare triple or Iris premise; the classes are package assumptions of translations, listed as trusted;
- extensions fixed (`kvraftExts`: net + Linux fs), their assumptions in the header's prose;
- the driver (`kvcheckProgram`, porcupine panics unless `Ok`) states the property;
- a concrete instance (`kvraft_robust_example`) comes with it.

**To improve:**
- `cl.Ok`, `replicas.length < 2 ^ 32`, `dir.length < 2 ^ 39`, `Net.addrOk`: pure facts the programs can
  check; moving into Go (branch `kvnet-single`, P8: the programs `return` on an invalid configuration);
- `threads := 2 ^ 61 + 1, bound := 2 ^ 61`: the right shape (no thread cap; steps at raft's `readyFits` cap),
  but bare: name both and say in the header why `2^61` (kvraft-udp's `kvraftUdpThreads` does);
- bare literals (`2 ^ 32`, `2 ^ 39`): name them;
- the header has history ("adapted here", "added 2026-11-22"): drop it, keep it in `notes/`.

```lean
def kvraft_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
    [field_sem : net.FieldAssumptions]
    [os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]
    [log_sem : log.NewModel],
  ∀ (cl : ClusterConfig) (dir : GoString) (replicas : List (GoString × state)) (σc : state)
    (g : GlobalState),
    cl.Ok replicas.length →
    replicas.length < 2 ^ 32 →
    dir.length < 2 ^ 39 →
    (replicas.map (·.1)).Nodup →
    (∀ a σ, (a, σ) ∈ replicas →
      Net.addrOk a = true ∧                               -- canonical a.b.c.d:p
      dir ∈ (fsOf σ).fs.roots.map (·.1) ∧                 -- dir is an empty root
      ∀ c, (fsOf σ).lookup (joinPath dir [c]) = none) →
    let addrs := List.intercalate go!"," (replicas.map (·.1))
    Robustness.Robust
      (replicas.mapIdx fun i p => (kvraftReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      [(kvcheckProgram cl addrs, σc)]
      g (threads := 2 ^ 61 + 1) (bound := 2 ^ 61)

/-- The example deployment's options: 5 replicas, 3 of them bootstrap voters (the driver adds the
others). -/
def exampleConfig : ClusterConfig :=
  { voters := 3, preVote := true, checkQuorum := true, stepDownOnRemoval := true,
    maxSizePerMsg := 1048576, maxCommittedSizePerReady := 1048576, maxInflightMsgs := 256 }

/-- **kvraft is robust, an example**: replicas 1..5 at 10.0.0.1:7001 .. 10.0.0.5:7001, durable state
in /var/lib/kvraft. A corollary of `kvraft_robust`. -/
def kvraft_robust_example.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
    [field_sem : net.FieldAssumptions]
    [os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]
    [log_sem : log.NewModel],
  ∀ (σ₁ σ₂ σ₃ σ₄ σ₅ σc : state) (g : GlobalState),
    (∀ σ ∈ [σ₁, σ₂, σ₃, σ₄, σ₅],
      go!"/var/lib/kvraft" ∈ (fsOf σ).fs.roots.map (·.1) ∧
      ∀ c, (fsOf σ).lookup (joinPath go!"/var/lib/kvraft" [c]) = none) →
    let addrs := go!"10.0.0.1:7001,10.0.0.2:7001,10.0.0.3:7001,10.0.0.4:7001,10.0.0.5:7001"
    let dir := go!"/var/lib/kvraft"
    Robustness.Robust
      [(kvraftReplicaProgram exampleConfig addrs dir 1, σ₁),
       (kvraftReplicaProgram exampleConfig addrs dir 2, σ₂),
       (kvraftReplicaProgram exampleConfig addrs dir 3, σ₃),
       (kvraftReplicaProgram exampleConfig addrs dir 4, σ₄),
       (kvraftReplicaProgram exampleConfig addrs dir 5, σ₅)]
      [(kvcheckProgram exampleConfig addrs, σc)]
      g (threads := 2 ^ 61 + 1) (bound := 2 ^ 61)
```
