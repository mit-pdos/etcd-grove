# Raft's cluster vocabulary, independent of machine and generation (kvnet decision B, 2026-11-21)

The goal is decision B of `notes/kvnet-proof-plan.md`. kvnet must (i) allocate raft's cluster in
`goose_dist_mixed_crash_adequacy(_init)`'s `Hstart`, which has only `[GooseGlobalGS]`, and (ii) let the
checking client's machine hold `isCluster`. This note is the design section. Branch
`raft-cluster-global` (off `lean` `52c16abb4b`). Nothing is implemented yet: (b) below is a design gap
reported before any work.

## (a) What ties the vocabulary to one machine and one generation

Checked by reading the sources at `52c16abb4b`. A probe that compared `isCluster` at `⟨G, L1⟩` and
`⟨G, L2⟩` by `rfl` did not typecheck, for reason 2 below.

1. **The node table.** `isClusterU γ N := ⌜UniNames γ N⌝ ∗ clusterInv γ N ∗ rdPool γ N ∗ nodeTabInv γ N`
   (`InvApiDec.lean:68`).
   - `nodeTabInv := inv (N .@ "nodetab") (∃ M, ghostMapAuth γ.nodeTab 1 M ∗ [∗map] n ↦ _, ∃ nv, n ↦□ nv)`
     (`InvApi.lean:1701`) holds the heap of the machine and generation that started each node.
   - It serves two purposes. The first is agreement: `nodeTabOk γ n γn := n ↪[γ.nodeTab]□ cfgNamesOf γn`
     makes every description of the node at `n` (`isNode`, `nodeRunning`, `nodeDriver`, `nodeStopped`,
     `nodeArm`, `nodeTagPin`, the snapshot-source facts, the ready-token claim) agree on its names. It
     appears in 15 uses of `nodeTabOk_agree`/`nodeNames_live_agree`. The second is freshness:
     `StartNode`/`RestartNode` insert `n` while they own `n ↦ v` whole, which refutes an entry's `n ↦□`.
   - Keyed by `Loc` alone, it breaks across generations: a restarted generation's heap can reuse a
     dead node's address, whose entry still holds the old names.
2. **The section variables.** Every API predicate is defined in a section with
   `[hG : HeapGS HasLC.hasLC GF] [StorageModel GF] [sem : go.Semantics] [package_sem : …]`
   (`InvApi.lean` has 12 such sections, `InvApiDec`/`InvApiJoin`/`InvApiBoot`/`InvApiDecAlloc`/
   `InvApiView` one each, `InvNode` 3, `InvNodeRule` 2, `ConfPolicy` 1). `sem : go.Semantics` depends on
   `GoLocalContext`, which is the local ghost state's (`goose_go_local_context`). Lean includes
   instance-implicit variables whose dependencies are included, so `isCluster`, `sentMsg`, … take
   `hG`, `sem` and `package_sem` as arguments even where the body uses none of them.
3. **The bodies are global, except the node table.** `clusterInv`, `apiInv`, `rdPool`, `raftStateU`
   (`ownDurGhost`, `termLB`, `inv budgetN`), `nodeVacantU` (`raftIdSlot`), `confAtU`,
   `isCommittedLogLb`, `snapshotCert`, `sentMsg`, `msgCredits` and `confPolicy` all unfold to ghost
   state: `AllG` maps and vars, saved predicates, receipts, and invariants at
   `goose_irisGS.invGS = G.gooseInvGS`. The protocol layer (`Protocol/*`) is already stated over
   `[AllG] [ReceiptGS] [InvGS]`, with `[CrashGS]` only in its crash sections.
   - `nodeVacantA`/`nodeCrashTok` hold the arm's crash invariant, which mentions the generation's
     `crashed`, so they are per generation by design (A). What crosses a crash is `nodeVacant`, which is
     global.

## (b) The node table: design gap

Moving `nodeTabInv` out of `isCluster` means finding a new home for the agreement on node names (a1)
and for the freshness at `StartNode`/`RestartNode` (a2). Agreement needs one anchor per node. Freshness
needs the heap facts of the generation that inserts. Neither fits in a global invariant:
- A global invariant's body is one fixed term.
- The typed `n ↦□ nv` of a node struct depends on the generation's local ghost state (heap name, its
  `inG`, the go state), and a global invariant cannot quantify over "the current generation".

Options considered:

1. **A global registry keyed by a per-generation ghost name** (`goose_go_stateGS.packageInitedName`
   or `goose_crashGS.crashName`, both fresh per generation), with entries `(genKey, n) ↦ cfg`. This
   gives agreement, but freshness needs the entry to carry `n ↦□` at the inserting generation's heap.
   That is not expressible in the global body. Each attempted way around it fails:
   - Saved propositions: a later caller cannot recover which proposition was saved.
   - Quantifying over `L` with the same key: not provable for an arbitrary `L`.
   - A raw heap-name-parametric points-to: would need Perennial to relate each generation's heap `inG`
     to `GooseGpreS`'s.
2. **A per-generation table, allocated once per generation.** Freshness is local. Agreement then needs
   all descriptions in a generation to name the same table, which requires a unique anchor per
   generation.
   - Raft's package initializer runs once per generation (`isPkgInit` is this repository's
     `isInitialized`), but `isPkgInit` is a persistent proposition that another proof could re-prove
     with a different table name.
   - The exclusive per-generation resource Perennial gives (`ownGoState ∅`) is consumed by the package
     initializers.
   - A client-allocated per-generation handle passed to `StartNode`/`RestartNode` works, but then the
     node predicates need the handle as a parameter to agree on it. That is an API change, as in 3.
3. **No table: node predicates take the node's names.** Make the node handle explicit: `nodeRunning n
   γ N q` becomes `nodeRunning nh γ N q` for an opaque `nh : NodeH` (the node's location and names),
   returned by `StartNode`/`RestartNode` (`∃ nh, ⌜nh.loc = n⌝ ∗ …`).
   - No agreement or freshness is needed: the client carries `nh`, and the descriptions of one node
     share it by construction.
   - The cost is an API change of every node-level predicate.
   - Impact, outside raft: `nodeRunning` 57 files/166 lines, `isNode` 28/34, `nodeConfig` 21/53,
     `nodeDriver` 14/28, `nodeTagPin` 4/6, `nodeStopped` 2/2. Inside raft: about 330 lines over the same
     predicates.
   - The clients are kv, kvreconf, kvdurable, the etcd server (`InvRaftNode`, `NodeBridge`, …),
     etcdstart, the trace check, and the generated copies.

Recommendation: 3. It removes the table, which was only internal consistency bookkeeping, and with it
the reuse-of-addresses issue. It needs no Perennial change. Its churn is a mechanical change of the
node predicates' first argument from `n : Loc` to `nh : NodeH`, plus `nh.loc` where code values are
built.

Asked of the coordinator before implementing: 3, or one of 1 and 2 with the Perennial support or the
per-generation token they need.

## (c) The shared predicates at `GooseGlobalGS` (no gap)

Move the definitions and allocation lemmas of the shared vocabulary into sections with only
`[G : GooseGlobalGS HasLC.hasLC GF]` and `attribute [local instance] GooseGlobalGS.gooseInvGS`. That is
no `HeapGS`, `StorageModel`, `go.Semantics` or package assumptions. Under `HeapGS` a client's
`isCluster γ N` then elaborates with `G := hG.goose_globalGS`, and `inv` agrees with
`goose_irisGS.invGS` by unfolding reducible instances.
- **Definitions:** `isClusterU` (without the node table), `clusterInv`, `apiInv`, `rdPool`, `UniNames`
  facts, `raftStateU`, `nodeVacantU`, `confAtU` and `confDecided…`, `isCommittedLogLb`, `snapshotCert`,
  `sentMsg`/`msgCredits` (their `isRaftMsg`/token parts), the read-context facts, `confPolicy`, and the
  sealed wrappers in `InvNode`/`InvNodeRule`/`ConfPolicy`.
- **Allocation:** `cluster_alloc_dec_impl`, `cluster_alloc_boot_impl(_tr)`, `joinAuth_join`.
- **Clients:** kvreconf's/kvdurable's `rkvInv`, `kdSnapInv`, conf policy, and their alloc lemmas
  likewise.
- **Impact:** the definitions move between sections, with no change to their bodies. Lemmas that mix
  heap and cluster facts stay under `HeapGS`.
- **Risk:** a lemma stated under `HeapGS` that `iapply`s a law stated under `G` must unify the two
  instance paths for `InvGS`/`AllG`. They are reducible, but this must be checked on the first file
  (`InvApi`) before the rest.

## (d) Decision (the coordinating session, 2026-11-21)

Option 3, explicit node handles: the node-level predicates take an opaque `nh : NodeH` (the node's
location and names; `nh.loc` for code values), which `StartNode`/`RestartNode` return, and the node
table goes. Also the `GooseGlobalGS` sectioning of the shared predicates and allocation lemmas. The
unification risk of (c) was checked on `InvApi` first: its `api` section moved to
`[G : GooseGlobalGS]` with `gooseInvGS` as a local instance, and `InvNode`, `InvApiView` and
`InvNodeRule` (lemmas under `HeapGS` over those definitions) built unchanged.

Found while doing it: every raft file that declared `[CrashGS GF]` in its section variables (23
files, from A) made all its lemmas take the instance, because Lean includes instance-implicit
variables whose dependencies are included. `CrashGS` is local (per generation), so those lemmas could
not be used at `GooseGlobalGS`. The fix: the variable lines no longer declare it, and the
declarations that use the crash token take it with `variable [CrashGS GF] in`.
