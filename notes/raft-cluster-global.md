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

Correction (2026-11-22): the global sections use `{GF} [AllG GF] [ReceiptGS GF] [InvGS GF]`, as the
protocol layer does, not `[G : GooseGlobalGS]` with `gooseInvGS` as a local instance. With the
latter, a lemma whose conclusion is a fancy update, used under `HeapGS`, could not be eliminated:
`imod` reported "not a modality" (`RestartNode.lean:770`), because the update's instance came from
`G.gooseInvGS` while the caller's comes from `goose_irisGS`. With `[InvGS GF]` as a parameter, a
caller under `HeapGS` synthesizes its own instance, and kvnet's `Hstart` (only `GooseGlobalGS`)
supplies `G.gooseAllG`/`G.goose_receiptGS`/`G.gooseInvGS`. At that boundary the two instance paths
are equal by unfolding.

## (e) Status (2026-11-22, commit `4e73336696`, branch `raft-cluster-global`)

**Done** (raft's `Link` builds):
- `NodeH` (`InvApi`, sealed in `InvNode` with `NodeH.loc`); the node-level predicates take it; the node
  table and `nodeTabInv` are gone (`nodeTabOk γ n γn := ⌜γn = n.names⌝`, so the agreement lemmas
  kept their statements); `RestartNode`/`TracedStartNode` persist the struct and build the handle
  `⟨n_ptr, γn⟩`; `StartNode`/`RestartNode`/`node.*` specs over `nh` (`nh.loc` in code).
- Global sections (`{GF} [AllG GF] [ReceiptGS GF] [InvGS GF]`) in `InvApi`, `ApiVocab`, `InvApiDec`,
  `InvApiJoin`, `InvApiBoot`, `InvApiDecAlloc`, `ConfPolicy`, and `InvNodeChan`'s budget. The
  declarations that need the heap moved to sections of their own (`…Heap<N>`).
- `CrashGS` per declaration in the 22 ghost-level files.

**Left:**
- `InvNode`'s and `InvNodeRule`'s sealed wrappers in global sections. An automated try made a mess
  of the section structure (a wrap crossed an `end api`, which gave `whnf` timeouts) and was
  reverted. Do it by hand: move the shared wrappers (`Cluster.*`, `isCommittedLogLb`, `sentMsg`,
  `msgCredits`, `snapshotCert`, `raftState`, `nodeVacant(A)`, `nodeCrashTok`, `isCluster`, `confAt`,
  `confPolicy`, the alloc laws) into a global section at the top of each file.
- The shared store module (`kvreconf/Store.lean`: `rkvInv`, `opSlot`, `readSlot`, `waitP`, `kvLb`,
  `kvCore`, `kdSnapInv`, the conf policy).
- The clients (kv, kvreconf, kvdurable, the etcd server, etcdstart, the trace check, kvwitness?).
- The generated copies (`etc/gen-raft-tla.py`, `etc/copy-part.py`), Links, interfaces, gates.

The scripts used are in `.lake/tmp/scripts/` of the worktree (not committed): `globsec.py` moves a
section to the global variables, `heapwrap.py` wraps a declaration that needs the heap, `locfix.py`
and `binderfix.py` handle `NodeH` vs `Loc`, and `fixloop.sh` runs them.

## (f) Status (2026-11-22, branch `raft-cluster-global-2`, second session)

**Done in this session:**
- `InvNode`/`InvNodeRule`: every declaration whose statement and proof need no heap or Go semantics is
  in a global section (`section api`, `{GF} [AllG GF] [ReceiptGS GF] [InvGS GF]`), the rest in
  `section apiHeap` runs, in file order (split by a classifier over the built environment, which
  follows each declaration's constants to the heap classes; `.lake/tmp/rcg/Classify.lean`,
  `split.py`). Global now: `Cluster.*`, `isCluster`, `isCommittedLogLb`, `ownCommittedOps`,
  `ownReadCtxs`, the read-context facts, `sentMsg`, `msgCredits`, `snapshotCert`, `raftState`,
  `nodeVacant(A)`, `nodeCrashTok`, `nodeArm`, `confAt`, `confDecided`, `ownConfDecisions`,
  `ownSnapsMade`, `snapMade`, `joinAuth`, `joinAuth_join`, `nodeVacant_arm(D)`, `nodeCrash`, and
  their laws. `nodeVacantA`/`nodeCrashTok` take `[CrashGS GF]` per declaration. Still heap: the
  node-level predicates, `nodeBoot` (its `bootMarshal` is a WP), hence `cluster_alloc(_ns,_traced)`;
  new `cluster_alloc_nb` is the global allocation without a bootstrap log (kvnet's `Hstart`).
- `NodeInstalls.lean` (importable): `NodeH.installs` (a `GName`) and `nodeInstalledIndex_installs`.
  The etcd server pinned its node's location in a `dghostVar` before `StartNode` returns; `NodeH`
  holds functions (not `Pos.Countable`), so the server pins `n.installs` instead.
- Clients: a static sweep (`.lake/tmp/rcg/sweep.py`): a variable a node-level predicate takes as its
  node gets `NodeH` in its declaration's binder (order kept), `#n`/`n @!!` get `.loc`; client
  definitions whose binder changed become node-level predicates at that position (per package),
  to a fixpoint. The server's `RNNames.nl : NodeH` (`#γ.nl.loc` in code).
- The client sections' stray `[AllG GF]` variables (kvreconf, kvdurable, RaftNoAx/KvNet own files)
  are removed (`notes/decisions.md`, "One `AllG`"): with the raft vocabulary taking `[AllG GF]` as an
  instance argument, the second instance made a client's hypotheses and raft's laws different terms.
  Specs that relied on `AllG` to fix `GF` get `(GF := GF)` on their first predicate.
- `kvdurable/Store.lean`: `KdNames`, the namespaces, `kdMask`, `rkvVal`, `opAu`, `opSlot`, `kvCore`,
  `readSlot`, `readReg`, `rkvInvBody`, `rkvInv`, `waitP`, `kvLb`, `readAns`, `kdSnapRecOk`,
  `kdSnapInv`, moved out of `Defs.lean` (statements unchanged) into a global section; `Defs` imports
  it. RaftNoAx's copy (`kvdurablenoax/Store.lean`) is what kvnet imports.
- The server: `RNNames.nl : NodeH`, the apply thread's view option `dv : Option NodeH` (`rnDv`),
  `newRaftNode.spec`'s `nl : NodeH`; the pin holds `n.installs` (`InvRaftNode`, `InvApplyAll`,
  `NodeStartLinked`).
- Generated: Links (kvreconf, kvdurable lose `[AllG GF]`), `etc/gen-raft-tla.py`, `etc/copy-part.py`
  (RaftNoAx's own `ApiVocab.lean` got the main tree's section changes by hand: the patch of
  `52c16abb4b..a8aef4766c`).
- `lean` merged at `c912d6c4e0` (its `0c9b410886`).
- Posted the heads-up on #22.

- The full `lake build` is green; Links, `gen-raft-tla`, `copy-part`, `gen-init` up to date;
  interfaces regenerated (raft, etcdstart); `tier-check` and the raft API's layout check pass.

**Left:** kvnet itself should use `cluster_alloc_nb` and `kvdurablenoax/Store.lean` (the copy KvNet
imports) in its `Hstart`. The sweep's scripts are in `.lake/tmp/rcg/` of this worktree (not
committed).
