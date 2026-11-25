# kvraft: the proof plan for `kvraft_robust` (2026-11-20)

The theorem: `notes/kvraft-robust-goal.md`. The user's instruction (2026-11-20): before proving, make
sure the proved intermediate specs (the Iris WPs) suffice for the new theorem, and plan so that no
proof is redone. This note is that check and that plan. Source: a read-only survey of the sources
(2026-11-20, a fresh agent), its two load-bearing claims re-checked by hand (marked ✓).

## Verdict: the proved specs are not yet sufficient

What carries over as it is: the store-level linearizability argument (kvreconf/kvdurable's `rkvInv`,
operation slots, `waitP`/`kvLb`, the read registry: all ghost), raft's message layer (`sentMsg`,
`stepIn_intro`, `msgCredits_copy`, `snapLocalMsg_noDir`: every resource a message needs is
persistent, so it can travel as bytes), `Replica.propose`'s interface (a persistent precondition
`d ↪[ops]□ γp`, the postcondition `waitP`), fsExt's `durable.Write` (in `WalTester/`), the net
function specs (`Net/Spec/net/*`) and the connection laws (`GooseLang/Ext/Net/Proto.lean`).

What is missing, each a gap that would force re-proving if found late:

1. **Raft has no real-crash law.** ✓ `nodeVacant` (needed by `RestartNode`,
   `Spec/go_etcd_io/raft/v3/RestartNode.lean:100`) comes back only from `node.Stop`
   (`node__Stop.lean:36`) or at `StartNode`; it is `raftIdSlot` (generation share, `slotFree`,
   leader-side ghost authorities), owned by the running node's threads. A killed process's threads
   take it with them, so the next incarnation cannot restart. kvdurable avoids this by crashing
   cooperatively (`Replica.crash` → `node.Stop`, `examples/raft/kvdurable/kv.go:374-389`).
   `notes/raft-durability-plan.md` §3.2 once proposed the missing law (`□(crashed -∗ halted ι)`);
   not adopted.
2. **Raft's cluster invariant is tied to one heap.** ✓ `isClusterU` includes `nodeTabInv`
   (`Proof/go_etcd_io/raft/v3/InvApiDec.lean:68-69`), which holds `n ↦□ nv` for every node
   (`InvApi.lean:1696-1698`): local heap, not shareable across machines and generations. And raft's
   predicates are over `[HeapGS]`, while `goose_dist_crash_adequacy`'s `Hstart` has only
   `[GooseGlobalGS]` (`Perennial/GooseLang/DistAdequacy.lean:744-760`), so the cluster cannot be
   allocated where shared invariants are.
3. **No adequacy for crashing and stable machines together.** `goose_dist_crash_adequacy` makes
   every node prove a crash obligation (`DistAdequacy.lean:766-768`); kvcheck cannot (restarted, it
   would reuse operation ids). Known (`notes/robustness.md`).
4. **The parts do not compose, and the main raft is not axiom-free.** kvraft needs bodied `net`
   (`Net/` part), bodied `durable` over fsExt (`WalTester/` part), and raft without hand-written
   axioms (`RaftNoAx/`); each part shadows main-tree names (`lakefile.toml`), e.g. two
   `wp_initialize'` for `os`. kvraft's Go module pins the main raft (`examples/go.mod:16`), whose
   proofs rest on `proto` axioms (`notes/raft-noax-part.md`): outside the goal's trust base.

## Interfaces to freeze before any kvraft proof (each, decided late, redoes proofs)

- **A. Raft's crash law** (first: it changes raft's API and its run-loop proofs). **Decided
  (2026-11-21): route 1, the crash invariant** (`notes/raft-crash-law-design.md`): `raft_stop`
  (`Protocol/Enter.lean:1866`) already works from any state and needs only six timeless exclusive
  pieces (half the virtual maps, `slotLive 1 g`, the four leader-side authorities), changed only at
  the win, the cut, the enter and start/restart/stop; they move into a per-id
  `inv ((∃X, view ½ X ∗ pieces X) ∨ crashed ∗ tok)`, `nodeVacant_arm`/`nodeCrash` the new laws,
  `notCrashed` threaded at cut/enter/win (`wp_notCrashed_acc`). About 1000-1500 lines, mostly
  mechanical; main risk the traced instance's win gate (`StepG`). Was: `StartNode`/
  `RestartNode` give a per-generation resource with a law of the shape
  `crashed ∗ nodeCrashable n γ N id ={E}=∗ nodeVacant γ id`, covering a batch cut but not entered
  (`raftIdSlot`'s `slotFree` is broken by a pending cut). Two ways: keep the slot in an
  `inv (… ∨ crashed ∗ tok)` (the `durInv` pattern), or give each incarnation fresh slot and
  leader-side names. Either touches `InvNodeRun.lean` (2820 lines). Also decide whether kvdurable
  keeps the `node.Stop` path, and what the etcd server's uses of `RestartNode` see.
- **B. Machine- and generation-independent ghost vocabulary.** Move `nodeTabInv` out of
  `isCluster` (into `isNode`, or a per-generation invariant); state the shared predicates at
  `GooseGlobalGS`, or prove (by `rfl`) that they do not depend on the local ghost state:
  `isCluster`, `sentMsg`, `msgCredits`, `raftState`, `nodeVacant`, `confAt`, `isCommittedLogLb`,
  `snapshotCert`, the read-context facts, kvraft's `rkvInv`/`kdSnapInv`/conf policy. Raft's
  allocation lemmas usable in `Hstart`. Changes every client spec's signature: before any kvraft
  proof.
- **C. What crosses a crash.** Only `raftState γ id S` with the store's per-id ghost (writer,
  snapshot certificate), `nodeVacant` (A), and fsExt's `durSt`. Within a generation,
  `inv (body ∨ crashed ∗ tok)` holds `durInv`/`durSt`, the writer half and
  `StorageHolds S (decode cur-or-alt)`, rebuilt at boot (`durInv_crash` → `durBoot`). Raft's
  "entered" must fire at `durWriteSync`, not at the rename (a crash between them may restore the old
  file). Freeze `persist`'s spec on these two updates so `Replica.run`'s proof sees only an abstract
  persist/`dmu` interface.
- **D. Where the proof lives and which raft it uses.** **Decided (2026-11-21, under the user's
  "you have a clear goal: prove the theorem"): the axiom-free raft.** Done on the Go side: kvraft is a Go
  module of its own (`examples/raft/kvraft/go.mod`, raft replaced by `RAFT_NOAX_REV` as kvdurablenoax's,
  `GO_MOD_PINS`), with kvdurablenoax's substitutions (`pb.CloneConfState`/`CloneSnapshot`,
  `pb.UnmarshalConfChangeV1/V2`, the timer `withTimeout`), and no clock at all: connection deadlines
  are timers that close the connection (`timeout.go`, `closeAfter`), so Perennial's `time.Now` axiom
  is not reached. Was: To keep the trust base, build on the axiom-free
  raft (`RaftNoAx/`), kvraft its own Go module as `kvdurablenoax` is; a part importing RaftNoAx, Net
  and bodied `durable` (reconcile the two `os` inits), or first retire the main tree's names-only
  `net` and trusted `durable`. Copy kvdurable's files with `etc/copy-part.py`, never by hand.
- **D2. The part.** kvraft's proof needs three trees that today are separate parts, each declaring
  main-tree names: raft-noax (`RaftNoAx/`, ~1260 files, generated by `etc/copy-part.py` from the main
  tree), the bodied `net` (`Net/`, 263 files), the bodied `durable` over fsExt (`WalTester/`, 195
  files). Plan: a new part `KvRaft/`, made like `RaftNoAx/`: `etc/copy-part.py` generalized to more
  than one source root (RaftNoAx's copies and own files, Net's `net`, WalTester's `durable`), plus
  kvraft's and kvcheck's translation (a new `etc/goose.py` project, `kvraft`, into `KvRaft/`);
  initializers and Links as RaftNoAx's (`etc/gen-init.py` `PARTS`, `etc/gen-link.py`). Alternative
  that shrinks it: first move the bodied `durable` into the main tree (CLAUDE.md: WalTester is
  temporary until kvdurable moves off `durableExt`). After the crash-law design (A), since A changes
  raft's files that the part copies.
  Checked (2026-11-21): Goose (Perennial `lean` at `19fd486f6`, no configuration) translates
  `kvraft` and `kvcheck` with no unsupported construct and no axiomatized declaration (10.6k and 1.0k
  lines).
- **E. The request/reply protocol.** Per replica address: a hello byte, then either peer frames,
  each `putMsg(st)` with `sentMsg γ src st`, or one client frame (`ReqPropose d` with
  `d ↪[ops]□`, or `ReqRead seq key` with the client-minted read-context facts and
  `readCtxAfter l0`); the reply frame answers what `sentLb` says was asked (`waitP γ d v`, or
  `∃ L, kvLb L ∗ L0 <+: L ∧ v = kvFold L key`). Everything persistent: nothing exclusive crosses the
  wire. kvcheck mints read contexts, so it needs `isCluster` (another reason for B). Freeze
  `Replica.propose`/`read(seq, …)` with persistent preconditions.
- **F. Mixed adequacy** (Perennial, independent): only a prefix of the machines has boot programs;
  the others get no crash obligation.

## Order

1. Freeze A, B, C's persist spec, E, and the list of net laws used (on paper, user's sign-off on A
   and D: they change raft's API and the build's structure).
2. Perennial (now): F; the `ExtSemantics.init`/`globalInit` change (goal plan item 1), coordinated
   with the agent working on net.
3. Raft (now, after 1): B, then A; regenerate the RaftNoAx copies; re-check kvdurable.
4. Store layer (after 3): `persist` over fsExt `Write`; `run`/`request`/`snapshot` over the abstract
   `dmu`; `read(seq)`; `StartNode`'s boot (`durable.Read` → `openStorage` → `RestartNode`).
5. Codecs and wire (now): `putMsg`/`getMsg` against raft's message predicates; `readFrame`/
   `writeFrame` (`examples/net/wire`'s `ReadFull` as the pattern).
6. After the net rework: `Transport`, `serve`/`serveClient`/`handle`, `RunNode`'s Listen retry and
   accept loop (`acceptloop`'s thread tokens), kvcheck's request client.
7. kvcheck: `Check` from kvdurable's `Run`/`Main` and lintest (`lintest/Run.lean:49`: timeout 0
   gives `Ok`-or-`Illegal`; `applySpec` an AU over `libState`), the Read prophecy as kvdurable's.
8. Last: the `kvraftExts` bundle, `Hstart` (cluster, store, per-address tokens, every id's slot), the
   per-node crash frame, `kvraft_robust`, the non-vacuity lemma, the corollary.

Risks, largest first: A (open design, reaches raft's run loop), D (build structure), B.
