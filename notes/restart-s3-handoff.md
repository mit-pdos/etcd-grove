# Restart S3 handoff (2026-11-11, branch `restart-s3`, from `lean` `47d7b2f2cd`)

Phase: **implementation, steps 1-2 done (and item 1, `memStorRestarted` defined); next: items 6, 5,
7, 8, then the build and checks** (the second agent stopped at its context budget, 2026-11-11). The
decisions D1-D5 are in `questions.md`; the forms this agent decided are there too ("Restart S3
implementation").

For W4/C3: the enter-at-durability pitfall below goes into the W4 brief (the coordinator's decision).

## Done (implementation, 2026-11-11)

- `b17934556f` step 1' (D2 (b)): `bootstrappedWAL.MemoryStorage` translated (goose config, regenerated
  from the pin **`a4d2bb172`**, see pitfalls); `Proof/.../etcdserver/BaseRestartStor.lean`
  (`walSnapCS`, `memStorRestarted`, the body below); spec and proof
  `bootstrappedWAL__MemoryStorage.lean` (its post is `memStorLock ∗ memStorRestarted`), linked in the
  server's `Link.lean` (`etc/link-lean-first-server.txt`); item 1: `InvRestart.lean`'s opaque removed
  (it imports `BaseRestartStor`). **Raft spec change** (form, recorded): `MemoryStorage.ApplySnapshot.
  spec` is now `(old triple) ∧ (index-0 triple)`, callers use `.1` (kv `KVStorageInstance`, kvreconf
  `KvrStorageApi`, kvdurable `openStorage` x2 and `Replica__run`, `raftNode__start`). The index-0
  triple is what base `0` (a WAL with no later snapshot record) needs.
- `02fd510023` step 2: `srvMem_restartStorage` (`NodeStart.lean`): `memStorReg ∗ memStorLock ∗
  memStorRestarted ∗ (⌜σ.b = 0⌝ ∨ snapshotValid γr.cl (walSnapCS σ cs)) ∗ F-maker ⊢ restartStorage
  γr.cl (memStorIface ms) σ cs A F`, premise `σ.b ≤ σ.commit`, freeze point `σ.b`.
- `591b31a388` step 2: `srv_confAt_eq_simple` (Q39 at every committed index) and `walSnapCS_valid`
  (`srvRaftLogInv ∗ walSnapCert cl σ ⊢ |={E}=> ⌜σ.b = 0⌝ ∨ snapshotValid cl (walSnapCS σ cs)`, given
  `hterm`, `hcs`, `hcsb`), both in `NodeStart.lean`.
- Checked with `etc/lean-check.py -a` (kernel included): `MemoryStorage__ApplySnapshot`,
  `bootstrappedWAL__MemoryStorage` (spec, proof), `InvRestart`, `NodeStart`. **Not yet built**: the
  six `.1` call sites, the server's `Link.lean`, raft's `Link`/`Linked`/`Results`, and every
  importer (the raft spec change and the `Code` change rebuild most of the tree): the next build
  must cover them (`etc/importers.py --leaves`).

## Next, in order

1. Targeted build of the changed callers first (cheap check of the `.1` edits):
   `Proof/github_com/mit_pdos/etcd_grove/examples/raft/{kv/KVStorageInstance,kvreconf/KvrStorageApi,
   kvdurable/openStorage,kvdurable/Replica__run}.lean`, `raftNode__start.lean`, the server's and raft's
   `Link.lean` (under the 64G cap; it rebuilds raft's importers up to them).
2. Item 6: `newRaftNode`'s binders `a0 t0 L₀ commit0 snap0` (review 4, frozen form).
3. Item 5: `bootstrappedRaft.newRaftNode`'s `RestartNode` branch (Q35 (a), the boot sum), using
   `srvMem_restartStorage` (its `snapshotValid` disjunct from `walSnapCS_valid`; `hterm`, the base
   term and the entries' numbering from W4's `walRead_wf`; `σ.b ≤ σ.commit` from `StorageHolds`).
4. Item 4 (InvWal restart AU, minimal: W4 rebases on S3), item 7 (`rnRestartOk` into `isRaftNode`;
   start/stop at `P`), item 8 (`NodeStartSpecR`, separate; `NewServer.lean` untouched; exported
   `server_raft_node_start` restated in Link/Results).
5. Full build under the lock and the 64G cap; `etc/tcb-report.py --check` (the opaque
   `memStorRestarted` is gone: trusted text change allowed by D2 (b)), collections,
   `etc/gen-interface.py etc/api/raft.txt` (the `ApplySnapshot` spec: interface diff), `etc/gen-init.py
   --check`, `etc/goose.py --check --project etcd` (needs the pin's source, see pitfalls); STATUS; STOP
   before `etc/land.sh` with the changed frozen and exported statements and the tcb diff.
6. Before landing: delete the untracked `Scratch/S3Probe.lean` (the first S3 session's probe; the copy
   stays in `/shared/tmp/restart-s3/`).

## Done (probe, the first session)

- **Probe (scratch, never lands)**: `Scratch/S3Probe.lean`, which is untracked. It holds the
  proposed `walSnapCS`, `memStorRestarted` body, `rsPartial`, `PendBatchM`,
  `StorageHoldsCrash`, `DeepArm`, and three small lemmas. It elaborates with 0 errors, axioms
  `[propext]`. Check it with
  `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json TMPDIR=/shared/tmp etc/lean-check.py -a Scratch/S3Probe.lean`.
  A copy is in `/shared/tmp/restart-s3/S3Probe.lean`.
- Go sources at the pin `673da07c8f` were read from `/shared/etcd-goose-lean-walsnap`
  (`git show 673da07c8f:...`). Copies of `bootstrap.go` and `wal.go` are in `/shared/tmp/restart-s3/`.

## Probe findings (R-C1 under power loss)

Write `S` for the entered durable state (`raftState`). Write `pb` for the batch that was cut and
whose `Save` began, but which was not yet entered (there is at most one: the loop is sequential).
After a power loss, `walRead I` returns one of these:

1. **A lower commit** (commit-only `HardState`s lost). This is already inside `StorageHolds S σ`:
   its commit range `[S.wcommit, S.commit]` covers it. Every batch that writes entries is
   `mustSync`, so its state record, at `wcommit`, is synced before the enter. **No change.**
2. **The whole batch** (its state record survived, but it was not entered):
   `StorageHolds (pb.next S) σ`. Before `RestartNode`, a crash-time enter of the pending batch is
   needed (the existing `raft_enter`, with `pendBatch`/`batchOk` kept in a crash-stable invariant).
   This is an **extension** (C6/InvWal design), with no protocol change.
3. **A torn batch, same term** (the first `k ≥ 1` entries survive, the state record is lost, and
   the batch's entries come from the leader of `S.term`): `StorageHolds (rsPartial S es k) σ`.
   The log keeps every term `≤ S.term`. `hist`'s okL can cite the leader of `S.term < bndD`. An ack
   at `S.term` lies below the batch's first index, because raft truncates only at the first
   conflict, and an ack at the current term agrees with the log. So `durPers` at the partial state
   follows from `durPers S E` plus `batchOk`'s `durPers` of `pb.next S`, as a pure prefix argument.
   **Extension**: a new ghost rule `raft_enter_prefix` (pendBatch ⇒ `ownDurGhost (rsPartial …)`,
   the batch's promises discarded, never sent) and a lemma `durPers_prefix`. `RestartNode.spec`
   stays unchanged, because the client updates `raftState` before calling it.
4. **A torn batch of a new term** (the batch raised the term to `T > S.term`, which happens when a
   follower gets a `MsgApp` at a higher term: one `Ready`, one `Save`, entries before the state):
   the log can hold entries of term `T` (`DeepArm`). Even entries of term `≤ S.term`, taken from
   leader `T`'s log, can break `hist` at `bndD S kd`. This violates two invariants by their
   definitions:
   - `TermsLe` (`Protocol/GhostState.lean:501`: "No term in a node's full log is above its own"),
     with about 15 uses in Protocol/RawNode;
   - `durPers`'s term bound together with `hist`'s bound `bnd s`/`bndD`, with about 25 uses.

   The protocol is still safe:
   - the node never sent anything at `T`;
   - `T`'s winning quorum has durable term `≥ T` and voted at `T`, so the node cannot win at any
     term `≤ T`;
   - a stale leader of `S.term` that overwrites the term-`T` entries cannot commit, by quorum
     intersection.

   But the argument is new. It needs a ghost "knowledge term" separate from Go's term, and a new
   election lemma ("an entry of term `T` blocks every win at `≤ T`"). **This is a deep change**:
   Protocol `Ghost.lean`/`GhostState.lean`/`StepGhost.lean`/`Enter.lean`/`Refinement.lean`, and a
   rebuild of every raft importer.

**Verdict: R-C1 is an extension for arms 1-3 and a deep change for arm 4.** None of it touches S3's
graceful Lean. `memStorRestarted` is crash-agnostic (below). The crash arms belong to C3 / rung 2
(scope.md's ladder), and to InvWal's crash clause (W4).

**C3/InvWal pitfall** (not a bug): the enter point must be the batch's durability point. That is
after `Save` for a `mustSync` batch or a commit-only one, but after `Sync` (`raft.go:279`) for a
snapshot batch that is not `mustSync` (`MustSync` ignores snapshots). Otherwise a lost state
record makes `walRead` drop the snapshot record (index above the saved commit) and read the
pre-snapshot base, below `S.base`, which no arm accepts. Today's graceful proof enters after
`Save`, which is fine only for graceful stops.

## Proposed definitions (from the probe)

```lean
def walSnapCS (σ : StorContents) (cs : ConfStateM) : SnapshotM :=
  SnapshotM.mk [] (SnapshotMetadataM.mk cs σ.base.index' σ.base.term')

def memStorRestarted (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM) : IProp GF :=
  memStorFresh ms γs σ.b (walSnapCS σ cs) ∗ memStorMeta ms γs σ.hs ∗
  memCompacted γs σ.b ∗ memLog γs σ.b DFrac.discard [memDummy (walSnapCS σ cs)] ∗
  memSnapLb γs σ.b ∗ memLog γs (σ.b + 1) (DFrac.own 1) σ.ents ∗ memEnd γs (σ.last + 1)

-- C3 / rung 2, not trusted text before R6:
def rsPartial (S : RaftState) (es : List EntryM) (k : Nat) : RaftState :=
  { S with ents := appendEnts S.base S.ents (es.take k) }
def StorageHoldsCrash (S : RaftState) (pb : Option PendBatchM) (σ : StorContents) : Prop :=
  StorageHolds S σ ∨ ∃ b, pb = some b ∧
    (StorageHolds (b.next S) σ ∨
     ∃ k, 0 < k ∧ k ≤ b.es.length ∧ b.snap = none ∧ StorageHolds (rsPartial S b.es k) σ)
```

- `memStorRestarted` is exactly what `NewMemoryStorage`, then `ApplySnapshot(walSnapCS σ cs)`, then
  `SetHardState(σ.hs)`, then `Append(σ.ents)` leave by their proved specs (`bootstrap.go:741-753`).
  It needs no raft ghost and has no crash case: `σ` is whatever `walRead I` returned.
- v3.7's `ApplySnapshot` accepts index 0 on a fresh storage (`msIndex != 0` guard), and
  `bootstrap.go:107-115` always sets the snapshot (with the backend's `ConfState`). So the
  definition needs no case split.
- `Append`'s premises (entries consecutive from `σ.b+1`, `σ.last ≤ 2^61`) must come from W4
  (`walRead_wf`, requested below).
- `restartStorage` follows by `srvMem_restartStorage`, generalizing `srvMem_bootStorage`
  (`NodeStart.lean:254`):
  - freeze point `σ.b`;
  - `memStorInv_alloc` at `c = σ.b`;
  - `snapshotValid γ (walSnapCS σ cs)`, from `walSnapCert` (`InvWal.lean:397`) plus Q39 plus
    `confStateIs cs (simple cfg)`. The last of these is a premise here; S6 discharges it from the
    backend's members, H10.
- **Q39's law exists**: `srv_confAt_simple` (`SrvRaftLog.lean`, every `k ≤ |l|` of a committed
  `l`) with `confAt_agree` (`InvNodeRule.lean:310`) gives `confAt cl k m → m = simple cfg` at
  every committed index. The R-S3 fallback is not needed.

## Plan for S3's Lean (graceful track; sizes est.)

| # | File | Change | Lines | Shared with |
|---|---|---|---|---|
| 1 | `Proof/.../etcdserver/InvRestart.lean` | `memStorRestarted` defined (+ `walSnapCS`); `Hrest` unchanged in shape. **Trusted text: Freeze, HS2 re-attack** | +40 | **W4/S2** (bootOkR's WAL slot, `bootstrapRestartContract`): S3 edits only `Hrest`/`memStorRestarted` |
| 1' | (D2 (b)) `Code/.../etcdserver.toml` + regen; new `Spec/.../etcdserver/bootstrappedWAL__MemoryStorage.lean`, `Proof/...` | translate `bootstrappedWAL.MemoryStorage` with its body; prove its post is `memStorRestarted` | +1 config, +60 spec, +180 proof | — |
| 2 | `Proof/.../etcdserver/SrvRaftLog.lean` | `srv_confAt_eq_simple` (Q39 at every committed index) | +30 | — |
| 3 | `Proof/.../etcdserver/NodeStart.lean` | `walSnapCS_valid`, `srvMem_restartStorage` | +250 | stage B: `NodeStartSpec` feeds `NewServer.lean` (D5) |
| 4 | `Proof/.../etcdserver/InvWal.lean` | the restart AU (`StorageHolds S σ` from `ViewOk` at the identity image) for `RestartNode` | +80 | **W4** (rnDurInv moves to `walDisk`; S3 takes `walRead I = some σ` + the identity instance) |
| 5 | `Spec/` + `Proof/.../bootstrappedRaft__newRaftNode.lean` | the `RestartNode` branch (Q35 (a), the boot sum) | +60 spec, +250 proof | — |
| 6 | `Spec/` + `Proof/.../newRaftNode.lean` | binders `a0 t0 L₀ commit0 snap0` (review 4, frozen form) | +10, +40 | — |
| 7 | `InvRaftNode.lean`, `raftNode__start.lean` (+ `raftNode__stop` spec if needed) | `rnRestartOk` into `isRaftNode` (`rnCfgAt := rnView`, review 5); start/stop at `P` (Q34 (a)) | +80, +150 | — |
| 8 | `NodeStart.lean` | `NodeStartSpecR` (restart arm), a separate spec (D5); exported `server_raft_node_start` restated in Link/Results | +100, +20 | stage B (NewServer, S6) |

Total about 1200-1350 lines. Two targeted builds per round; one full build at the end (the
`InvRaftNode` importers). C3 (crash arms) is separate: rung 2 / C3, after W4.

**Requests to W4** (interface; S3 consumes and does not invent):
- `walRead_wf : walRead I = some σ → (∀ j e, σ.ents[j]? = some e → e.Index = σ.b+1+j) ∧ σ.last ≤ 2^61`;
- the restart slot gives `walRead I = some σ` with the identity instance at a graceful stop
  (`walImg_full`, `walRead_graceful`);
- for C3, InvWal's crash clause in the form `StorageHoldsCrash S pb (walRead I)`, where `pb` is
  the batch whose `Save` update fired and which was not entered. Its proof uses the
  enter-at-durability-point rule above.

## Decisions needed (recommendations)

- **D1, R-C1 arm 4** (torn batch of a new term):
  - (a) the deep protocol change: a knowledge term, `TermsLe`/`hist` bounds widened, the election
    lemma. Est. 5-8 wk, which grows C3 from 3-6 wk to 6-10 wk;
  - (b) a fork change: a `Ready` that raises the term and carries entries first saves its
    `HardState` alone (synced). This reduces arm 4 to extensions. It is a code change made for
    the proof, not for a bug;
  - (c) a scope assumption: dishonest under power loss.

  **Recommend (a)**, decided at rung 2's Scope. First do a 1-week paper proof of the election
  lemma (de-risk). It does not block S3.
- **D2, `memStorRestarted`'s justification**:
  - (a) a trusted definition as drafted;
  - (b) translate `bootstrappedWAL.MemoryStorage` with its body and prove the definition is its
    post. The trusted text then says only that bootstrap's storage is that method's result on the
    read `σ`, `cs`.

  **Recommend (b).**
- **D3, the arms 2-3 rules** (`raft_enter_prefix`, a crash-time enter of the pending batch): raft
  API laws at C3. They are not trusted text, but they change raft's API (`etc/api/raft.txt`).
  Recommend: approve as C3/rung-2 scope.
- **D4 (form, decided at the checkpoint)**: freeze point `σ.b`; Q39 as `srv_confAt_eq_simple` at
  every committed index; `confStateIs cs (simple cfg)` a premise of `srvMem_restartStorage`,
  discharged in S6.
- **D5**: the restart arm as a separate `NodeStartSpecR`, so that `NewServer.lean` (stage B, S6)
  is untouched in S3. Recommend yes.

## Pitfalls

- `.lake/go-src/etcd` lacks `673da07c8f`; read Go from `/shared/etcd-goose-lean-walsnap`.
- `Scratch/` is untracked and must never be committed or landed.
- A name `RaftState.foo` declared inside a nested namespace is not reachable by dot notation (the
  probe uses `rsPartial`).
- **The etcd pin of the Goose translation is `a4d2bb172`** (`etc/goose.py`, branch
  `goose-lean-purgesnap`), not `673da07c8f` (the Go-test pin of the common rules). Regenerate with a
  clone at it: `git clone --shared --no-checkout /shared/etcd-goose-lean-walsnap X; git -C X fetch
  /shared/etcd-goose-lean-purgesnap a4d2bb172...; git -C X checkout a4d2bb172...`, then
  `etc/goose.py --project etcd --src etcd=X` (one is at `/shared/tmp/restart-s3/etcd-src`). From
  `673da07c8f` the diff also shifts line numbers in `server.go`.
- Iris proof mode: `rw … at H` does not reach an Iris hypothesis (Unknown identifier); `rw` on the
  goal rewrites the whole Iris context, or restate with `ihave H' : … $$ [H]`. Two `match`es from
  different files are different auxiliary functions: `cases o` before `iexact`. A `wp_join … with
  [hyps]` sees only the listed hypotheses: include the pointer cells the branches load.
- Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
  --packages=/shared/tmp/manifest-ddc.json build <targets>`.

