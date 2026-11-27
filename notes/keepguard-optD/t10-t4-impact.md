# Keep guard reverted, boot fix (D): what it does to T4 and T10 step 3 (B)

For the etcd_safe lead / etcd-grove-03, 2026-11-27 (#50: Upamanyu's decision to revert the fork's keep guard and
fix the backend-ahead restart at boot, branches A/B of `review.md` beside this file). Read-only analysis of branch
`etcd-safe-t10s3b-a/2026-11-27` at `c9a99a9c42` and of B4 (`etcd-safe-crash-b4r/2026-11-26` @ `700f58c79f`,
`notes/etcd-dist-b4.md`). Nothing built. `P` = `Proof/go_etcd_io/etcd/server/v3/etcdserver`, `S` = the same under
`Spec/`. Line numbers are at `c9a99a9c42`.

## 0. The one-line consequence

After the boot step, every crash restart with `σ.b ≤ i` is, **at the records the boot step leaves**
(`σ' := bootFix σ i t cs`), exactly the graceful restart's shape: `σ'.b ≤ i ≤ σ'.commit` (A: `σ'.b = σ.b`,
`σ'.commit = i`; B: `σ'.b = σ'.commit = σ'.last = i`), and `σ' = σ` when `i ≤ σ.commit`. So the crash case
`σ.commit < i` stops being its own proof. It becomes the graceful proof run at `σ'`. Most of (B) was built to
carry `σ.commit < i` through the running server. That work is no longer needed, and most of it can be
reverted. The new cost moves to **boot**: a raft law that moves `raftState` at boot, a term fact about the
backend, and restated bootstrap contracts.

**On the lead's Branch A question (replay below `ci`).** raft starts with `applied = max σ.b Applied` and
`Applied = 0` (`rnRestartCfg`), so `applied = σ.b`, not `ci`. Under A, raft hands out `(σ.b, ci]` again. Each of
those entries has `shouldApplyV3 = false`, so it is replayed v2-only, as at a graceful restart today: the graceful
image also has `σ.b ≤ i ≤ σ.commit` and replays the same window. The difference from today's crash case is that
`commit0 ≥ |a0| = ci` from the first `Ready` on. So the window `(snap0, |a0|]` lies inside raft's commit:
`rnRestartOk`'s `|a0| ≤ commit0` holds. And every leader snapshot `k` that raft hands out has
`k > committed ≥ |a0|`, so A8 holds: `rnRestartOk_winAbove`, `P/InvRaftNode.lean:633`. T10's replay machinery
(`restReplay γr rp A`, `rp = ⟨σ.b, A₀⟩`, `restReplay_close`, `epReplayCfg`'s window disjunct) needs nothing
new: it is the graceful restart's, which is proved. Under B the window is empty (`σ'.b = |A₀|`): no entries,
`initialReplayTerms = nil`, and the merged-snapshot window branch is never taken (`diskSnapshotIndex = ci`).

## 1. T10 step 3 (B): which items are no longer needed or are simpler

| Item | Verdict | Why |
| --- | --- | --- |
| **B5 step 2** (`applyAll.specKeep`, the run's keep arm, `hwin`'s other case) | **gone** | Without the guard, `applySnapshot` never keeps the backend. raft refuses every `k ≤ committed`, and `committed ≥ ci` from boot on. Session 10's stale-member-attribute finding was about the guard only, so it is moot. |
| `applySnapshot.specKeep` (`S/EtcdServer__applySnapshot.lean:290`), `wp_proofKeep` (`P/EtcdServer__applySnapshot.lean:414`), its Link line | **gone** with the Go revert | the lead's list |
| `applySnapshot.specSnapM`'s strict `hle : ciEff < k` (`:112`) and its `ConsistentIndex` callee in `applySnapshot_walk` (T4 round 3) | **revert** to the pre-guard `specSnapM` | They exist only to refute the guard's branch. |
| **B5 step 1** (`rnApSnap`'s second `notifyc` deposit `rnReplayJob …`, `P/InvRaftNode.lean:2484`; `S2` in `applySnapshot.specSnapM`/`applyAll.specSnapM`, `SnapApplyWalk`, `ApplyAllSnap`, `run_job_snapC`) | **revertible** | It was needed for a *kept* snapshot (`k < |a0|`), where `rnReplayState.empty`'s `|a0| ≤ k` fails. With A8 true, every snapshot `Ready` has `k > |a0|`, and the pre-B5 evidence (`taReplayField`, `.empty`) suffices. |
| **B6 part 2** (drop `rnRestartOk`'s `|a0| ≤ commit0`, `P/InvRaftNode.lean:584`; drop `rnApSnap`'s A8 bound; drop `raftNode.onStop.spec`'s `S/raftNode__onStop.lean:52`) | **gone. Keep the bounds.** | Both are TRUE at boot: `commit0 = σ'.commit ≥ i = |a0|`, and A8 follows from raft's `restore` refusing `k ≤ committed`. So packet row 6 is never made. |
| **B6 part 1** (`rnReplayHist` without `replayPending`, packet row 5) | **revertible** | It only removed `.empty`'s `|a0| ≤ n`, which the keep case needed. |
| **B7** (`rnStopImage`'s `a0 ≤ σ.commit`, `P/InvRaftNode.lean:2649`; `raftNode.stop`'s `S/raftNode__stop.lean:58`; `wal.stopImage`'s `i ≤ σ.commit`, `P/WalApi.lean:750`) | **gone. Keep the bounds.** | A crash-restarted incarnation now satisfies them: `|a0| ≤ commit0 ≤` every later commit. Its graceful stop's `ai ≤ commit` holds as today. The crash image (`wal.crashImageR`) never had the bound. Packet rows 7 and 8 are never made, so **`Serve_dist` is untouched**. |
| **B8 (i)** `σ.commit < i` | **becomes "boot raises commit to `i`"** | `specRAt` is used at `σ'`. This needs the restated `bootstrapAtR`/contract (§3, items 1-2) and the raft boot law (§4, item 1). No B5, B6 or B7 work. |
| B8 (ii) `confRowW`'s second case | done (session 11). **Keep.** | `confAt_committed` is also what branch B's `CS = conf at ci` uses (§4, item 3). |
| **B8 (iii)** `i < bootLen` | **unchanged. Still the lead's decision.** | The boot step fires only when `ci > Commit_w`, and `Commit_w ≥ bootLen` (F-B1 / C-I2's antecedent). So `i < bootLen` implies `i ≤ σ.commit`, and the step does nothing. It gives `bootLen ≤ σ'.commit` (which F-B1 already gave), but **not** `bootLen ≤ i`. The fix stays as session 11 proposed: `srvDiskImageAt`'s and `bootstrapAtR`'s `⌜bootLen ≤ i⌝` becomes `⌜bootLen ≤ σ.commit⌝`. The only consumer is `restart_idx`, `P/BuiltRestart.lean:93`. |
| **B8 (iv)** `i < σ.b` (`.snap.db`) | **unchanged** | `recoverSnapshot` runs before `ReadAll` (in the fork, check that the boot step goes after `bootstrapBackend`), so the step sees `ci = σ.b ≤ σ.commit` and does nothing. |

## 2. Draft changes already made: still needed or revertible

The motivation recorded for B3 (d6 T4 round 4, step 1) was this: after a power loss, the WAL's entries
`≤ |a0|` can hold a stale entry, so `replaySeed_facts` and the replay job need a leader-completeness law. Under
A, the term check at `ci` plus Log Matching on durable logs makes the WAL prefix through `ci` the committed one.
Under B no entries are left. And with no keep, `replaySeed_facts` reads only up to `|A₀| ≤ σ'.last`. So the
pre-B3 evidence (`rnReplayState`, `replayPending`, `rnReplayState.job`) holds at a crash restart as it does at a
graceful one.

| Draft change | Verdict | Trusted delta if reverted |
| --- | --- | --- |
| B3 part 1: `NotifyCD.lean` / `isNotifyD`, `rnApN`'s job moved into `notifyc` (`P/InvRaftNode.lean:2444`), `applyAll.specBatch`'s `isNotifyDR` | **revertible** | packet row 1 disappears |
| B1 `rnLeadLaw` / `rnLeadLaw_enter(E)`, `rnDurK_leadLaw`, `rnReplayJob_of_lead` (`P/ReplayJob.lean:123`, `:195`) | **revertible** (unused once B3 reverts) | none (Proof-only) |
| B2 / B3 part 2: `rnReplayHist`, `rnReplayHistP`, `replayBatchP`, `RNNames.s0` (`P/InvRaftNode.lean:136`), `rnLoopTokP`'s `S` parameter (`:2580`), `rnWorkerStartTok`'s seed (`:2745`), `newRaftNode`/`bootstrappedRaft.newRaftNode` specs' `s0` | **revertible** | packet rows 3 and 4 disappear. **Row 4 was the only *stronger* row of `NewServer_dist`**, so reverting removes the only change that needed Upamanyu's sign-off. |
| B5 step 1, B6 part 1 | **revertible** (§1) | rows 2 and 5 disappear |
| session 11: raft's `confAt_committed` law and `srvCrashImageAt_disk` over `srvRaftLogInv` | **keep** | proved law; no row |
| `raft-restart-confpoint` (option D, raft; `raftNode_of_RestartNode` at `a' = min |A₀| σ.commit`) | **keep**: `a' = |A₀|` now always; leave the `min` | untrusted spec generalization over raft's clients; reverting it gains nothing |

Net: revert `P`/`S` to the (A) base (`0fd28cd373`), keeping session 11's two changes. The T10s3b packet
(`notes/t10s3b-axiom-packet.md`) is then empty. `NewServer_dist` and `Serve_dist` mean what they meant at
`7ff538e61d`. Check this by rerunning `AxCheck6` after the revert: expect no hit for a changed definition.

## 3. Statements that change beyond the lead's list (most important first)

1. **`bootstrapCrashContract`** (`P/InvCrashImage.lean:172`; the law in `P/CrashInterim.lean:137`; B4's crash-aware
   **C-I2-K**). In its first case, `bootstrap` now writes the WAL. The post `bootOkR … σ i …` must be at
   `σ' = bootFix σ i t cs`, and `bootOkR`'s `"Hwal" ∷ wal.restartOk … σ` and `"Hrest" ∷ memStorRestarted … σ cs`
   (`P/InvRestart.lean:472`) follow it. The precondition needs the term row (item 3). And somebody must move
   `raftState S` to `S'` with `StorageHolds S' σ'` **at the WAL's durable point**. Options: the contract takes
   `raftState` and the raft boot law and returns `raftState S'`; or (shape (a) of B4's D-B4-5, `srvDurLoop … (σview S
   σ)` in the precondition) the boot step is a step of `rnDurInvK`. C-I2-K's mid-`bootstrap` crash slot must
   accept both read-backs, `σ` and `σ'`. Direction: **stronger** (a promise about new Go code and a ghost
   update), so it needs a fresh review (`notes/axiom-review/c-i2-snapdb.md` redone) and Upamanyu. **This pushes
   D-B4-5 toward (b)**: allocate `rnDurInvK` after `bootstrap`, so the contract carries a raw `raftState`. Under (a)
   it needs a new `rnDurK` boot-step law.
   The second case (`.snap.db`) is unchanged.
   **`bootstrapRestartContract`** (`P/InvRestart.lean:738`): the text is unchanged (the step does not fire when
   `i ≤ σ.commit`), but its justification must say so. The same holds for `bootstrap.wp_proof_dist`
   (`P/bootstrapDist.lean:84`) and `bootstrap.wp_proofOne`, which describe first starts only (no WAL, so the new
   code is unreachable). The function's Go text changes, so the code is re-translated.
2. **`bootstrapAtR` / `NewServer.specRAt`** (`P/NewServerRAt.lean:45`). The precondition `σ.b ≤ i ≤ σ.commit`
   becomes `σ.b ≤ i`, with the post at `σ'` (the same `S'`/`raftState` handoff as item 1). `bootstrapAtR_of_restart`
   (`:87`) needs the lemma `i ≤ σ.commit → bootFix σ i … = σ`. In `NewServer.wp_proofRG`, `wal.stopImage_elim` runs
   *before* the `bootstrap` call (`P/NewServerR.lean:281` vs `:294-296`), and its facts are used after it
   (`restart_idx` `:341`, `raftState` `:440`). Rebinding `S σ := S' σ'` after the call means moving those facts.
   This is mechanical but touches the 2949-line proof. `srvCrashImageAt_disk`'s failure case (`:135`) shrinks to
   `¬ (σ.b ≤ i ∧ bootLen ≤ i)`, and `wp_proofC`'s `sorry` keeps only (iii) and (iv).
3. **`srvCrashImageAt`** (`P/InvCrashImage.lean:106`): a new row, **the backend's stored term is the term of the
   committed entry at `i`** (`A`'s last entry's, `i > 0`). Today `imageRestAt` (`P/InvImage.lean:173`) has
   `∃ t, term key = encMeta t`, unconstrained. Do not tighten `imageRestAt` itself. It is reached by
   `srvDiskImageAt`, which is inside `Serve_dist`'s `srvDoneInv`, so the change would be incomparable there. State
   the row in the crash image, guarded `σ.commit < uint.nat i → …`, so that `srvDiskImageAt ⊢ srvCrashImageAt`
   (specC's "one restart spec") still holds vacuously.
   **`NewServer.specC`** (`S/NewServerCrash.lean:98`) changes only through `srvCrashImageAt`; its post names no
   `σ`. **B4's `specCK`/`NewServerC_dist`**: `srvCrashImagePure` gains the row (a stronger precondition makes the
   axiom weaker, which is pre-approved). But `"Hloop" ∷ srvDurLoop γ id νk h (σview S σ)` ties the loop's durable
   view to the image's `S σ`, and after boot that view is at `S' σ'`. So the tie must be restated (incomparable:
   needs review and Upamanyu), or it disappears under D-B4-5 (b). **F-B1** (`bootLen ≤ σ.commit →`) **stays**: it
   chooses Go's branch (unsaved WAL → `Discard`), which the boot step never reaches. It does not become provable
   from the step. F-B2 (`σ.b ≤ i`) stays.
4. **raft's API**: a **new law** that moves `raftState` at boot (§4, item 1); `etc/api/raft.txt` and the
   interface are regenerated, and so are the copies (`RaftTla`, `RaftNoAx`, `KvRaft`). **`RestartNode.spec`
   (`S/../raft/v3/RestartNode.lean:90-94`) is unchanged**: at `σ'`, `max σ'.b Applied ≤ a = |A₀| ≤ σ'.commit`
   and `bootLen ≤ σ'.commit` hold. Under B the commit is *not* above the last index (`σ'.commit = σ'.last = ci`).
   `restore` and the snapshot specs are unchanged.
5. **cindex** (Go: the atomic `(index, term)` pair, so re-translate). `ciInv` (`P/InvCindex.lean:134`) holds one
   pair field and a pair predicate `P k t`, where the server's instance is "`t` is the term of committed entry `k`"
   (`srvRLogLb` of a log of length `k` whose last term is `t`). The cindex specs (`SetConsistentIndex`,
   `SetConsistentApplyingIndex`, `ConsistentIndex`, `UnsafeSave` reading the pair once) and their proofs are
   restated. The callers supply `P` (`applyEntryNormal`'s tail, including the deferred set at Go's
   `server.go:2037`; `applyConfChange`; `applySnapshot` at the snapshot's `(index, term)`). `metaAfterSave`'s
   "`t = 0` keeps the old term" stays, but becomes unreachable for `k > 0` because entry terms are `≥ 1`.
6. **T10's backend crash invariant**: the image facts `bkImg` deposited at each commit (d6 T10 §1) and
   `batchLockInv`'s image row (`InvApply.lean`) gain "the stored term = `A`'s last term", from item 5's pair at the
   hook step. This is T10's own definition, not a dist axiom.
7. **WAL** (`P/WalApi.lean`): no byte-level WAL spec changes. Branch B's record is `walSaveSnap`'s
   received-snapshot arm (`Proof/…/storage/WalRecsCore.lean:35`, index above the commit, entries dropped), which the
   loop already uses, and the read model's "newest valid pair" (`WalHistLemmas.lean:492`, A3) already gives the
   intermediate crash point (record durable, HardState not: reads back `σ`). This matches ce3dbc097's start rule:
   no entries above `ci` precede the record. What changes is the sealed **`wal.restartOk`** (and B4's narrowed
   `wal.restartOkK`). It must be producible *after* writes on the read handle (records `σ'`, the handle's
   `enti`/encoder advanced), with `wal.restartOk_facts` at `σ'` (I3 holds: `σ'.b ≤ σ'.commit ≤ σ'.last`; I4: B's
   record is data-less at the base). When #34 proves the restart branch of `bootstrap`, it will use `Save` (no
   entries), `SaveSnapshot` and `Sync` on that handle, which are new spec *uses* but not new specs.
8. **Unchanged**: `NewServer_dist` (after the §2 revert, back to `7ff538e61d`; with no revert, the packet as it
   stands; the step never fires on a first start), `Serve_dist` (`wal.stopImage` keeps `i ≤ σ.commit`;
   `imageRestAt` is untouched by item 3), `PeerServe_dist`, `NewPeerHandler_dist`, `RestartNode.spec`, F-B1, and
   B8 (iii)/(iv).

## 4. New proof obligations the boot step brings

1. **The raft boot law** (inside the raft proof, the durable ghost `ownDurGhost`/`raftStateU` and `RInv`; the
   biggest item). A vacant node (`nodeVacantA`), with `isCluster`, `raftState γ id S` and a committed log `l`,
   `|l| ≥ ci`, whose entry `ci` has term `t`, may move `S` to:
   - **A**, if `S` holds `(ci, t)`: `S` with `hs.commit := ci`. This needs Log Matching on *durable* logs (`S`'s
     prefix through `ci` is `l`'s), which rests on the torn-`Save` fix.
   - **B**: base `(t, ci)` with configuration `CS`, no entries, `hs = ⟨max Term_w t, Term_w ≥ t ? Vote_w : 0, ci⟩`.
     This needs: dropping the node's durable entries keeps every inductive fact that counted its acks (a
     divergent entry at `ci` can never commit), and `Term_w < t` implies no durable vote at `t`.
   Both mirror raft's own steps (`commitTo` on a heartbeat; `restore` of a leader snapshot), but no message
   triggers them. The law gives `StorageHolds S' σ'`, and `DurAgrees S' l` for `wal.stopImage`'s committed-log row.
   `raftState_cmtBefore` and `nodeStartTerm` are then taken at `S'.term` (after the step: ordering only).
2. **The backend's term is the term of `ci`** (§3, items 3, 5 and 6): the cindex pair predicate plus T10's image
   row. Also, `i > 0 → t > 0`, so the Go precondition "`term_be > 0`" holds (pre-3.5 backends are out of scope).
3. **`CS` is the configuration at `ci`**: `confRowW` + `confAt_committed` + `srv_confAt_eq_simple` (static
   cluster, session 11's argument), plus `walSnapCert` for the new record, whose margin is a static cluster as
   `wal.stopImage`'s.
4. **T10's snapshot-record rule** (`rnDurInvK`'s records: every saved snapshot index `j` with
   `ciFloorLb γc j ∨ snapSaved γd j`): the boot's record at `ci` takes `ciFloorLb γc ci`, from the backend read at
   `ci`. This keeps the next crash out of the `.snap.db` case for this record.
5. **Crash atomicity of the ghost step**: `raftState` moves to `S'` exactly when the read-back moves to `σ'`. For
   A, that is the HardState's `Sync`. For B, it is the HardState's `Sync`, with the record alone reading back
   `σ`. This lives in C-I2-K's slot, or in an `rnDurK` step (§3, item 1).
6. **Branch selection**: the Go check "WAL entry at `ci` has term `t`" decides A against B. Under A, `ci ≤ σ.last`
   and the entry matches; under B, `ci > σ.last` or the terms differ. Both are pure facts about `σ` from
   `ReadAll`'s result (`StorageHolds S σ`).

## 5. D′ (raft's start snapshot built from the backend at every boot, no WAL record)

D′ needs the same raft law (§4, item 1) and the same term and conf facts, and avoids §4 items 4 and 5 and the
`wal.restartOk` change. The cost: the WAL alone no longer holds raft's durable state. `StorageHolds S σ`
becomes `StorageHolds S (bootView σ D)` in every place the WAL view appears (`rnWalView`, `rnDurInvK`,
`wal.stopImage`, `wal.crashImageR`, the crash contracts). The term raise would not be persisted until the loop's
first `Save`, so `raftState`'s term must be re-derivable at each boot. My estimate is that this is larger than
(D)'s two-record argument. It also changes `Serve_dist`'s `wal.stopImage`, unless the stop image keeps the WAL-only
form.

## 6. Bookkeeping

- `nonissues/` from `b251f33464` and `6593bce6c7` (the keep guard's stale configuration; the keep branch's cluster
  recovery), and `nonissues/etcd-crash-backend-ahead-snapshot-regress.md`: mark them superseded or fixed by the
  boot step when the fork lands.
- The torn `(consistent_index, term)` pair is upstream code: a `nonissues/` (or `issues/`) candidate
  (`review.md`, "Upstream-relevant observations").
- Ledger entries come first (`notes/specs-only/ledger.md`): the reverts of `specSnapM` (S2 and the strict `hle`),
  `applyAll.specBatch`, and the `newRaftNode` specs; and `bootstrapAtR`/`specRAt` at `σ'`.
