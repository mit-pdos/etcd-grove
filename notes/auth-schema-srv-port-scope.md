# auth-schema-srv: porting onto lean's backend (Scope, 2026-11-19)

Status: **Scope, STOP for an independent review** (etcd-grove-03's decisions (1)-(3), questions.md "BLOCKER:
merging lean e95ce79ce9"). Branch `auth-schema-srv` at 99a71018a7; lean at e95ce79ce9 (pin 3afd77e35); merge base
1e4cb38613 (the per-heap merge). Nothing merged: the measurements below come from a throwaway
`git merge-tree --write-tree HEAD lean` (tree `bce44cd63b`, conflict list `/shared/tmp/auth-schema-srv/mt.txt`).

## 1. The two designs side by side

They redesigned **different layers**. Lean (bbolt-integrate S1-S6, `notes/bbolt-integration-plan.md`) replaced
the backend's *bbolt-facing* vocabulary; this branch (A1, A6.2, K-c) added a *ghost layer* over the tracked
buckets (`rbOwn`/`γ.rbk`). Neither touches the other's layer: lean's diff since the merge base adds no line
mentioning `rbOwn`, `rbPart`, `rbk`, `rbSide`, `rbOwnIn`, `bStopView` or `rbData` (one moved line in
`ApplyAllSnap`), and this branch's claim-layer statements mention no bbolt predicate except at the 7 places in
§2.B.

| | lean (e95ce79ce9) | this branch (99a71018a7) |
|---|---|---|
| bbolt below | proved bbolt, one canonical spec per function; backend predicates are `onFs` wrappers: `txLive tx γd q T := onFs (boltTx tx γd q T)` (`T : bbolt.TxView`), `ownWTxG tx γd D S G := txLive tx γd 1 (wView D S G)`, `txBytes tx γd`, `wBkt tx γd b n g`, `ownCur tx γd c T es pos`; `rdB γd tx`, `kvsOutRd γd tx` | the merge base's `_kv` layer: axiomatized `txLive tx q`, `rtxSnap tx D`, `rtxStats tx`, `rBkt`, `txBytes tx`, `rdB tx` over the `bbolt.*_kv` axioms; plus A2's `Bucket.ForEach_kvr/kvw` axioms |
| glue | private `kvGlue_*` lemmas per proof file (canonical spec → backend shape at `theFs`) | none (calls the `_kv` specs) |
| ghost names | `BNames` unchanged except `db : DBNames := bbolt.BoltName` | `BNames` + `rbr`, `rbc` (A1, A6.2), namespace `rbClaimN` |
| readers' interval | `intvInv` without the `stats` invariant (`tmTok` one token), `wgInv γ rtx D …`, `rdShare γ rtx D …`; `txLive` is **not timeless** (`wgBody_later` strips the later with `isDB`) | `intvInv` with `inv stats (rtxStats ∨ γ.txb)`; `rtRes`/`clnPart` + `rbrHalves` (readers' halves of `γ.rbr`) |
| batch lock | `batchLocked γ P b st`; `rdB` accessor over `txBytes_acc` | `batchLocked γ P b st c` (mode `c`), `trkSide`/`rbrSide`/`rbrOne`, `tkI`, `st.cw`; writes take `k`; `Unlock` claimed (`Sc`, `rbAcc`, confirmation window `rbConf`) |
| claims | **nothing equivalent**: no claim, no `γ.rbr`/`γ.rbc`, no claim invariant or tokens | `rbClaimInv` in `inv rbClaimN`, `rbClaimToks` (one per tracked bucket, in `newPostK`), `rbOwnIn_claim`, `rbPartRF` (⅛ of `γ.rbk`, K-c), `rbRd`, `rbOwnInR` |
| `New`/`OpenBackend` | `New` takes the concrete `fileHolds`, gives `bPath γ.db path` too; `OpenBackend` sound in the strict sense (S5: its post is exactly `New`'s) | `New` (NewAlloc) allocates `γ.rbr`, `γ.rbc` and the tokens; `newPostK` holds the tokens |
| `Close` | gives `bStopView` and `bClosed γ.db D` (joins with `bPath` into `fileHolds`) | `bStopView` as before (its share is in forbidden law (iii)/(iv)) |
| ForEach | **no** `Bucket.ForEach` spec in bbolt (translated, unproved, unused); no backend ForEach | `backend.unsafeForEach` (over `FeSide`), `baseReadTx`/`readTx`/`batchTx`/`batchTxBuffered.UnsafeForEach` over A2's two axioms |

So the port is a **vocabulary port** of this branch's backend onto lean's bbolt-facing predicates, plus ForEach
re-done over a proved canonical spec. No design decision of the claim layer has to change.

## 2. Porting plan, by file

Mechanism: `git merge lean` on a staging branch `auth-schema-port` off 99a71018a7 (a merge, not a rebase: the
conflicts are small and the history stays), pin switch to manifest-3af (`.lake/package-overrides.json` = copy),
then compile-fix. Fast-forward `auth-schema-srv` to it only after the stage's checkpoint.

**A. Textual conflicts (16 Lean files, 39 in all).** Rule: lean's bbolt vocabulary + this branch's parameters.
| file | hunks | resolution |
|---|---|---|
| backend `InvBatch` (the `rdB` accessor) | 1 | `rdB γ.db st.tx` + mode `c` |
| backend `NewAlloc` (`rtRes` build) | 1 | lean's `txLive rtx γ.db ½ (ro D)`, `wgInv γ rtx D …`, minus `rtxSnap`/`Hrtx`, plus our `rbrHalves` |
| backend `batchTxBuffered__{UnsafePut,UnsafeSeqPut,UnsafeDeleteBucket,UnsafeRange}` proofs | 1 each | both binder lists (lean's `Hkv`; our `c k Hkc`); `rdB γ.db` |
| backend `batchTxBuffered__unsafeCommit` | 3 | lean's `kvGlue_Tx__Rollback_kv` + our `c Sc Rr E hE`, `Htk`, `commit_ghost`'s extra args |
| backend specs `batchTxBuffered__UnsafeDelete`, `__UnsafeRange` | 1 each | `txBytes st.tx γ.db`, `kvsOutRd γ.db`, `rdB γ.db` + `c`, `k` |
| backend `Link` | 4 | regenerate (`LAKE_OPTS=… etc/gen-link.py --backend`) |
| `CindexBackend` (2), `BackendHooks__OnPreCommitUnsafe` | 1-2 | lean's key-length argument + our `false false` |
| etcdserver `ApplyAllSnap` | 1 (362 lines) | lean moved the lemmas to `ApplyAllSnapLemmas.lean`: move our `kvAppliedM_rev` there; keep our `srvAuthApplyResB_lend` call |
| auth/auth3/authN `Results` | 1 each | lean's text with only `hD22` removed (decision 3: A7's change; re-run `stmtdiff.py`) |
Non-Lean: `etc/{axiom-tok-allow,link-lean-first-backend,tcb-baseline}.txt`, six collections, 11 interface files
(regenerate after the build, never hand-merge), `notes/STATUS.md`, `status-history.md` (append-only: union, `wc -l`
≥ lean's), `specs-only/ledger.md` (union).

**B. This branch's files that name a changed predicate (added lines only; measured on the merged tree).**
- `InvBackend`: `FeSide`/`feOwn` (l.1680-1683) **go**: the walk holds `txLive tx γd q T` with `⌜T.rw → q = 1⌝`
  (what `Tx.Bucket` takes; `ownWTxG` is that at `wView`). Form change of internal specs (no twin: in place).
- `unsafeForEach` spec + proof: over lean's `Tx.Bucket` and the new canonical `Bucket.ForEach` (§4), through
  private `kvGlue_*` lemmas as in lean's `baseReadTx__UnsafeRange.lean`; entries `bktOf T.cur bi.name`.
- `baseReadTx__UnsafeForEach` (283 lines): drop `rtxStats` and the `stats` invariant (as lean's
  `baseReadTx__UnsafeRange` did), `txLive rtx γ.db q (ro rv.1)`; `readTx`/`batchTx`/`batchTxBuffered.UnsafeForEach`
  specs: `txLive … γ.db`, `txBytes … γ.db` (3-4 lines each).
- `Model2.rtForEach`: pure, unchanged.
- realization: `AuthRealWr` (7 sites: `rdB bs.tx`, `txBytes bs.tx`, `kvsOutRd` unfolds), `AuthRealRead` (3: the lent
  `txLive x ¼` becomes `txLive x γ.db ¼ (ro rv.1)`), `InvAuthBackend` (1).
- the bbolt A2 files (`{Spec,Proof}/go_etcd_io/bbolt/Bucket__ForEach_kv{r,w}.lean`): **deleted** (§4).

**C. Files that merged cleanly but sit on lean's changed plumbing** (expect compile errors, not design ones):
`ReadLemmas`, `ReadSide`, `RdPool`, `InvCommit`, `CommitLemmas`, `WritebackLemmas`, `InvStop`, `NewLemmas`,
`batchTxBuffered__{Unlock,commit,Commit,CommitAndStop}`, `backend__run`, `UnlockBare`, `ClientLaws`; and the
claim layer `TrackedLemmas`/`ClaimedLemmas`/`TrkModel` (pure ghost: expected to compile as is). One known risk:
`txLive` is no longer timeless, so any of this branch's code that takes a reader's `txLive` out of an
invariant from under a later (pool invariants hold reader slots; `pool_release_later` assumes `Timeless (Rs a)`)
needs lean's `txLive_later` with `isDB`; a grep found none (the slots are ghost tokens), the build will tell.

**D. Not ported:** nothing of lean's is reverted; nothing of the claim layer is dropped.

## 3. Trusted texts on the A7 list after the port

Unchanged in meaning; re-stated over lean's vocabulary only where their bodies name it:
| item | after the port |
|---|---|
| K-c (`rbPartRF` ⅛, `rbClaimC` ⅝) | body unchanged (pure ghost); still under `isBackend`, so in `backend.backend.Snapshot.wp_proof` (axiom, still on lean) and `newPostK` |
| `rbPartF`'s fraction ½ → ¼ | unchanged; under `isBackend` |
| `newPostK`'s tokens | unchanged; `newPostK` now also lean's (S5). `OpenBackend` is lean's strict-sense axiom ("its post is exactly `New`'s"): **that argument now covers the tokens only because this branch's `New` allocates them** (NewAlloc); the merged `NewAlloc` must keep `rbr_alloc` and the token allocation |
| fix (A), L-rev, P2, P1', R-c, O-a, `authRdSlots`' tokens, ticket count | unchanged (auth/schema side; lean did not touch them) |
| A2's `Bucket.ForEach_kvr/kvw` axioms | **leave** (proved, §4); with them their two `axiom-tok-allow` entries |
`isBackend`'s body changes by lean's own edits (`isDB db γ.db`, `txDB … γ.db`, `dbFile … γ.db`), already on lean.
No new trusted text: the canonical `Bucket.ForEach.spec` is proved, the glue lemmas are private theorems.

## 4. ForEach: prove bbolt's `Bucket.ForEach` (decision 2)

- **Spec** `Spec/go_etcd_io/bbolt/Bucket__ForEach.lean`, converging on `SpecPlan/Spec/go_etcd_io/bbolt/
  Bucket__ForEach.lean` (visitor gets the transaction **at the walk's fraction `q`** and gives it back at the same
  view; `E i err`; `curAt`), restated in the proved API's vocabulary (`boltBkt tx γ b n (T.gen n)` and `T.cur.lookup n
  = some m` for SpecPlan's `bktUse`/`T.ents p`):
  `{{ boltTx tx γ q T ∗ boltBkt tx γ b n (T.gen n) ∗ ⌜T.cur.lookup n = some m⌝ ∗ I 0 ∗
      □ ∀ i k v, {{ ⌜i < (bktEnts m).length⌝ ∗ I i ∗ curAt tx γ (bktEnts m) i k v ∗ boltTx tx γ q T }} fn k v
                 {{ err, boltTx tx γ q T ∗ (⌜err = nil⌝ ∗ I (i+1) ∨ ⌜err ≠ nil⌝ ∗ E i err) }} }}
    b.ForEach(fn)
   {{ err, boltTx tx γ q T ∗ (⌜err = nil⌝ ∗ I (bktEnts m).length ∨ ∃ i, ⌜err ≠ nil ∧ i < len⌝ ∗ E i err) }}`
  (with `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` as every canonical spec). The visitor gets all of `q`, not the
  A2 axioms' half: "must not modify the bucket" is enforced by giving back the same `T` (a `Put` that changes the
  bucket changes `T`; `dropBkt` bumps the generation); soundness is the proved `Cursor.Next`'s, not an argument of
  ours. Fallback if the proof needs it: the half (a weaker spec, report it).
- **Proof** `Proof/go_etcd_io/bbolt/Bucket__ForEach.lean`, `wp_proof (hcur : Bucket.Cursor.spec) (hfst :
  Cursor.First.spec) (hnx : Cursor.Next.spec)`: the `b.tx.db == nil` check through `boltBkt`'s `tx` field and
  `rdTxK_db_acc`/`wtxWQ_db_acc` (`import all` of the Api, as `Bucket__Cursor.lean`), then the loop over the public
  specs with `I i ∗ boltCur … (some i)`; template `Bucket__ForEachBucket_rP.lean` (237 lines). Est. 200-300 lines.
- Wiring: bbolt's link list and `etc/gen-link.py --bbolt`; `etc/api/bbolt.txt` (spec importable); bbolt interface
  regenerated (one new spec file: an API change to review); backend `Link` passes `bbolt.Bucket.wp_ForEach`;
  delete the two `_kv` axioms and their specs, the `axiom-tok-allow` entries, tcb baseline −2, collections
  (backend, server, authkv, auth3, authN: −2 each). `examples/bbolt/foreachkv` (9 Go tests): keep as the spec's
  behavioral evidence (recommended) or delete.
- No twin: one spec for both transaction kinds (as `Bucket.Cursor`); the backend's `FeSide` goes with it.

## 5. The soundness re-check (forbidden laws (i)-(iv), soundness §6-§7, against lean's backend)

Laws (i)-(iv) are about the claim layer, which lean did not touch, so the re-check is of what lean **added** that
could produce or consume a tracked-bucket share:
1. **No new law** on `γ.rbk`/`rbOwn*`/`rbPart*`/`bStopView` in lean (grep of lean's diff: none). Re-run the grep on
   the merged tree, and over `Spec/**` for texts holding `isBackend`/`newPostK` (30 spec files on lean).
2. **(iii) re-opening under the same names**: lean adds `Close → bClosed γ.db D`, `bPath ∗ bClosed ⊢ fileHolds`,
   and re-opens through `New`, whose `γ` is fresh (`∀ γ` in the pre's update, `∃ γ` in the post): OK by statement.
   To check: `storage.OpenSnapshotBackend`, `EtcdServer.applySnapshot`, `bootstrapped*.Close`, mvcc's
   `EtcdBackend` close (`bStopView` at the store's `W`: MERGE-TODO on lean), that none hands a backend over a `γ`
   it took in.
3. **(iv) stale shares after `Close`**: `bStopView`'s quarter + a claimed part's ⅛ + the invariant's ⅝ make a whole
   element; lean's `boltState_read_au`/`commit_au` are over `boltState γ.db` (bbolt's names, not `γ.rbk`): no
   path from them to `γ.rbk`. Confirm on the merged tree.
4. **`OpenBackend` strict soundness (S5) with the tokens**: its post must still be exactly `New`'s proved post;
   check the merged `newPostK`/`NewAlloc` (both sides edited them).
5. **`backend.Snapshot` axiom**: lean's rewording (S4b) of its observation; K-c's argument (the observation sees
   coexisting shares; the lock's ¼ is client-reachable only there, after `Close`, or via `bStopView`) re-read
   against lean's text.
Deliverable: a §8 of `notes/auth-schema-srv-a1-soundness.md` ("after the port"), then a fresh read-only check
(subagent) as for K-c.

## 6. Stages and estimate

| stage | work | est. |
|---|---|---|
| P1 | staging branch, merge, §2.A resolutions, pin switch, `.lake/package-overrides.json` | 0.5 session |
| P2 | §4 spec + proof + bbolt wiring (independent of P1's compile-fix; can go first) | 1 session |
| P3 | §2.B/C compile-fix of the backend (incl. `unsafeForEach`, `baseReadTx__UnsafeForEach`), backend Link | 1-1.5 sessions |
| P4 | realization (`AuthReal*`, `InvAuthBackend`, schema/auth consumers) re-checked: lean-check each file, server Link | 0.5 session |
| P5 | full timed build (the pin change recompiles ~20.5k modules: ~3.5 h wall, slot-cap retries), tier-check, gen-init `--check`, interfaces, Links, tcb `--check --update` (−2 axioms), collections, gates config | 0.5 session + build time |
| P6 | §5 re-check note + independent check; A7 `stmtdiff` re-run; STATUS/handoff; land stop | 0.25 session |
Total: about 4-4.5 agent sessions, 2-3 days of wall time with the build queue. Checkpoints (reports): after P2
(the new spec, for review: an API addition of bbolt), after P5 (green build, trust-base delta), at P6 (land stop).

## 7. Decisions requested

1. The ForEach spec's form (§4): visitor at the walk's full fraction `q` (SpecPlan's; recommended) vs the A2 half.
2. `FeSide` replaced by `txLive tx γd q T` + `⌜T.rw → q = 1⌝` in `unsafeForEach` and its callers (in place; recommended).
3. `examples/bbolt/foreachkv`: keep (recommended) or delete.
4. Mechanism: merge on a staging branch, fast-forward `auth-schema-srv` at the checkpoint (recommended).
