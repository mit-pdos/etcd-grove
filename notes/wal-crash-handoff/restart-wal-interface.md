# The WAL at a restart: the interface between the crash-model WAL spec and the restart track

DRAFT for etcd-grove-81, 2026-11-12. Read-only survey of `lean` at `5961b2f46a`; nothing edited or built.

**The aim.** The collaborator specifies etcd's WAL in one crash model (AbsDisk + LinuxFs). We go on
with S5, S6 and S7 and leave S2 (the WAL at restart) and C6 (linking the new WAL spec to the server)
for later. This note fixes what a restarted server takes from the WAL, stated over the read contents
`σ : StorContents`. The new spec should produce exactly that. Our proofs should use only that.

Abbreviations: `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `St/` =
`Proof/go_etcd_io/etcd/server/v3/storage/`, `SW/` = `Spec/go_etcd_io/etcd/server/v3/storage/wal/`.
`StorContents` (`Proof/go_etcd_io/raft/v3/NodeApiVocab.lean:128`) is `hs, snap, base, ents`, with
`σ.b`, `σ.last`, `σ.commit` (`:135-139`).

---

## 1. What the restart proofs take from the WAL today

There is one entry point, `bootstrapRestartContract` (`E/InvRestart.lean:596`). It is a premise, and
its precondition holds `srvFiles cfg.DataDir' id σ D` (`:622`).
`srvFiles` (`:96`) is `∃ cid, walFiles (walDirOf dd "") id cid σ true ∗ backend.fileHolds …`.
`walFiles` (`St/WalRecs.lean:229`) is an axiomatized token, documented as "a graceful stop in one
process". The stop produces it inside `srvDiskImage` (`E/InvRestart.lean:152`), through
`stopCleanupImage.spec` (`E/StopShutdown.lean:360`). Downstream, the facts are these:

| # | Fact | Lean name / where | Source today | Graceful-only? |
|---|------|-------------------|--------------|----------------|
| F1 | Replayed hard state, entries and base are `σ` | `bootOkR`'s `"Hrest"`: `memStorRestarted bv.storage' γs σ cs` (`E/InvRestart.lean:438`; def `E/BaseRestartStor.lean:53`); the snapshot applied is `walSnapCS σ cs` (`:33`) | contract (trusted); `bootstrappedWAL.MemoryStorage.spec` (`Spec/…/etcdserver/bootstrappedWAL__MemoryStorage.lean:41`, proved) is the Go step it abbreviates | no (shape only) |
| F2 | Entries consecutive from the base; `σ.last < 2^61`; base 0 implies term 0 | premises of `bootstrappedWAL.MemoryStorage.spec` (`:44-46`) | today implicit in the contract; S3 planned `walRead_wf` | no |
| F3 | Snapshot record at the base: `σ.snap = some ⟨[], m'⟩ → m'.Term' = σ.base.term'` | `NodeStartSpecR`'s `%Hraft` (`E/NodeStart.lean:973`, the premise at `:988-989`) | not yet supplied | no |
| F4 | Base ≤ commit: `σ.b ≤ σ.commit` | `srvMem_restartStorage`'s `Hbc` (`E/NodeStart.lean:581`), derived at `:1088` | from `σ.b ≤ i ≤ σ.commit` | no (the WAL alone gives it) |
| F5 | The records hold the node's durable state: `StorageHolds S σ` (`NodeApiVocab.lean:150`: base within S's log, `σ.ents = S.entsFrom σ.base`, term and vote equal S's, `S.wcommit ≤ σ.commit ≤ S.commit`, the snapshot in `[σ.b, σ.commit]`) | `wal.stopImage` (`E/WalApi.lean:373`, elim `:385`) → `rnBootPre .restart` (`E/InvNodeStart.lean:335-339`), `NodeStartSpecR` | the stop, from `rnDurInv`/`ViewOk` (`E/InvWal.lean:388`) | **yes, as stated with the S of the stop.** After a crash, S must be adjusted first: R-C1 findings 2-4, `notes/restart-s3-handoff.md:100-140` |
| F6 | Commit bounds against the backend: `σ.b ≤ i ≤ σ.commit`, `bootLen ≤ i` | `bootstrapRestartContract` premise (`E/InvRestart.lean:600`); `rnRestartOk`'s `snap0 ≤ \|a0\| ≤ commit0` (`E/InvRaftNode.lean:495`); `NodeStartSpecR` `:988` | `wal.stopImage` | **`i ≤ σ.commit` is graceful-only** (stated so at `InvRaftNode.lean:492`; crash-design §2.3). `σ.b ≤ i` fails too after a crash between the WAL `SaveSnap` and the backend; `bootstrap` then opens `.snap.db`, a case outside the contract |
| F7 | Snapshot certificate: `walSnapCert cl σ` (`E/InvWal.lean:398`): base 0, or a valid data-less snapshot at the base | `wal.stopImage`; `NodeStartSpecR` `"#Hcert"` (`:1009`); used by `walSnapCS_valid` (`E/NodeStart.lean:532`) and `restart_lastTerm` (`:357`) | `rnDur_saveSnap_au`/`rnDur_ownSnap_au` carry it to the stop | no in substance: it is a property of every snapshot record ever saved |
| F8 | Replayed entries size-bounded: `γs.sz = true` | `bootOkR` `"%Hγsz"` (`E/InvRestart.lean:447`) → `srvMem_restartStorage`'s `hsz` | `walFiles … true` + premise `storage.walSaveOk` (`E/InvRestart.lean:608`; `St/InvOpen.lean:79`) | **yes as argued** (`notes/restart-vs-crash.md:360-368`) |
| F9 | Conf state: the backend's `cs` replaces the WAL snapshot's (`v3ConfStateIs`, `E/InvRestart.lean:108`) | `"Hrest"` | the backend, not the WAL | n/a: nothing is needed from the WAL's conf state |
| F10 | Metadata: the member id and the cluster id | `bootOkR`: `cv.ID' = id`, `"%Hid"`, `"#Hcid" … cid` (`:451`); `srvFiles`' `∃ cid`; `walMetaIs` (`St/WalRecs.lean:251`) | `walFiles`' `id cid` | no |
| F11 | The WAL handle after the read: `walReady`, `walOpen w 1` | `bootOkR` `"%HwalR"`, `"Hwalo"` (`:403,406`) | contract | no |
| F12 | Durability invariant at the restart view `⟨S, σ.hs, none, srvLE (A₀.take σ.b)⟩` | `NodeStartSpecR` `"#Hdur"`, `"Hwview"`, `"Hwok"`; made by `rnDur_alloc_view` (`E/InvWal.lean:488`), which takes `walRecs w σ true ∗ walSnapCert cl σ` | **no source today**: `bootOkR` gives no `walRecs`/`walOpened`/`walPurgeRight` (S2a's `wal.restartOk`, Scope S2) | the allocation is not; the records it holds are |
| F13 | S7's window facts | `rnRestartOk`: `srvRLogLb γ.srv γ.a0`, `snap0 ≤ \|a0\| ≤ commit0`, `rnSnapTermAbove` (row 4, `InvRaftNode.lean:464`, not a WAL fact); the boot sum `RNBoot.restart σ cs S a m A₀` (`InvNodeStart.lean:127`) | F5/F6/F7 | `\|a0\| ≤ commit0` only |

## 2. The proposed interface (does not depend on the crash model)

A restart's read returns `σ` (and a handle). Every fact below is either pure in `σ`, or relates `σ`
to a history `I` that the server's own invariant describes. The second column gives the W4b lemma
that already provides the fact, for `walReadCut I k = some σ` or `walReadR I p σ`
(`St/WalHist.lean:98-130`; lemmas in `St/WalHistLemmas.lean`). The third gives what the graceful
model provides now.

| # | Interface fact | New spec (W4b) | Graceful model |
|---|----------------|----------------|----------------|
| I1 | **Well-formed raft storage**: `walEntsWf σ` | `walReadCut_wf` (`:639`) | implicit in `walFiles` |
| I2 | **Last index bounded**: `σ.last ≤ 2^61 - 1` | `walReadCut_last_le` (`:816`) at `B = 2^61-1`, which needs `walIdxLe B I` (`:779`) | implicit |
| I3 | **Base ≤ commit**: `σ.b ≤ σ.commit`; and `σ.commit ≤ σ.last` (raft's `loadState` check) | `walReadCut_b_le_commit` (`:1156`); `commit ≤ last` from `walCommitLe I` (`:1438`, all prefixes of the fold) | from `σ.b ≤ i ≤ σ.commit` |
| I4 | **Snapshot at the base**: either base `(0,0)` with no snapshot, or a data-less record `⟨[], m⟩` with `(m.Index', m.Term') = (σ.b, σ.base.term')`. Gives F3. (Corrected 2026-11-13, restart CP2 review, minor (b): it does **not** give F2's third clause, base index 0 implies base term 0: the WAL model's `walSaveSnap` at index 0 sets the record's term, any term, `storage/WalRecs.lean:59-64`; only the server's history excludes it, no `SaveSnap` at index 0, `snapshot`'s `0 < ai` and raft's snapshots past its commit; C6 gets it from the history invariant, not from I4) | `walReadCut_snap` (`:530`) + `walReadCut_base` (`:494`); `walReadCut_snapAtBase` (`:1186`) | implicit |
| I5 | **Hard state is the last saved one**: `σ.hs = walLastHS I` | `walReadCut_hs` (`:254`) | `σ.hs` of `walRecs` |
| I6 | **Entries come from the server's own `Save`s** | `walReadCut_ents_sub` (`:743`) | provenance in `walFiles`' docstring |
| I7 | **A compaction of the unpurged read**: `StorCompacts (walRead I) σ`. In the exact form `σ = walRead I` under `Open`'s name bound | `walReadR_compacts` (`:1825`), `walReadR_eq(_openPos)` (`:1816,1834`); `StorCompacts` (`:1200`), `_wf` (`:1233`) | `σ` itself (no purge before the close) |
| I8 | **`I` is what the old incarnation persisted**: `I` is an image of the old history `H` at its synced mark `n` (`walImg`, `GooseLang/Ext/AbsDisk/Impl.lean:141`: a prefix `H.take j` with `j ≥ n`, possibly followed by a torn `Save` that keeps its first `k` entries and has a zero hard state). The kept fields are `walCrashKeeps d d' n` (`St/WalViews.lean:32`), which composes across crashes (`walCrashKeeps_trans`, `:44`) and includes the graceful case (`walDiskAt_crash_graceful`, `:85`) | WalViews B2 | `I = H` (every write is visible) |
| I9 | **Size-bounded entries**: every entry of `σ` sits at a content with `entSizeOk` | `d'.sized = d.sized` is in `walCrashKeeps`; **gap: `ReadAll` returns `walSaveEnts false`** (`SW/WAL__ReadAll.lean:76`). It must return `walSaveEnts d.sized` | `walFiles … true` + `walSaveOk` |
| I10 | **Metadata is the member's**: `mdp ↦*□ d.metadata`, which encodes `{NodeID: id, ClusterID: cid}` | `ReadAll`'s post; `walCrashKeeps` keeps `metadata`. The decoding to `(id, cid)` is still a C6 item | `walFiles … id cid`, `walMetaIs` |
| I11 | **Handle after the read**: open for append, synced, purge right | `ReadAll`: `walOpenW`, `walSyncedLb dir \|H\|`, `walNamed`, `walPurgeW` | `walOpen`, `walReady`, `walPurgeRight` |

**How the server's side connects to it (C6, not the WAL spec).** I1-I11 are facts about `σ` and
`I`. The facts F5, F7, F12 and F13 come from the server's own invariant over histories. C6 must
state that invariant over `H` and prove it closed under `walImg`. For every history the server's WAL
can be at:
- (a) `walCommitLe`, and `walIdxLe (2^61-1)` from raft's room fact;
- (b) every snapshot record is certified (`walSnapCert`'s right arm), so that F7 holds of any read;
- (c) each read holds a durable state, either `S`, or `pb.next S`, or `rsPartial S es k` (R-C1
  findings 1-3). `walImg`'s torn `Save` (zero hard state, `es.take k`) is exactly finding 3. Finding 4
  (a torn batch at a new term) is the open protocol item in `restart-s3-handoff.md`.

Because (c) is stated over histories, `walRecs w σ` cannot stay a σ-level record after C6. The read's
`walKeep` filter (`St/WalHist.lean:98`) uses the whole history's final commit, so "a later restart
reads `σ` followed by the new operations" does not hold in general. This is why the restart proofs
must reach the records only through a sealed slot (§4).

**The slot we propose, `wal.restartOk cfg id cid w σ`** (S2a's name, sealed as `wal.bootOk` is at
`E/WalApi.lean:326`). Its body is S2/C6's. Its elimination laws are the only thing our proofs use:
- `wal.restartOk_facts`: the pure facts I1-I5, F3, and `γs.sz`-able entries (I9);
- `wal.restartOk_start`: the analogue of `wal.bootOk_start` (`E/WalApi.lean:337`). It allocates
  `rnDurInv cl ν w` at the view `⟨S, σ.hs, none, l₀⟩` for an `S` with `StorageHolds S σ` supplied
  by the image, and gives `walSnapCert cl σ`, `walOpen w 1`, `walReady w`, `walMetaIs w id cid`,
  `walPurgeRight (walDirOf w)`, and `walDirOf w = config.walDirOf cfg.DataDir' ""`.

The graceful model can satisfy both laws from `walFiles` (S2). The crash model can satisfy them from
`ReadAll`'s post plus (a)-(c).

## 3. The C6 gates already recorded (the collaborator's spec must meet or restate them)

1. **One WAL per process.** The lock token covers the whole area, so a generation has at most one
   handle (`notes/decisions.md:34884-34889`). A tester with several members in one process needs a
   token per directory.
2. **No WAL at start, against an existing data directory.** `absDiskInitOk` requires `s.wal = ∅`
   (`:35198-35206`). A restart across processes starts with a WAL present. That needs "written by
   etcd at the pin, from its `Create`, under the `Save`/`SaveSnapshot` premises". This is a soundness
   item: a WAL named by an older etcd breaks `walOpenPos` and the read. Related: the restart's start
   names its directories by premise and hands over the durable reservation (`:34780-34783`). The
   first start's counterpart is `dataDirsAbsent` (`Proof/runtime/Start.lean:29`).
3. **`walCreateOk`** (`St/InvOpen.lean:115`, inside `diskOk`, `:123`). This is the first start's
   environment premise. Under crashes, a `Create` cut short (the temporary directory and the rename)
   must be specified.
4. **`unsafeNoFsync` off.** Every `walSyncedLb` post assumes it (`:35078-35082`). The server's
   configuration must exclude it, by a premise or an assumed configuration.
5. **The index premises of `Save`/`SaveSnapshot`** (`< 2^64-1`, `:35207-35212`). `Ready`'s entries
   come from raft's room fact, and etcd's own snapshot is at the applied index. **A received
   snapshot's index has no bound yet: this is open.**
6. **`walCommitLe`** is the premise of C2-C4. C2 is false without it (counterexample at
   `:35248-35256`). It must be discharged from raft's `Ready` invariants: item (a) above.
7. **Logically atomic recovery specs.** `Open`, `ReadAll`, `ReleaseLockTo`, `Repair` and `Exist` are
   now atomic (`:35142-35146`; for `Close`/VSE see `:35059-35070`). The error arms are argued, not
   proved (W4a.2 revision 1).
8. **The server's purge.** `fileutil.purgeFile` runs alongside `Save`/`ReleaseLockTo` and needs a
   spec of its own, which cannot reuse `purgeRound` (`:35313-35318`). The server's opaque
   `walPurgeRight` and the extension's per-handle `walPurgeW` are still two notions (`:34814-34815`).
9. **The area and the reservation.** C6 must restrict WAL names or exempt `member/snap`
   (`:34819-34823`). The area must lie at or below the data directory, and a dedicated WAL directory
   would extend the "Paths" assumption (`:34874-34878`). Our contract already fixes
   `DedicatedWALDir = ""` (`E/InvRestart.lean:600`).
10. **Sizes across crashes (I9).** `ReadAll` must return `walSaveEnts d.sized` (gap above). A failed
    `Save` is `¬ storage.walSaveOk` in the new spec too (`SW/WAL__Save.lean:69`), so the
    `walSaveOk` premise stays. But the argument no longer relies on a graceful stop: `sized` is kept
    by `walCrashKeeps`.
11. **Option A**, the linking design (`notes/wal-w4-handoff.md:31-40`): `absDiskExt` joins
    `trivialExts`; `walRecs`/`walFiles` become definitions over `walDisk` (two axioms fewer); the
    slot `wal.bootRes` takes `walAbsent`.
12. **Restarts are machine crashes** (`notes/restart-vs-crash.md:328-358`). The fork's `ReadAll`
    syncs the read and the directory (F-Z, F-N4; `SW/WAL__ReadAll.lean` docstring), which closes the
    WAL's Q1 path. Q5 (purge on a non-durable snapshot record) and bbolt's page reuse remain world
    assumptions, unless they are fixed upstream.
13. **W4c's strength items** (`:34893-34902`). `Open`'s raise persists. Clause 3 of `walRelGuard`
    against etcd-shaped histories (the apply loop's snapshot saved after a newer received one) is
    unchecked.

## 4. What S5, S6 and S7 will and will not assume

**S5 (constructors: `NewAuthStore` over `authBoot`, `lateWBR` deleted).** It touches no WAL fact,
so C6 does not affect it.

**S6 (`NewServer` over both boots).** It **will** consume `bootOkR` (`E/InvRestart.lean:384`) and
`NodeStartSpecR` (`E/NodeStart.lean:973`). It takes the WAL only through:
- the pure facts I1-I5 / F3-F4;
- `"%Hγsz"`;
- the slot's elimination `wal.restartOk_start` for F11/F12. S6 should state `bootOkR`'s WAL part as
  that slot now, with an opaque body if S2 has not landed, as `wal.bootOk` was at first. It must not
  add `walRecs` to `bootOkR`.

It **will not**:
- unfold `walFiles`, `walRecs` or `srvFiles`;
- relate the restarted records to the stopped ones beyond `StorageHolds S σ`, with `S` a binder of
  the image (so that a crash-time enter can supply a different `S`);
- use `i ≤ σ.commit` anywhere except `rnRestartOk`'s one conjunct marked graceful-only. Where only
  `σ.b ≤ σ.commit` is needed, take it from I3 and not from `σ.b ≤ i ≤ σ.commit`, as `:1088` does
  today. That proof line should be rewritten when S6 touches it;
- use `walSaveOk` other than through `diskOk`.

The metadata (F10) stays as `bootOkR` states it. C6 owes the decoding in I10.

**S7 (R2s-A).** It **will** use:
- the boot sum's `σ.b ≤ a ≤ σ.commit`;
- `walSnapCert` (F7), stated so that it is a per-record property;
- `srvRLogLb γ.srv γ.a0`;
- `restart_lastTerm`'s base-term fact, which I4 gives.

It **will not**:
- depend on the order of a graceful stop (the snapshot before the backend commit, the backend
  before the WAL commit) beyond `snap0 ≤ |a0| ≤ commit0`. That conjunct already sits apart in
  `rnRestartOk`, and S7's deletions of `srvWinPend`/row 4 should not spread it;
- assume the WAL snapshot's conf state (`bootstrap` replaces it, F9).

A restart after a crash where the backend is behind the WAL snapshot (bootstrap opens `.snap.db`) or
ahead of the synced commit is **backend-side** (rung 3 of the crash ladder, scope §"ladder"). It is
not part of this interface.

**What remains for later (S2 + C6).**
- S2: give the slot's body from `walFiles` and keep `sized = true` from start to end (Scope S2b).
- C6: rebase the body on `ReadAll` + `walCrashKeeps` + invariant (a)-(c); close gates 1-13; fix the
  `ReadAll` sized gap (I9).

Once both are done, S6/S7 should need no change beyond the slot's body.

## 5. Who owns `wal.restartOk` (2026-11-12, restart S6; lands with S6)

S6 introduces `wal.restartOk` in `Proof/go_etcd_io/etcd/server/v3/etcdserver/WalApi.lean`, beside
`wal.bootOk`. It has a defined sealed body over the graceful model
(`walOpened w dir id cid σ true ∗ walPurgeRight dir ∗ ⌜walReadFacts σ⌝`, with I1-I4 as
`walReadFacts`) and two proved laws, `wal.restartOk_facts` and `wal.restartOk_start`, and it
replaces `bootOkR`'s two WAL rows (`HwalR`, `Hwalo`). No axiom or opaque is added. After S6, C6
owns the body: it rebases the body on `ReadAll` + `walCrashKeeps` + the server's invariant (a)-(c)
and re-proves the two laws. The restart proofs use only the laws, so they should need no change.
