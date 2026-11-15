# W4c U5 (tester), sixth session (branch `wal-c-tester`, 2026-11-14)

Base `origin/wal-int` (`8fdd224baa`), merged again with `origin/wal-int` after `wal-c-durable` and
`wal-c-boot` landed (`3f5ffd02a8`). No axiom, no `sorry`, nothing trusted changed, no Go changed, no
statement of an existing lemma or spec changed. `TP/` = `LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`,
`TS/` = `LinuxFs/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`.

## Proved (`lake build` of each module passes)

- **`addCand`** (`TS/addCand.lean`): `candsOwn s cs ∗ opsRep si img` gives `candsOwn s' (tAddCand img unl pur cs)`.
- **`checkRestart`** (`TS/checkRestart.lean`): the restart's check. Premises: `tCheckWf o` (every candidate's
  history well formed and shorter than `2^62`, `synced ≤ |since|`) and **`tCheckNext o c ≠ []`** (the no-panic
  condition). `tCheckNext_ne_nil` derives it from "some candidate's image at its mark reads `c` from a
  purged prefix `kk ≤ min pur |img|`" (`tReadCut img kk = some c`). It returns `oracleRep v (tCheckRestart o c)`
  and gives back `oracleRep vo o`. The proof nests four loops: `since`'s append, the opens' raise, the
  images, and the purged prefixes. It needs `maxHeartbeats 4000000`.
- **`newRnd`, `rnd.next`, `rnd.choose`**: the choice source is `∃ v : rnd, r ↦ v`. `choose(n)` returns a value
  below `n`, or 0 when `n = 0`. `next` uses Perennial's linked `wp_RandomUint64`, as `mvccfull.choose` does.
- **`member.hs`**, **`member.size`** (`16 ≤ size < 140000`: what `tEntWf` asks), **`member.resume`** (the
  raft-like fields from the read `c`: `TP/Resume.lean`, `tResumeTerm/Last/Terms/Commit`; a fresh `terms` map
  `↦$ tResumeTerms c`).
- **`member.opTerm`**, **`member.opCommit`** (`TS/member__opTerm.lean`, `member__opCommit.lean`): over
  `member.save.spec`, `member.hs.spec` and `rnd.choose.spec`. Their pre and post use `TP/MemberRep.lean`:
  - `memSaveRes` is `member.save.spec`'s precondition minus `isPkgInit` and the arguments;
  - `memSavePost` is its postcondition at a hard state and entries;
  - `tNextTerm` is the term raised by one below `maxIndex`.

  `opCommit`'s post says either nothing happened (`l ≤ cm`, `memSaveRes` back) or the commit moved to
  some `cm' ∈ (cm, l]` followed by `save`. Both take the stored oracles' size premise for **every** hard state
  (`∀ h, tOrSmall (tSaveO1 o h []) ∧ …`), since the vote or commit is chosen inside. Reason: the encoding's
  length does not depend on the hard state's values. That lemma is not proved yet; the caller needs it.

## New non-spec modules

- `TP/Check.lean` (pure, transliterates the check):
  - definitions: `tAddCand`, `tRaiseUnl`, `tImgReads`, `tCandNext`, `tCheckNext`, `tCheckRestart`, `tCheckWf`;
  - lemmas: `tAddCand_set/_none`, `tImgReads_true/_false`, `tCheckNext_ne_nil`, `tHistWf_of_mem_tImgs`.
- `TP/CandsLemmas.lean`: `candsElems_length/_lookup/_snoc/_set` and `ownSlice_elem_read_cand`.
- `TP/Resume.lean`, `TP/MemberRep.lean`.

## Not done, and the next steps (in order)

1. **`restartRead` / `member.restart`**. Its callees' specs exist: `ValidSnapshotEntries`, `Open`,
   `ReadAll`, `Close.specFailed` (a hypothesis), `Repair`, `storeOracle`.
   - The spec must carry the opens raise. Before each `Open` the oracle with `opens ++ [idx]` is stored, and
     `tRelI` is re-established by monotonicity of `tOpensBound`. `Open`'s AU raises `d.unl` to
     `walOpenPos … idx`, which must be at most `tOpenBound` of the images (`tNameBound_le_openBound`, `tNameBound_eq`).
   - On success, the read must be related to `walReadAllOk` and then to `tReadCut` of the crash image, so that
     `restart` can discharge `checkRestart`'s `tCheckNext o c ≠ []`. This needs a lemma from `walReadAllOk`
     to `walReadCut` (WalHist) and `tReadCut_abs`.
   - `fromRaft` is still unspecified. It is needed to read the entries back: `fromRaft (absEnt e) = e` under
     `tEntWf e`, over `walEntsIn walRaftP`.
2. **`tester_crash`**, per the coordinator's note. First a `tBootCrash` like `tBoot0`: in the new generation,
   after `wp_osShare`, from `walInv_crash`'s and `durInv_crash`'s outputs, `walBootCrash`, then durable's
   `durBoot` on the oracle directory's claim (`mem_bootRest_root`). To rebuild `tRelI` in the new generation,
   the client must learn `walSyncedLb`/`walNamed` of the crashed WAL from `walBootCrash`/`walStart`, and the
   candidate's accounting from `tCandOk_crash` (`CrashPure`). **`BootFo`** of the crashed tree is still an open
   premise, which the crash invariant must carry for now (boot.md).
3. `opEntries`, `opResend`, `opRecvSnap`, `step` need a member invariant over the raft-like fields
   (`base ≤ commit ≤ last < 2^62 + …`, `terms`, entries `tEntWf`) and the `tOrSmall` size lemma above.
   `saveSnap`/`opOwnSnap` wait on U1 mismatch 3 (the `ConfState` encoding) and U6 (`purgeRound`, a user decision).
4. `Boot`, `Main`, then U7 (closed theorems: a user decision).

## Decisions for the user

None reached this session. U1 mismatch 3 and U6 still stand.

# Seventh session (same branch, after the merge of `87ead66a41` into `wal-int`): item 1, `restartRead`

Scope as the coordinator set it: `restartRead`/`restart` only; `tester_crash` and the ops are other units.
No axiom, no `sorry`, nothing trusted changed, no Go changed, no existing statement changed.

## Proved (`lake build` passes)

- **`fromRaft`** (`TS/fromRaft.lean`): of a raftpb instance's entry `walRaftP.entIn re m`, the entry
  `tFromRaft m` (`TP/FromRaft.lean`), with no panic.
  - `tFromRaft_absEnt`: a tester entry with `8 ≤ size` reads back as itself.
  - The salt round trip is closed by `bv_decide`.
  - New getter lemma `wp_entRoC_GetData` in `S/RaftModel/Getters.lean`, beside `wp_entRoC_GetIndex/GetTerm`
    (a lemma added to a shared WAL module; no statement changed).
- **`TP/RestartPure.lean`**, the pure core of the restart:
  - **`walReadAllOk_read0`** (WAL vocabulary): `ReadAll`'s success post `walReadAllOk I cut s σ'` gives the
    unpurged read. That is `walRead I = some σ`, with `σ'`'s hard state and entries and the base `s`, for a
    history with no maximal index that **reads back** (`walReadsBack I`, W4b's C2-C4 premise). It holds
    whatever position `k ∈ [cut, walOpenPos]` `ReadAll` read from, so the tester's check uses the purged
    prefix 0 and needs no bound on `k`. The proof goes through `walReadAt_cut`, `walReadCut_base` and
    `walReadCut_eq`; the snapshot record's existence (`ha`) comes from `walNewestPair_mem`.
  - **`tCandOk_open`**, the opens bound:
    - `tAddOpen o a` is the oracle with `a` appended to `opens`, which `restartRead` stores before each `Open`.
    - With it, the WAL state with `unl` raised to `walOpenPos … a` (`Open`'s update) is still accounted for
      by the same candidate. The chain is `walOpenPos ≤ walNameBound = tNameBound img a ≤ tOpenBound imgs a ≤
      tOpensBound`, using `tImgs_complete`, `tNameBound_eq` and `tNameBound_le_openBound`.
  - **`tCheckNext_of_read`**: the restart's read passes `checkRestart`'s premise. It needs:
    - `cd ∈ o.cands` and `tCandOk o cd d`;
    - `walReadAllOk (d.H…) d.cut s σ'` and `walReadsBack (d.H…)`;
    - the tester's read built as `restartRead` builds it: `absHs c.hs = σ'.hs`, base `s`, `c.ents = σ'.ents.map tFromRaft`.

    It then gives `tCheckNext o c ≠ []`, through the image `d.H` read from prefix 0.
    `tRead_ents_wf` shows a well-formed history's read holds only well-formed entries, so `fromRaft ∘ absEnt`
    is the identity on them.

## New obligation, for whoever owns the oracle invariant (not stated anywhere yet)

`tCheckNext_of_read` needs **`walReadsBack` of the crashed WAL state's history**, which is an image of a
candidate's history. Two ways to supply it:
- (a) carry it in `tCandOk` (or beside it, as `∀ img ∈ tImgs (tCandHist o c) (tCandMark o c), walReadsBack
  (img.map absOp)`);
- (b) prove it from the tester's raft discipline: entries only above the commit, the commit at most the last
  index, a snapshot at or below the commit.

It is true of the tester's histories but proved nowhere. `walReadsBack_snap`/`_save` give preservation under
appends; images (prefixes, torn saves) still need a lemma. **Not taken as an unstated hypothesis**: it is an
explicit premise of `tCheckNext_of_read`.

## Not done: `restartRead`'s and `restart`'s specs and proofs

The plan, everything below over existing specs:
- **`restartRead` (m non-nil)**:
  - **Resources:** `memSaveRes`-like (invariants, `osCallPerm 1`, `walAreaOk`, `osPathS`, `walAreaRes`,
    `walUnlockedTok`, the fields `lg`/`walDir`/`orPath`/`o`, `oracleRep`, `tOrOwn`, `tWalOwn γ od`).
  - **`ValidSnapshotEntries`:** its AU is committed in `TInv` unchanged, as `tInv_walAu` in `member__close.lean` does.
  - **The newest-pair loop:** gives `(idx, term) = walNewestPair snaps`.
  - **The per-attempt store:** `m.o.opens = append(…, idx)` and `storeOracle` of `tAddOpen o idx`.
    - `tRelI` holds by `tOpensBound_addOpen`.
    - `storeOracle` needs `tOrSmall (tAddOpen o idx)`: a size hypothesis, which wal-c-ops' size lemma does not cover.
  - **`Open`:** its AU commits `unl ↦ max unl (walOpenPos …)` by `tCandOk_open`.
  - **`ReadAll`:** its AU is committed unchanged. Its post gives `walReadAllOk` and `walHsIn hp σ.hs`
    (`walHsIn_hsGet`, `wp_hsGet*`), plus the entries `walEntsIn`, read by `fromRaft`.
  - **Failure arm:** `Close.specFailed`, then `Repair` (AU unchanged) and the retry. The loop invariant carries
    `repaired` and the token/permission flow (`osCallPerm ½` back from `Close.specFailed`).
  - **Post on `readOK`:** `contentsRep` of `c` with the facts `tCheckNext_of_read` needs, the open handle
    (`walOpenWF`, `walNamed`, `walSyncedLb`, `walLenLb`, `walPurgeW`), and `m.o` holding `tAddOpen^n o`.
- **`restart`:** `checkRestart` (premise from `tCheckNext_of_read`, `tCheckWf` from `tCandOk`'s
  `tHistWf`/lengths), `storeOracle` of the new oracle (`tRelI` of `tCheckRestart o c`: every new candidate is an
  image read back, with `tCandOk` at mark `|img|`), and `member.resume`.

## Head

See the final report.

# Eighth session (branch `wal-c-tester`, 2026-11-14): `restartRead` / `member.restart`

Base `origin/wal-int` (`89ef103d5b`), merged again with `origin/wal-int` after `wal-c-ops` landed (`fc80692a71`).
No axiom, no `sorry`, nothing trusted changed, no Go changed. Statement changes: `tOpWf`, `member.save.spec`,
`opTerm`/`opCommit`/`opResend`'s premises (below; ledger 2026-11-14).

## Blocker (decision for the user): `restartRead`'s newest-pair loop dereferences `*snaps[i].Index`

`restartRead` reads `*snaps[i].Index` and `*snaps[i].Term` (wal.go:168-171): loads through the snapshots'
`*uint64` fields. `ValidSnapshotEntries.spec` gives each snapshot only as `walSnapIdTerm p s` (`snapRoC p c`
with `(c.model.Index', c.model.Term') = s`), where `c.index : Option w64` and the model reads a nil field as 0
(`index.getD 0`); `recCell pi none` is `pi = null`. So nothing excludes a nil `Index`, and the load would
panic (the model gets stuck): **the loop is not provable from the WAL's spec**. In the tester's runs the
fields are always set (every snapshot record is `Create`'s or `saveSnap`'s, both with `Index`/`Term` set, and
proto2 presence keeps a set 0), so this is not a reachable Go bug, but the WAL's model does not track presence
(the history holds `SnapshotMetadataM`). The WAL itself reads them with `GetIndex()` (`validSnapshotEntries`,
`openAtIndex`, ...: 22 uses in its translation). Options:
- **(recommended) change the tester** to `snaps[i].GetIndex()` / `snaps[i].GetTerm()` (same behaviour: the
  getters return 0 on nil, which is what the model reads; specs exist, `walpb/Snapshot__GetIndex.lean`,
  `Snapshot__GetTerm.lean`). A Go change (and a re-translation of project walfs's part), hence the user's.
- strengthen `walSnapIdTerm`/`ValidSnapshotEntries`'s post with the fields' presence: needs the WAL's decode
  side to know that every snapshot record's bytes are `Mr.encSnap md` of an object with the fields set (a
  WAL-layer change across `U.SnapCoh`, the marshaller's canonical form and every `walSnapIdTerm` producer).

Until then `restartRead.wp_proof` is not written; its spec is stated and `member.restart` is proved over it.

## Open point 1 (`walReadsBack` of the crashed WAL): option (a) as stated is false; a weaker premise

`walReadsBack` of **every** image of a tester history is false: after `opRecvSnap`, `SaveSnapshot(s)` with
`s > last` (synced), then `Save({commit s}, [s+1..])`; the torn image keeping the snapshot record and some of
the `Save`'s entries but not its hard state has commit the old one `< s`, so `walRead`'s filter drops the
record and the entries `s+1..` leave a gap after the old last index: `readEnt` fails, `walRead = none`. So
"carry `∀ img ∈ tImgs …, walReadsBack (img.map absOp)` in `tCandOk`" (option (a) of the seventh session) would
be a false invariant. On that image `ReadAll` fails too (the same gap: `ErrSliceOutOfRange`), so what the
restart needs, and takes, is **`tReadsBackOk I := ∀ cut s σ', walReadAllOk I cut s σ' → walReadsBack I`**
(`RestartOk.lean`): where `ReadAll` succeeds, the history reads back. It is a premise of `restartRead.spec`
and `member.restart.spec` (on the WAL state `d`), the obligation of whoever carries the oracle invariant.
Option (b) (proving it from the raft discipline) needs a history invariant every operation maintains (entries
contiguous above the commit, commit at most the last index, the `opRecvSnap` shape), which lives in the ops'
specs (`wal-c-ops`) and in lemmas about images that are not prefixes; not attempted. I believe `tReadsBackOk`
holds of the tester's images (the deviation `readAllFold_zero_dev` needs a commit above the last index), but
it is not proved.

## Open point 2 (sizes)

- `restartRead`: the opens' growth is proved, not assumed: `tEncodeOracle_withOpens_length` (8 bytes per
  open, whatever the values); the premise is `(tEncodeOracle o).length + 16 ≤ 2^30` (two attempts).
- `restart`: `storeOracle` of `tCheckRestart (tWithOpens o ls) c` needs its `tOrSmall`, which depends on the
  candidates' images (their number and lengths), not on values; taken as the explicit premise
  `∀ ls c, tOrSmall (tCheckRestart (tWithOpens o ls) c)`. Note for U7: across unboundedly many incarnations
  the candidates' histories grow without bound (they start from `Create`), so the 1 GiB bound is an
  assumption on the run's length, not a fact.

## Done

- `TP/RestartOk.lean` (pure): `tWalPathsOk` (the area's path premises, a world premise of the root),
  `tWithOpens` and its encoding length, `tCandOk_addOpen` (monotonicity), `walOpenRaise_idem`, `tReadsBackOk`,
  `tRead_of_readAll` (`tCheckNext_of_read`'s core, naming the image: `tRead img = some c`), `tHasCand` with
  `tAddCand_has/_keep`, `tCandNext_keep/_has`, `tCheckNext_has` (the image is among the next candidates with
  bounds at least its candidate's), `tRaiseUnl_ge`, `tRead_hs`, and **`tRestart_ok`**: the new oracle's
  candidate accounts for the WAL as a running member's (`tMemOk`, `tMemHs`, `tCandOk`, mark = `|d.H|`).
- `TS/restartRead.lean`: the spec (see its header).
- `TP/RestartOk.lean` also: `tCheckNext_imgs` (the next candidates are images of the candidates' histories),
  `tCheckWf_restart` (the new oracle meets `tCheckWf`, within 1 GiB, through `OrLen.tOrSmall_hist_lt`).
- `TP/RestartLive.lean`: `tMemFields_read` (the fields `resume` sets from a well-formed history's read meet
  `tMemFields`: the hard state's term the last save's, the base term a snapshot's, the entries' `tEntWf`).
- `TS/member__restart.lean`, `TP/member__restart.lean`: **`member.restart.wp_proof`** over `restartRead.spec`,
  `checkRestart.spec`, `storeOracle.spec`, `member.resume.spec`. Its `true` post is **`memLive W e γ m ½ o''`**
  at the new oracle (`o'' = tCheckRestart (tWithOpens o ls) c`): `memSaveRes` with the handle's `walLenLb`, the
  fields with `tMemFields`, `walPurgeW`, `tMemOk`/`tMemHs`/`tCheckWf`, so `step` can continue from it.

## Statement changes (the coordinator's item 3, from `ops.md`)

- **`tOpWf`** (`Defs.lean`) gains `o.snap = false → uint.nat o.hs.term' < 2 ^ 63` (a save's hard-state term), so a
  restart's read term is bounded (`tMemFields_read`). Constructors re-proved: `tSaveOp_wf` (now takes the bound),
  `tSnapOp_wf`, the torn op in `Check.tHistWf_of_mem_tImgs`; the users of the second clause
  (`RefLemmas`, `RestartPure`, `opResend`) take `.2.1`.
- **`member.save.spec`**: premise `uint.nat h.term' < 2 ^ 63`; `tCandOk_save1`, `tMemOk_save1`, `tInv_saveAu`,
  `tCheckWf_saveO` take it too.
- **`opTerm.spec`, `opCommit.spec`**: premise `uint.nat t < 2 ^ 63`; **`opResend.spec`**: premise `tMemFields t M`
  (its `t'` is bounded by the loop's `tMemFields t M → tMemFields t' M'`). `opEntries` (its `t < 2^63`) and
  `opRecvSnap` (`memLive`) had the bound. All implied by `memLive`.

## Next steps

1. The user's decision above; then `restartRead.wp_proof`, all over existing specs: the AUs on `TInv`
   (`ValidSnapshotEntries`, `Repair`: `walDirIs` unchanged; `ReadAll`: `walDiskAt` unchanged, its newest-pair
   premise from `d.H`/`d.cut` being stable; `Open`: both ghost halves of the WAL state to the raised `d1`,
   `tRelI` of the stored oracle from `tCandOk_open` and the persistent `walSyncedLb (tCandMark o cd)`); the
   snapshot literal `walSnapIdTerm` (as `CreateSnap.walSnapAt_lit`); the loop invariant over `repaired`
   (`l = [idx]` or `[idx, idx]`, `walOpenRaise_idem`), the permissions (`Open`'s half plus
   `Close.specFailed`'s half for `Repair`); on success `tRead_of_readAll` (with `hsGet`'s and `fromRaft`'s
   specs for the read).
2. Discharging `tReadsBackOk` (open point 1) and the size premise in the invariant (U7 / whoever owns it).

# Ninth session (branch `wal-c-tester2`, 2026-11-15): the tester's Go changes; `restartRead`, `saveSnap`

Base `origin/wal-int` (`bf4cf547b9`), merged again (`79bbbe6b65`, notes only). No axiom added; one retired
(`purgeRound`, below). No `sorry`. Nothing trusted or generated edited by hand.

## The Go changes (the user's decisions of 2026-11-15, "Fixup the tester as needed")

Recorded in `notes/decisions.md`, "WAL tester over fsExt: Go changes". In `examples/etcd/wal/`:
1. `restartRead`: `snaps[i].GetIndex()`/`GetTerm()` (was `*snaps[i].Index`/`*snaps[i].Term`).
2. `saveSnap`: `&raftpb.ConfState{Voters: []uint64{1}, AutoLeave: new(bool)}` (raft's canonical form).
3. `Boot(area, orDir, seed, nOps)`: the WAL area (WAL `area/wal`) and the oracle directory (`orDir/state`) are
   the environment's; no `TouchDirAll`. `Main(area, orDir)`. The harness (`robust_test.go`) creates
   `root/data/member` beside `root/oracle` and calls `Boot(root+"/data/member", root+"/oracle", …)`.
4. The oracle's size: `fits(o, room)` (oracle.go: `len(encodeOracle(o)) + room <= maxOracle = 2^30`). `step`
   returns false unless `fits(m.o, oracleRoom = 256)`; `restart` unless `fits(m.o, 16)` before `restartRead`
   and `fits(m.o, 0)` before storing `checkRestart`'s oracle. Chosen over a `storeOracle` that refuses (that
   would add a false arm at every store, i.e. change every operation's spec); the two places are where the
   oracle can grow by more than a caller-known constant.
5. `purgeRound` dropped, with its call and the purge bound's raise in `opOwnSnap`; retired with it: the main
   tree's approved axiom `Proof/.../examples/etcd/wal/purgeRound.lean`, its spec, `PurgeBody.lean`, the Go
   evidence `purge_test.go`; the main tree's goose configuration (`Code/.../etcd/wal.toml`) now translates
   everything. **It returns with a lock model** (`notes/wal-fsext-plan.md` gap 3, Q1): then `opOwnSnap` raises
   the candidates' purge bounds again before a round, and `purgeRound` gets an `fsExt` spec over the lock model.
   `etc/tcb-baseline.txt` and the collections did not list the axiom (no result reached it): no change.

Checks: `go vet ./etcd/wal/...`, `go test ./etcd/wal/...` (pass), `TestRobust -chains 30 -model posix -fz
-fn` (210 incarnations, 180 checked restarts, 0 violations). `etc/goose.py --project etcd-wal` regenerated
both translations (main tree and `LinuxFs`); `--check --project etcd-wal` passes; `etc/gen-init.py`
regenerated both `Init.lean` (the tester no longer imports `os`, `strings`, `fileutil`).

## Proof repairs and statement changes

- **`TEnv`** (`TP/Inv.lean`): `area`, `orDir` in place of `root`; `tWalDir area = area ++ "/wal"`, `tOrPath orDir =
  orDir ++ "/state"` (`TP/Defs.lean`); `tArea`, `tDataDir`, `tOrDir` gone; `tOrPath_child orDir`; `tWalPathsOk
  area`. Every tester spec/proof rewritten mechanically (`tArea e.root` → `e.area`, …); all rebuild.
- **`member.restart.spec`**: loses its two size premises (`(tEncodeOracle o).length + 16 ≤ 2^30`, `∀ ls c,
  tOrSmall (tCheckRestart …)`): the two `fits` checks give them; gains `m ≠ null` (below). Re-proved.
- **`restartRead.spec`**: gains `m ≠ null` (ledger 2026-11-15: `restartRead` tests `m != nil`).
- **`member.saveSnap.spec`**: unchanged but its header (now proved).

## Proved (`lake build` of each module passes)

- **`fits`** (`TS/fits.lean`): `b = true ↔ tOrRoom o room` for `room ≤ 2^62`.
- **`restartRead.wp_proof`** (`TP/restartRead.lean`), over `ValidSnapshotEntries`, `Open`, `WAL.ReadAll`,
  `WAL.Close.specFailed`, `Repair`, `walpb.Snapshot.GetIndex/GetTerm`, `newU64`, `storeOracle`, `fromRaft`
  and `RaftModel.Getters`' `wp_hsGet*`. The newest-pair loop computes `walNewestPair` (`walNewestPair_loop`);
  the attempt loop's invariant is `(repaired, l, dc)` with `|l| = [repaired]`, `dc.H = d.H`, `dc.cut = d.cut`,
  `tCandOk (tWithOpens o l) cd dc`; on success `tRead_of_readAll` names the image.
- **`TP/RestartAu.lean`** (new, non-spec): `tInv_dirAu` (VSE/Repair), `tInv_readAu` (ReadAll, with its
  newest-pair premise), `tInv_openAu` (Open's raise, both WAL halves moved, the invariant's relation by the
  member's candidate), `walOpenRaise`, `tNewestStep`/`walNewestPair_loop`, `walSnapIdTerm_lit` (Open's
  argument frozen), persistence instances of `walSnapsAt`/`walEntsIn`.
- **`member.saveSnap.wp_proof`** (`TP/member__saveSnap.lean`), over `storeOracle`, `newU64`,
  `WAL.SaveSnapshot`. **`TP/SnapAu.lean`** (new): `tSnapD`, `tCandOk_snap1`, `tMemOk_snap1`, `tMemHs_snap`,
  `walSnapCanon_absSnapMd`, `absSnapMd_enc_lt` (< 2^40), `tRelI_snap1`, `tInv_snapAu`, and
  **`walSnapAt_litCs`**: the literal with the canonical conf state, frozen, is `walSnapAt walRaftMr _
  (absSnapMd idx term) true` (its object is `walSnapCanon`, so `snapEnc c = walRaftMr.encSnap md` by `rfl`).
  So `opRecvSnap` now links (its callee hypothesis is proved).

## Not done, next steps (in order)

1. **`member.opOwnSnap`**: unblocked, not written. Its spec in `memLive` form, as `opRecvSnap`'s. Needs: a pure
   `tRaiseNames o a` (every candidate's `unl` raised to `tNameBound (cd.h ++ since) a`, Go's `>` on `uint64`),
   its encoding length equal (`tEncodeOracle_length`: only `unl` values change), the candidates loop (as
   `checkRestart`'s, `CandsLemmas.candsElems_set`), `m.terms[a]` (map lookup; `tMemFields` bounds it), and
   `ReleaseLockTo`'s AU on `TInv` (the record at `i = |d.H|` before the snapshot's append, `i < n = |d.H| + 1`
   from `saveSnap`'s `walSyncedLb`; the raise is accounted for by `walReleasePos_le_openPos`, `walOpenPos ≤
   walNameBound … false` (it is a `min`) and `tNameBound_eq`).
2. **`member.step`**: its arms but the restart are in reach (`opTerm/opCommit/opEntries/opResend` to `memLive` by
   `memSaveRes_post`; `fits(m.o, 256)` gives each op's `tOrRoom`). **The close-and-restart arm is blocked** on
   `restart`'s premise `tReadsBackOk (d.H.map toM)` of the member's WAL state, the eighth session's open point 1
   (true of the tester's histories as far as known, proved nowhere; it is a fact about the tester's raft
   discipline that every operation must preserve). `step`'s spec cannot discharge it from `memLive`; options:
   (a) carry it in `memLive` and prove its preservation by every operation (option (b) of the eighth session:
   entries contiguous above the commit, commit at most the last index, the `opRecvSnap` shape); (b) state
   `step`/`Boot` with an explicit premise on every reachable history (a weaker closed theorem). I recommend (a);
   not a user decision unless (b) is taken into the closed theorem.
   The restart arm also needs `step`'s frame to carry `m.lg`, `m.walDir`, `zapLoggerOk`, `osPathS`, `walAreaRes`,
   and the half of the call permission `close` returns (joined with `memLive`'s for `restart`'s `osCallPerm 1`).
3. **`Boot`, `Main`**: `Boot`'s first start (`Create` with `walAbsent` from `TBoot`'s `od = none`, `freshOracle`
   stored, `resume` of the zero contents) and its restart path (`restart`, same premise as in 2); then the step
   loop and the final `close`. `Main` = `Boot(area, orDir, 0, 40)`. Not started.

## For the closed theorem (not stated: the user's hard stop)

Its premises as far as this session sees them: the world premises of `tBoot0`/`tBootCrash` (`RootsOk R`; `area`
and `orDir` two distinct roots, both in the first tree; no oracle file nor its temporary at the first boot;
`ReceiptBoundLe GF (2^62)`; `e.orFile.Ok`; `tWalPathsOk area`, i.e. `area` clean and absolute, `area/wal`
shorter than `2^59`); `W1` (no CRC collision) as the crash premise (`hQ`); `BootFo` of the crashed tree until
`walFoRes` lands (tcrash.md); `WalDecEnvSupply` and the Perennial-gap hypotheses of `S/Link.lean`; and, until
step 2 above is done, `tReadsBackOk` of the restarted states.

# Tenth session (branch `wal-c-tester3`, 2026-11-15): `tReadsBackOk` carried; `opOwnSnap`; `step`

Base `origin/wal-int` (`9dcb7496e0`), merged again after `wal-c-create2` landed (`8d6f3670d8`, a fast-forward:
nothing to repair) and after the notes-only `23c56c7a32`/`be30c5013c`. No axiom, no `sorry` added, nothing
trusted or generated edited, no Go changed. `#print axioms` of `member.step`, `member.opOwnSnap`,
`member.restart`: no `sorryAx` (only the generated type axioms every tester proof shows).

## 1. `tReadsBackOk` carried by the tester's invariant (option (a), done)

The weak form, as the coordinator decided: wherever `ReadAll` succeeds on an image of a candidate's history at
its mark, the image reads back (`walReadsBack`). Proved for every image, through an invariant every operation
keeps. No counterexample: the eighth session's bad image (a received snapshot's record, then its `Save` torn) is
exactly the case where `ReadAll` and `walRead` both fail.

- **`TP/SimFold.lean`** (pure, WAL-generic): two folds of one history, the *guide* (`gFold`: applies the records
  a list marks, checks commit ≤ last index and every snapshot record's admissibility `gSnapOk`: below the
  base, at or below the commit, or at or above the last index) and any fold applying at least its records
  (`remask c`). `gFold_remask`: the second follows the first (`SRel`: same hard state, a base at least the
  guide's, the guide's entries above it). `gFold_readsBack`: a guide marked by the history's own last commit is
  `walRead`'s fold, so `walReadsBack`. `readAll_bad`: the torn `Save` after a received record above the commit
  and the last index fails `ReadAll` from **every** position (`fold_bound`: at the fixed base `B` the fold's last
  index stays `≤ max B` the guide's).
- **`TP/ReadsBack.lean`**: `TDisc σ B σ'`, the raft discipline of the operations since the last restart (a
  `Save` whose fold succeeds, commit ≤ last index, commit not going down, entries above the old commit; an own
  snapshot at or below the commit; a received one above the last index immediately followed by its `Save` with
  commit at least its index and entries above it). **`tSimAt H n σ`**: `H = A ++ B`, `|A| ≤ n`, `A` the image
  the last restart read (its guide re-marked by its own commit succeeds, to `σA`), `B` disciplined from `σA` to
  `σ`. **`tSim H n`**: that, or such a history followed by a received record whose `Save` has not come.
  Results: `tSim_readsBack` (every image at the mark: `ReadAll`'s success gives `walReadsBack`), `tSim_img`,
  `walRead_bad`, `tSim_restart`/`tSim_restartRead` (an image whose read succeeds starts `tSimAt I |I|` at its
  `walRead`), the steps `tSimAt_save/_own/_recv`, `tSim_snapT`, `tSim_mark`, `tSimAt_nil`. Why the decomposition:
  a restart may read past a received record whose `Save` a crash lost (the record stays in the WAL above the
  commit, and is applied once the commit passes it); the guide is the member's view, which ignores it.
- **Carried**: `tCandOk` and `tMemOk` (`Defs.lean`, `Member.lean`) gain a last conjunct `tSim ((tCandHist o c).map
  absOp) (tCandMark o c)`, so `TInv`'s `tRelI` carries it across operations and crashes (`tCandOk_crash` keeps
  the candidate). `tCandOk_readsBack` (`RestartOk.lean`): `tCandOk o c d → tReadsBackOk (d.H.map toM)`.
- **`TP/MemberSim.lean`**: `tMemSim o c bs l cm` (the history disciplined since the last restart, at `|c.h|`, up
  to a fold whose base, last index and commit are the member's fields), carried by `memLive`; one lemma per kind
  of operation giving `save`/`saveSnap`'s new `tSim` premise and the new `tMemSim` (`tMemSim_save` for
  consecutive entries above the base and the commit, `tMemSim_own`, `tMemSim_recv`), `tConsec`, and
  `tMemSim_last_lt` (the last index below `2^63`, which `opOwnSnap`'s snapshot index needs).
- **Each operation keeps it**: `save`, `saveSnap` (take the premise), `opTerm`, `opCommit`, `opEntries`
  (its loop now tracks the entries' consecutive indices from `lo > max(commit, base)`), `opResend` (from
  `last + 1`), `opRecvSnap`, `opOwnSnap` (below), `sync`/`close` (`tMemOk_synced`: the mark only grows).
- **The restart establishes it**: `tRestart_sim` (`RestartLive.lean`): the image read is disciplined from its own
  `walRead`, and `resume`'s fields are that fold's (`walEntsWf`: the last entry's index is the last index; the
  read commit is within it). The **first boot** has `tSimAt_nil` (used by `Boot`, not written).

### Statement changes (all tester-internal; ledger not needed: no statement was false, only strengthened)

- `tCandOk`, `tMemOk`: the `tSim` conjunct (above). `tHistWf` users take `.1` of the old last conjunct.
- `member.save.spec`, `member.saveSnap.spec`: premise `tSim` of the appended history (`tCandOk_save1`,
  `tMemOk_save1`, `tInv_saveAu`, `tCandOk_snap1`, `tMemOk_snap1`, `tInv_snapAu` take it).
- `member.opTerm/opCommit/opEntries/opResend.spec`: the member's `base`/`last` values and premise `tMemSim o c bs
  l cm`; their true arms add `tMemSim` at the new oracle and fields.
- `memLive`: the conjunct `tMemSim o c bs l cm`.
- **`member.restart.spec` loses its `tReadsBackOk` premise** (derived, `tCandOk_readsBack`); `tRestart_ok`
  takes the new candidate's `tSim`.

## 2. `member.opOwnSnap` (done)

`TS/member__opOwnSnap.lean`: `{memLive o ∗ tOrRoom o 56} opOwnSnap {b; if b then ∃ o', memLive o' ∗ |enc o'| ≤
|enc o| + 56 else True}`. Proof `TP/member__opOwnSnap.lean` over `rnd.choose`, `saveSnap`, `copyOps`,
`nameBound`, `storeOracle`, `WAL.ReleaseLockTo`. New: `TP/OwnSnapPure.lean` (`tRaiseCand`, `tRaiseNames`: the
candidates loop; the encoding's length unchanged; `tMemOk/tMemHs/tCheckWf/tMemSim_raise`; `tReleaseD`,
`tMemOk_release`: `walReleasePos ≤ walOpenPos ≤ walNameBound … false = tNameBound ≤` the raised bound),
`TP/OwnSnapAu.lean` (`tInv_releaseAu`, `ReleaseLockTo`'s update on `TInv`, the record at `|hist|` before the
snapshot's append, `< ` the synced mark). The loop's invariant: `tRaisePre o a k` (the first `k` candidates
raised).

## 3. `member.step` (done)

`TS/member__step.lean`: `{memLive ½ o ∗ zapLoggerOk lg ∗ m.lg ↦ lg ∗ m.walDir ↦ tWalDir area ∗ osPathS ∗
walAreaRes} step {b; osPathS ∗ walAreaRes ∗ m.lg ∗ m.walDir ∗ if b then ∃ o', memLive ½ o' else True}`, premises
`m ≠ null`, `e.orFile.Ok`, `tWalPathsOk area`. At `Open`'s half of the call permission (`memLive`'s `qc = ½`):
`close` returns the other half, joined for `restart`'s `osCallPerm 1`. `fits(m.o, 256)` gives each operation's
room. Helpers `TP/StepLive.lean` (`memFields`, `memLive_intro`, `memLive_post`, `tCheckWf_step`,
`osCallPerm_join2`).

## 4. `Boot`, `Main`: not written; three open points found

`Boot`'s callees all have specs (`loadOracle`, `wal.Exist`, `wal.Create`, `freshOracle`, `storeOracle`,
`member.resume`, `member.restart`, `member.step`, `rnd.choose`, `member.close`, `newRnd`, zap's `NewNop`), but:

- **(B1) A not-created oracle with an existing WAL** (a crash after `Create` committed and before the store of
  `created`): `Boot` calls `restart()` with the fresh oracle. Go is fine (`checkRestart` reads the empty history
  and returns a created oracle), but `restartRead.spec`/`member.restart.spec` require `o.created = true`, because
  the oracle stored before each `Open` (the fresh one with `opens = [idx]`) must satisfy `tRelI`, whose
  not-created branch is `tPreOk` (`o = tFreshOracle`). **Options**: (a, recommended) generalize the not-created
  branch to `tPreOk o od ∨ (the candidate relation)`, or `tPreOk` up to `opens` (`{o with opens := []} =
  tFreshOracle`), and drop `created` from `restartRead`/`restart`/`tInv_openAu` (their tRelI cases), the crash's
  `tRel_crash`/`tPreOk_crash`; the fresh oracle's candidate `⟨[], 0, 0⟩` accounts for `Create`'s fresh WAL
  (`walImg [] 0 []`, `tSimAt_nil`). About one session. Not a user decision (tester-internal invariant).
- **(B2) The panic** ("the WAL vanished after `wal.Create` returned"): from `Exist = false` (`ExistFalseOk od`:
  none, or empty and unnamed) and `o.created` (`tRelI`: `od = some d`, `walNamed`), a lemma that `walNamed dir`
  (a `walPast` lower bound) and `walDirIs dir (some d)` give `d.named = true`: `Ghost.walPast_ghost_le` (`absLe p
  s`) and `named` monotone along `absLe`; to write in WalFs' vocabulary (one lemma).
- **(B3) `Create`'s AU needs `walAbsent` (`od = none`)**, while `ExistFalseOk`/`tPreOk` allow `od = some d` empty
  and unnamed. At a generation's start that state does not occur: `walDiskAt_crash_any_keep` (`S/Crash.lean`)
  maps an unnamed WAL to `walAbsent` in the new generation, and the first boot has `od = none`. So `TBoot`
  (and `TCrashed`, from `tester_crash`'s `tWal_crash`) should carry `∀ d, od = some d → d.named = true` (or
  `tPreOk`'s second branch with `named`); then `ExistFalseOk od` gives `od = none` and `Create`'s AU applies.

## For the closed theorem (not stated: the user's hard stop)

Premises as far as this session sees them (unchanged from the ninth but for `tReadsBackOk`, now proved):
- the world premises of `tBoot0`/`tBootCrash`: `RootsOk R`; `area`, `orDir` two distinct roots of the first tree;
  no oracle file nor its temporary at the first boot; `ReceiptBoundLe GF (2^62)`; `e.orFile.Ok`; `tWalPathsOk
  area` (`area` clean and absolute, `area/wal` shorter than `2^59`);
- `W1` (no CRC collision) as the crash premise (`hQ`), `AbsDiskGpreS GF`, `(orDir, jo) ∈ R`;
- `BootFo` of the crashed tree until `walFoRes` lands (tcrash.md);
- `WalDecEnvSupply` and the Perennial-gap hypotheses of `S/Link.lean` (`errors.*`, `fmt.ErrorfErrsNot`,
  `filepathlite.IsAbs`), `proto.UnmarshalWalRecordE`, the model laws (U4);
- **no `tReadsBackOk` premise** (this session).

## Next steps (in order)

1. (B1): generalize `tRelI`'s not-created branch, drop `created` from `restartRead`/`restart`.
2. (B2), (B3); then `Boot.spec`/`wp_proof` (first start: `Exist`, `Create`, fresh oracle with the empty
   candidate, `resume` of the zero contents into `memLive` with `tSimAt_nil`; restart path; the `step` loop with
   `memLive ½`; the final `close`), over `TBoot` minus the crash tokens (which the crash condition keeps).
3. `Main` = `Boot(area, orDir, 0, 40)`, then the U7 statement (the user's).
