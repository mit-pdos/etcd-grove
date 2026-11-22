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

# Eleventh session (branch `wal-c-tester4`, 2026-11-15): B1, B2, B3; `Boot`, `Main`

Base `origin/wal-int` (`32a65fbcae`), merged again (`origin/wal-int` at `96d2ee138a`, unit `noioerr`: no
conflict, nothing of the tester rebuilt). No axiom, no `sorry`, nothing trusted or generated edited, no Go
changed. `#print axioms` of `Boot.wp_proof`, `Main.wp_proof`, `member.step.wp_proof`, `member.restart.wp_proof`,
`restartRead.wp_proof`, `WalFs.walDirIs_named`: no `sorryAx` (the generated type axioms only; `tester_crash`
also `recEncC_ok`, as before). **One new hypothesis spec** (`wal.Create.specFresh`, B3 below), taken by
`Boot.wp_proof`.

## Proved (`lake build` of each module passes)

- **`Boot.wp_proof`** (`TS/Boot.lean`, `TP/Boot.lean`): `{isPkgInit ∗ TRun W e γ o od} Boot(area, orDir, seed,
  nOps) {st; True}`, premises `e.orFile.Ok`, `tWalPathsOk e.area`, `(e.area, e.jr) ∈ e.R` (the area's spine,
  `osPathS_root`). Over `zap.NewNop`, `newRnd`, `loadOracle`, `wal.Exist`, **`wal.Create.specFresh`**,
  `freshOracle`, `storeOracle`, `member.resume`, `member.restart`, `member.step`, `rnd.choose`, `member.close`.
  The proof: before any step (`wp_notCrashed_acc`), the oracle's relation is read off the invariant
  (`tInv_rel`) and, when the oracle is created, the WAL's view raised to named (`tInv_named`, B2); `Exist`
  committed unchanged (`tInv_dirAu`); its `false` arm with a created oracle is refuted (the panic is dead);
  with a not-created oracle `Create` from that state (`tInv_createAu`), the fresh oracle with `created` stored
  (`tCandOk_freshC`, the mark 0), the zero contents resumed and `memLive` built (`tMemOk_freshC`,
  `tMemSim_freshC`, ...); the `true` arm restarts (`tRelI_relW`: the candidate, `tCheckWf`, `tRelW`); both
  starts end in `memLive ½ o' ∗ ⌜tOrSmall o'⌝`, then the step loop and, by the choice, `close`.
- **`Main.wp_proof`** (`TS/Main.lean`, `TP/Main.lean`): `Boot(area, orDir, 0, 40)`, same pre and premises.
- **`TRun`, `TBoot_run`** (`TP/Inv.lean`): `TBoot e ⊣⊢ ∃ W γ o od, TRun W e γ o od ∗ walCrashTok ∗
  durCrashTok`: the program's part and the crash tokens the crash condition keeps.
- **`WalFs.walDirIs_named`** (`S/NamedView.lean`, new, non-spec; over the ghost lemma `walGhost_named` and
  `walMapLe_named`): at a step of the generation (`notCrashed`), `walInv ⊢ walDirIs dir (some d) -∗ walNamed dir
  ={E}=∗ walDirIs dir (some {d with named := true})`.
- **`TP/BootAu.lean`** (new): `tInv_rel`, `tInv_named`, `tInv_createAu`, `tRelI_relW`, `walAreaOk_os`; pure:
  `tPre_since`, `tCandOk_fresh`, `tFreshC` (the created fresh oracle) and its facts, `tCheckWf_pre`.

## B1 (done as recommended, option (a))

- `tPre o := {o with opens := []} = tFreshOracle`; **`tPreOk o od := tPre o ∧ (od = none ∨ ∃ d, od = some d ∧
  tCandOk o tCand0 d)`** (`TP/Defs.lean`; was `o = tFreshOracle ∧ (none ∨ the fresh WAL's shape)`).
  `tCand0 = ⟨[], 0, 0⟩` is the fresh oracle's candidate; `tCandOk` of it at mark 0 is the old shape with the
  unlock position raised by the opens.
- **`tRelW area o cd`** (`TP/Inv.lean`): created: `⌜tCheckWf o⌝ ∗ walSyncedLb (mark) ∗ walNamed`; not created:
  `⌜tPre o⌝`. `tRelI_of_relW` (with `cd ∈ o.cands`, `tCandOk o cd d` it gives `tRelI o (some d)`),
  `tRelW_withOpens`.
- **`restartRead.spec`, `member.restart.spec`**: over any WAL state `od` (`tWalOwn γ od`, `∀ d, od = some d →
  tCandOk o cd d`, and `∀ d, od = some d → tReadsBackOk …` for `restartRead`) and `tRelW` in place of
  `o.created = true ∗ walSyncedLb ∗ walNamed`; `restartRead`'s post relates `od` and `od'` by `Option.Rel`, its
  success arm names `d` (`od = some d`). `tInv_dirAu` takes any `od`; `tInv_openAu` takes `tRelW`.
  `Boot`'s restart with a not-created oracle needs both: the WAL may be absent (`ValidSnapshotEntries` fails)
  or `Create`'s.
- Crash: `tPreOk_crash` now from `tCandOk_crash` (mark 0, `tPre_mark`); `tWal_crash` unchanged otherwise.

## B2: the recommended lemma is false; done with a view raise

The tenth session's lemma "`walNamed dir` and `walDirIs dir (some d)` give `d.named = true`" is false:
`walDirIs` is a lower bound of the real state (`walOptLe`), so a view with `named = false` is consistent with a
named WAL (`Create` returns the view `walDurFresh md`, `named = false`, beside `walNamed`; a crash keeps the
view's `named`). And `Exist`'s `false` arm is `ExistFalseOk` of the view, so the contradiction needs the view
named *at `Exist`'s linearization*. Done: `WalFs.walDirIs_named` (above, the WAL's vocabulary, minimal: the
program's map raised to the real state's `named`, which `walNamed` and `absLe` give), used by `tInv_named` at
`Boot`'s first step, before `Exist`.

## B3: the recommended fix is false; a hypothesis spec instead (decision for the coordinator / WAL owner)

The note "a crash maps an unnamed WAL to absent (`walDiskAt_crash_any_keep`)" is wrong: the trusted
`walCrash` (`LinuxFs/GooseLang/Ext/AbsDisk/Impl.lean:230`) is `(d.named = false ∧ d' = none) ∨ (an image,
named kept)`, and its comment says why (a WAL that survived a kill between `Create`'s rename and its parent's
fsync is seen through a name in the page cache only; a later power loss can still revert the rename). So a
generation may start with a fresh, unnamed WAL (after `Create` failed after its rename: `cleanupWAL` may have
moved it aside without fsync, then a crash), `Exist` may answer `false` (`ExistFalseOk`), and `Boot` calls
`Create`, whose spec takes only `walAbsent dir`. Nothing in the tester can turn that state into `walAbsent`.

Taken as **a hypothesis**, `wal.Create.specFresh` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/
CreateFresh.lean`): `Create.spec` with its update from `∃∃ o, walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝` (none, or a
fresh unnamed WAL), committed to `walDurFresh md` as before; `Create.spec` is its `o = none` case. True of the
Go code: `Create` returns `os.ErrExist` before any effect when `Exist(dir)` finds a `.wal` file, and a fresh WAL
whose directory is at `dir` holds its first segment (F-N1), so `Create` proceeds only when the unnamed WAL's
directory is not at `dir`, and then `RemoveAll(dir)` and the rename put the new WAL in place as from an absent
one. Options:
- (a, recommended) the WAL layer proves `Create.specFresh` (generalize `Create`'s creating update to
  `ExistFalseOk`; the invariant must let the commit replace an unnamed, empty WAL whose directory is not at its
  name, `AbsentNone`-like), and `Create.spec` follows;
- (b) a sharper `Exist` spec at a generation's start plus `walInv_crash` choosing `d' = none` when the crashed
  tree lacks the directory (two WAL-layer changes, and a fresh unnamed WAL kept present still needs (a));
- (c) keep the hypothesis in the closed theorem (not recommended: it is a WAL fact).
Ledger entry 2026-11-15 ("`wal.Create.spec`: the update from `walAbsent` only").

## A further gap found: the loaded oracle's well-formedness (fixed, tester-internal)

`restart` (`checkRestart`) needs `tCheckWf o` of the oracle `Boot` loads, and nothing carried it (`memLive`
has it for the running member's oracle only). **`tRelI`'s created branch now carries `tCheckWf o`** (every
stored oracle is a running member's). Statement changes (all tester-internal strengthenings): `tRelI`
(created: `… ∧ tCheckWf o`), `tRelI_save1`/`tRelI_snap1` (premise `tCheckWf` of the appended oracle;
`tCheckWf_saveO1`, `tCheckWf_snapO1` new in `OrLen`/`SnapPure`), `tRelI_synced` (premise `tCheckWf o`),
`tRelI_checkWf` (new); specs **`member.save`, `member.saveSnap`, `member.sync`, `member.close`,
`member.opEntries`, `member.opCommit`, `member.opTerm`** gain the premise `tCheckWf o` (their callers have it
from `memLive`). `SavePure.absHs_phsNext` removed (a duplicate of `RefLemmas.absHs_phsNext`, now imported).

## Also changed

- **`member.step.spec`**: the post's oracle is small (`memLive ½ o' ∗ ⌜tOrSmall o'⌝`): `Boot`'s final `close`
  stores the synced oracle (`tOrSmall (tSynced o)`), which no `fits` check precedes. `member.restart.spec`'s
  post likewise (`… ∧ tOrSmall o''`, from its `fits(m.o, 0)`). `StepLive`: `tOrSmall_saveO_room`,
  `tOrSmall_grow`.

## For the closed theorem (not stated: the user's hard stop)

`etcd_wal_adequate`/`etcd_wal_safe` over `fsSQ_crash_adequacy`: each generation's program is `Main(area,
orDir)`; its precondition after `wp_osShare` is `TBoot e` (first: `tBoot0`; after a crash: `tester_crash` then
`tBootCrash`), split by `TBoot_run` into `Main.spec`'s `TRun` and the crash tokens, which with `TRun`'s
persistent parts (`TInv`, `walAreaOk`, `dirDurable`, `durInv`) form the crash condition `tester_crash` takes.
The exact premises it would carry:
1. World (the first tree `V`, roots `R`): `RootsOk R`; `(area, jr) ∈ R`, `(orDir, jo) ∈ R`, `jo ≠ jr`, `jr ∈
   V.now`, `jo ∈ V.now`, `V.2 = []`; no entry of the area at an `AreaSlot` name; no oracle file nor its
   temporary in `orDir` (`e.orFile.b`, `e.orFile.tb`); `e.orFile.Ok`; `tWalPathsOk area` (`area` clean and
   absolute, `area ++ "/wal"` shorter than `2^59`).
2. Ghost/semantic: `ReceiptBoundLe GF (2^62)`, `AbsDiskGpreS GF`.
3. The crash premise: `∀ st st', Q st st' → W1 walCodec st st'` (no CRC collision).
4. `BootFo V'.now jr` of every crashed tree (until `walFoRes` lands; `tester_crash`'s `hfo`).
5. The callee hypotheses no proof discharges yet: **`wal.Create.specFresh`** (B3); `wal.Exist`'s `false` arm's
   ENOENT hypothesis (`fileutil.ReadDir.specChildIs`); `WalDecEnvSupply` and `S/Link.lean`'s Perennial-gap
   hypotheses (`errors.*`, `fmt.ErrorfErrsNot`, `filepathlite.IsAbs`), `proto.UnmarshalWalRecordE`, the model
   laws (U4). Every other callee spec of `Boot`'s tree is proved (the tester's link file is not written: a
   `Link.lean` for the tester, `etc/gen-link.py`, is the next step before the closed theorem).

## Next steps

1. A tester `Link.lean` (all the tester's `wp_proof`s linked, `Boot`/`Main` at the top), then `etc/tcb-report.py`
   on it.
2. B3 option (a) in the WAL layer (`Create.specFresh` proved), then `Boot` over the proved spec.
3. The closed theorem (the user's).

# Twelfth session (branch `wal-safe`, 2026-11-21, etcd-grove-03's delegate): survey for U7; a pre-switch crash gap

No Lean changed. Every tester function is proved (108 modules under `WalTester/Proof/.../examples/etcd/wal/`,
no `sorry`, no `axiom`; `Boot`, `Main`, `tBoot0`, `tester_crash`, `tBootCrash`, `InitLinked.wp_initialize'`).
`Link.lean` links all 107 results; `wp_Boot`/`wp_Main` take 29 hypotheses. What is left is U7: the adequacy
assembly over `fsSQ_crash_adequacy`, the TopLevel files, and the hypotheses. Three blockers:

1. **A crash before the shared-mode switch (new).** `wp_osShareE` is a WP lemma: it reads the state interpretation
   at the program's first step. But `fsSQ_crash_adequacy`'s `Hwp` must hand over the crash continuation
   *before* the WP, and `RealCrashNsteps` allows a crash after 0 steps of a generation. In generation 0
   that window holds only `osTree` and pure facts, so `osTreeCrash_take` handles it, as in seglog. In a
   generation after a crash it holds `TCrashed L' e V'`, whose `walStart L'`, `trFile L'` and `durFound L'`
   no lemma carries across a second crash. tcrash.md's "For U7" assumes the old `TBoot` is available to
   the crash continuation; it is not before the switch. Options, each in a shared area:
   (a) an accessor form of the switch (`wp_osShareE_acc`, threading a fupd so that a "box" invariant
   `(osTree ∗ pre) ∨ (switched resources)` can be opened at the switch), plus re-crash lemmas for
   `walStart` (S/) and `durFound`/`durFoundTmp` (the part's durable), about 2 sessions;
   (b, recommended) a crash interpretation or adequacy variant that starts every generation in the shared
   mode, so no program has the window (etcd's restart, C6, will need the same), an extension-level change;
   (c) a premise on executions (no crash before the first fs step): false of real runs, not recommended.
2. **`BootFo` of every crashed tree** (tcrash.md): needs the WAL's `walFoRes`.
3. **Hypotheses**: the model laws are dischargeable now (`walPb_laws`, `walRaftHsO_own`, `walRaftU_*`).
   The Perennial-gap specs are pending. `proto.UnmarshalWalRecordE` is the user's.
   **`WAL.renameWALUnlock.spec` is false as stated** (its header, the ledger), so it can never be a premise
   of a closed theorem.
The draft closed statement, with its premises and axioms, is in the coordinator's log
(`/shared/tmp/coord-03/walsafe-log.md`); stating it is the user's hard stop.

# Handoff (branch `wal-safe`, 2026-11-21, etcd-grove-03's delegate): steps 2 and 3 not started

**State.** `wal-safe` is lean `b7b2bb0dca` (Perennial pin `d648cfe22`) merged, plus:
- (b1): `GooseLang/Ext/Fs/CrashAdequacyAcc.lean` (`goose_crash_adequacy_acc`, a local copy of Perennial's crash
  adequacy whose `Hwp` gets one update of the extensions' local ctx at each generation's start; recorded in
  `notes/perennial-changes.md`), `GooseLang/Ext/Fs/TreeSharedKit.lean` (the switch in two halves:
  `treeCtx_switchG`, `osSwitchKit_open`; `wp_osShareE_acc`), `GooseLang/Ext/Fs/AdequacyShared.lean`
  (**`fsSQ_crash_adequacyShared`**: every generation switched to the shared mode before its WP).
- Step 1: `renameWALUnlock.spec` gone (ledger 2026-11-21). `os.Rename.specDirS(nc)` witnesses its errors
  (`NoErrSpecsRenameDir.lean`); `renameWAL`/`wal.Create(.specFresh)` take
  `FsNoErrOn (· = dir) ∧ PathFits (dir ++ ".tmp") ∧ PathFits dir`; the tester's `Boot`/`Main` take `tWalFsOk area`.
- Everything builds: the WAL Link and the tester's Links (3586 jobs). No sorry, no axiom added.
- The coordinator's log, with the decisions and the draft closed statement, is `/shared/tmp/coord-03/walsafe-log.md`.

**Next: step 2, `walFoRes`** (discharges `BootFo` of every crashed tree, `tester_crash`'s `hfo`; main-tree WAL
proofs; approved by the coordinator). The design is in `notes/wal-fsext-w4c-plan.md`, U3 log, third session
("`hfo`: condition checked, design"). Its crash side is proved: `Proof/.../storage/wal/BootFilesOnly.lean`
(`HistNoDir`, `regionCrashed_filesOnly`). What remains is the invariant side, a framed conjunct of `walInv` (claims
`fl` at half, `HistNoDir` of them and of the WAL directories' claims), maintained by the updates listed there:
(1) the pipeline's `0.tmp`/`1.tmp`, (2) `Create`'s `nm.tmp` (mkdir, `.touch`, first segment,
`RemoveAll(nm.tmp)`, the rename), (3) `Repair`'s `.broken` file, (4) the WAL directories' new versions,
files-only (`cut`, `Create`'s commit, `Repair`, `renameWAL`), (5) the open point `cleanupWAL`.
**First decide** between the full design and the plan's cheaper alternative for (2): drop `TmpOk` for a
general-subtree `os.RemoveAll` spec (`SubCover`), and let `tmpClTouch` accept a directory `.touch`. Then only
`nm` (1, 3, 4) needs `fl`. Note that `BootFo`'s second conjunct ("no `nm.tmp` is a file") is what `TmpOk` needs.
Afterwards `walInv_crash` exports `BootFo V'.now jr`, and `tester_crash`'s `hfo` and `TCrashed`'s carried fact go.
Then, if cheap, remove `renameWALPost`'s dead arm 2 (and `Create`'s handling of it, `Create.lean` ~line 1185).

**Then: step 3, the tester's wiring** onto `fsSQ_crash_adequacyShared`
(`WalTester/Proof/.../etcd/wal/`, new modules; the closed statement itself is the user's hard stop):
- `P L V := ownGoState ∅ (or σ's) ∗ (first boot: ⌜V = (m₀, [])⌝ and the world facts) ∨ TCrashed e V`.
- `Hstart`: `P L (m₀, [])`.
- `Hwp`: from `osShared R V` (= `tBoot0`'s/`tBootCrash`'s inputs: `osSharedInv`, `osAboveInv`, `osCallPerms`,
  the claims; `osLogLb` unused), get `TBoot e`, then `TBoot_run` gives `TRun` for `initialize'; Main` and
  the crash tokens. The crash frame: `tester_crash` (it returns `osTree L' ∗ TCrashed L'`, the frame's shape).
- The semantics: `fsExtsSemanticsWithS (StepPrem.and (NoIoErr allIo) (NoMapLockErr allIo)) (fun st st' => W1 walCodec st st')`.
  `tWalFsOk` comes from `fsNoErrOn_of` and the area premise.
- `ReceiptBoundLe GF (2^62)` from `receiptBound GF = N` (bound the executions' length, as etcd's results do).
- The Link hypotheses: instantiate `P := walRaftP`, `U := walRaftU`, `HsO := walRaftHsO` (`RaftModel/Laws.lean`).
  The Perennial-gap specs stay hypotheses: list them in the draft statement for the user.

**Pitfalls.**
- Build only through `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-d64.json build …`
  (Perennial worktree `/shared/perennial-d648cfe22`).
- `etc/lean-check.py` with `LAKE_OPTS=--packages=…` still runs `lake setup-file`, which cloned Perennial into
  `.lake/packages/perennial` (d648) and builds there. It works, but its first check of a file deep in the
  tree is slow. `lake build` of the module is the reliable check.
- `etc/gen-link.py --walfs`/`--wal-tester` print the Link to stdout: redirect it to the Link file.
- In Iris proofs, `unfold X` acts on the whole goal, the context included; use `iunfold X at H` for one
  hypothesis (an `unfold osTree` before `treeCtx_switchG` unfolded the goal's later `osTree`).
- A crash frame gets no later (crashes need no step between them), so it can only read timeless contents out of
  an invariant: a box invariant cannot carry a client's crash continuation (`notes/perennial-changes.md`, the entry
  of 2026-11-21).

# Handoff (branch `wal-safe`, 2026-11-21, session 3 of etcd-grove-03's delegates): step 2 part (A) done, (B) designed

**State** (head after this note's commit; no axiom, no `sorry`, WAL Link and tester Links green at Perennial
`d648cfe22`):
- **Decision (step 2):** the plan's cheaper alternative for `nm.tmp` (drop `TmpOk` for a general-subtree
  `os.RemoveAll` spec **proved** over the existing model `TrustedCode/os.lean` `RemoveAll.impl`; no new axiom or
  trusted model), the full design for the WAL directories. Why: the full design for `nm.tmp` needs the same
  RemoveAll recursion plus AU-shaped `TouchDirAll`/`RemoveAll` and every `Create` step on `nm.tmp` under the
  invariant. A directory `.touch` makes `Create`'s probe fail and `Create` return an error with nothing
  committed; the tester's `Boot` returns `StatusDown` (wal.go:636), so that error arm is harmless.
- **(A) done** (`f2f58a363d`): `HistFo.lean` (`HistFoP P n j N h`: no version a crash at commit bound `n` may
  leave holds a directory at a name of `N` satisfying `P`; `.mono`, `.log`, `.of_coh`, `.of_boot`, `.cur`,
  `.crash`; `HistFoN` = `P := (· ∉ walTmps)`; `NoDirX`). `WalsNamed`'s per-layout body has a third conjunct
  `∀ N hj, (lay.j, N, hj) ∈ cl → HistFoN n lay.j N hj`, kept by every producer (cut, purge, Repair's create and
  removal via `nonwalHist_pure`'s new `hcd`, `walsNamed_create` (new premises `hA`, `hJo`), drop (new `hA`),
  cover, moved, mono, tail). `walInv_alloc`/`walsNamed_start` take the boot tree's `NoDirX` (`hfo`).
- **(A2) done** (`38d50f478a`): `walCrash_pure` also says each new layout's directory is an old layout's;
  `crash_noDirX`; `walInv_crash`'s pure post has `∀ nm J, walNameOk nm → V'.now.entry jr nm = some (.dir J) →
  NoDirX (entsOf V'.now J)` (after `TreeWf`).
- `3ac1bca1b9`: `BootFoRest` (`BootCrashSub.lean`: the pipeline names of the WAL directories hold no
  directory; `nm.tmp` directories files only; no `nm.tmp` a file) and `bootFo_of`; `tester_crash`'s `hfo` is now
  `BootFoRest V'.now e.jr`.

**Next (B): the pipeline names `0.tmp`/`1.tmp`** (gives `BootFoRest.1`). Design, checked against the code:
- `tmpClaim j b` holds **half** the claim (`osNames j (.only [b]) ½ h ∗ tmpEnt …`); the invariant holds the other
  half inside `walTmpParked` (part of `walParked`, so `walInvBody` keeps its shape and stays timeless): for every
  `dir ↦ J ∈ Jt`, `[∗list] b ∈ walTmps, ∃ h n0, osNames J (.only [b]) ½ h ∗ osCommitLb n0 ∗ ⌜HistFoP (fun _ => True)
  n0 J (.only [b]) h⌝`, beside the existing `if dir ∈ T then emp else walTmpsRes J`. Not a separate invariant:
  `inv` is not timeless, and the crash frame has no later.
- `pipeFile`'s `osNames … 1 h` becomes ½; `pipeQ`/`pipeLeft` follow `tmpClaim`.
- The pipeline must open `walInv` at its logs: put `∃ C Mr jr r X, walInv C Mr R jr r ∗ walDirKey dir j X` in
  `isFilePipe` (both persistent: `walDirKey` is `↪□`). In the AU, `walDirKeysAuth K` agrees `K !! dir = (j, X)`,
  `DirKeysOk.1` gives the layout `Ls !! dir` with `lay.j = j`, and `walTmpParked`'s `Jt ⊇` the layouts' gives
  `J`'s halves. Pipeline creators (`newFilePipeline` callers: `CreateHandle`, `Handle`, openAtIndex) supply it.
- The log sites (each through the existing `…Snc` os specs with `q = r = ½` and an AU opening `walInv`, then
  `HistFoP.log` with the new entry a file or a removal): `filePipeline.alloc` (`wp_createTmp`,
  `os.OpenFile.specCreateTruncSnc`; `wp_truncS` logs no name), `run`'s `os.Remove` on `donec`
  (`PipeLemmas.wp_removeTmp`, `os.Remove.specFileSnc`), `Close`'s leftover removal (`CloseLaw.lean:85`), `cut`'s
  rename (`CutPipe`/`CutAu`: already inside `walInv`'s AU, also update the source half). Unfold sites of
  `tmpClaim` to revisit: `CreatePre:130`, `BootCrashRes:260`, `CutPipe:40`, `PipeLemmas:193,404`, `CloseLaw:85`,
  `CreateUnmint:70`, `filePipeline__alloc:161`, `openAtIndexLemmas:211`; `walTmpParked`'s 21 uses (`Parked`,
  `CreateKeys` (Create adds the new `J`'s halves at its commit: histories all below its commit bound,
  `HistFoP.of_coh`), `Tail*`, `CutAuLemmas`, `PurgeAuLemmas`, `Crash`).
- Boot: `walInv_alloc` splits each `walTmpsRes J` into halves (`HistFoP.of_boot`, the boot history's cur from
  `tmpEnt`). Crash: `walInv_crash` runs `crashRest_region` on the halves (with their `osCommitLb n0`) and exports
  "no directory at `walTmps` of every WAL directory", which gives `BootFoRest.1`.

**Then (D): `nm.tmp`** (gives `BootFoRest.2`/`.3`): `os.RemoveAll.specSubS` (any entry at `d/b`, every directory
under it whole, `SubCover`; post: the claims back, `b` and its subtree some sub-forest of what they were, or `b`
gone), proved by Löb induction over `model.removeAllFrom` (reuse `RemoveAllFrom`/`RemoveAllLeaf`/`RemoveAllParts`);
`TouchDirAll` with a directory `.touch` (an error arm; an `os.OpenFile` spec answering `EISDIR` on a directory,
proved over the semantics); `walAreaRes` without `TmpOk`, `tmpClTouch` accepting any entry; `Create`'s proof over
them (`CreateTmp.wp_removeAllTmp`). Then `BootFo` loses its `nm.tmp` parts, `tester_crash`'s `hfo` goes, and
`TCrashed`'s carried fact with it. Then, if cheap, `renameWALPost`'s dead arm 2 (`Create.lean` ~1185).

**Then step 3** (the tester's wiring onto `fsSQ_crash_adequacyShared`), as the previous handoff says; the hard
stop before the closed statement stands.

**Pitfalls (new).** `rotate_left`/`rotate_right` after a `refine` with a new last `?_` (to prove the new
conjunct before the old bullets); `rw [Prod.mk.injEq, Prod.mk.injEq] at he` rather than `simp only`, which may
drop a component that reduces (a layout's `.j` through `cutLay`/`purgeLayP`). A `lake build` of
`Proof.go_etcd_io.etcd.server.v3.storage.wal.Link` after an `Inv.lean` definition change took about 25 minutes
in one slot (3329 jobs).

# Handoff (branch `wal-safe`, 2026-11-21, session 4 of etcd-grove-03's delegates): step 2 (B) done; (D) and step 3 not started

**State.** `fcd2e39948` (on `70bc6e12a8`): no axiom, no `sorry`; the WAL Link, the tester's Links (`Link`,
`InitLinked`, durable's `Link`) and the WAL's outside users (`etcdserver/RnNewStorageLinked`,
`etcdstart/WalAreasInit`) build at Perennial `d648cfe22`.

**(B), as built** (differs from the previous handoff's design in two points, both decided here):
- Fractions: the program holds **three quarters** (`qTmp`, `tmpClaim`), the invariant a quarter (`qTmpI`,
  `tmpHalf j b := ∃ h n0, osNames j [b] ¼ h ∗ osCommitLb n0 ∗ ⌜HistFoP True n0 j [b] h⌝`). Halves would
  have broken `tmpClaims_walTmpsRes` (`Close` puts two claims back; with ¾ two on one name contradict,
  `qTmp_two`).
- The invariant's quarters are a separate map, `walTmpHalves Ls` (`∃ Jh ⊇ layouts' directories`,
  `[∗map] Jh, walTmpsHalf J`); `walTmpParked Ls T := walTmpParked0 Ls T ∗ walTmpHalves Ls` (the old
  definition and lemmas renamed `…0`, the old names restated; `walTmpParked_create` takes
  `walTmpsHalf lay.j`; `walTmpParked_acc`).
- `TmpAu.lean`: `walInvBody_tmpAcc`, `walParked_tmpAcc`, `walTmp_osAUnc` (the caller keeps a quarter in
  the update, the call gets half: `q = r = ½`). Users: `PipeLemmas.wp_createTmp`/`wp_removeTmp` (now take
  `walInv` and `walDirKey dir j X`; `isFilePipe` has `∃ C Mr jr r X, walInv ∗ walDirKey dir j X`, so the five
  pipeline specs take `[W : WalGS GF]`, `newFilePipeline.spec` the conjunct), `CutAu.walCut_osAUnc` (new
  premise `tmp ∈ walTmps`; `walCutP`/`walCutQ` hold a quarter of the pipeline file's claim).
- Create: `createJ_claims` takes `syncDir(nm.tmp)`'s `osCommitLb` and returns `walTmpsHalf J` (`HistFoP.of_coh`);
  `walCreateP` carries it to the commit (`walParked_create`) or back to `create_unmint`/`create_Jback`
  (`tmpClaim_join`). `RenameWALOk`'s spine law (spec of `renameWAL`) also returns the invariant and the
  new WAL's key (for its `newFilePipeline`), `create_spine` gives them from `createU`.
- Boot: `walDir_boot` (new premise `V.2 = []`) returns `walTmpsRes J ∗ walTmpsHalf J` (`HistFoP.of_boot`,
  `osCommitLb 0`), `walInv_alloc` takes that map. Crash: `walInv_crash`'s pure post has, after `NoDirX`,
  `∀ nm J, walNameOk nm → V'.now.entry jr nm = some (.dir J) → ∀ b ∈ walTmps, ∀ J', entsOf V'.now J !! b ≠ some (.dir J')`
  (`tmpHalf_crash`, `tmpHalvesL_crash`, `tmpHalvesM_crash`, `crash_tmpNoDir`).
- Tester: `tester_crash`'s `hfo : BootFoNmTmp V'.now e.jr` (defined in the tester's `Crash.lean`: `BootFoRest`
  without its first part).

**Next: (D) `nm.tmp`** (gives `BootFoNmTmp`, so `hfo` and `TCrashed`'s carried fact go), unchanged plan:
1. `os.RemoveAll.specSubS` (new spec in `Spec/os/RemoveAll.lean`, proof a new `Proof/os/RemoveAllSub*.lean`):
   any entry at `d/b`, every directory under it claimed whole (`SubCover`); post: the claims back, `b` and its
   subtree some sub-forest of what they were, or `b` gone. Proof by Löb/strong induction over
   `model.removeAllFrom`'s recursion; reuse `RemoveAllFrom` (the dir case), `RemoveAllLeaf` (a file entry),
   `RemoveAllParts`, `RemoveAllAbsentN`. Note `specDirS` covers only one level of files. Expect 1-2 sessions.
2. `TouchDirAll` with a directory `.touch`: an `os.OpenFile` spec answering an error on a directory
   (check the fsExt semantics of open with `O_WRONLY|O_CREAT` on a directory first), then `fileutil.TouchDirAll`'s
   error arm; `Create` returns an error, nothing committed (the tester's `Boot` returns `StatusDown`).
3. `walAreaRes` without `TmpOk`, `tmpClTouch` accepting any entry; `Create`'s proof over 1-2
   (`CreateTmp.wp_removeAllTmp`). Then retire `hfo`/`BootFoNmTmp` and `TCrashed`'s fact; if cheap,
   `renameWALPost`'s dead arm 2 (`Create.lean` ~1185).

**Then step 3** (the tester onto `fsSQ_crash_adequacyShared`): the plan in the handoff two sections up; the
hard stop before the closed statement stands.

**Pitfalls (new).** `etc/lean-check.py` (with `LAKE_OPTS=--packages=/shared/tmp/manifest-d64.json`) works well
here: it rebuilds changed imports itself, a few seconds per WAL file; use `-a` and read the summary line (a
filter on `error:` alone hides `lake setup-file` failures of an import). `osNames_join`/`osCommitLb_zero` need
`[go.BasicIntoValInj]` in the section (`osNames_frac` and the inline `monoNatLbOwn_0` do not). `iunfold` takes
one name. Inside a `have h : P ⊢ Q := …` (or a `BigSepL.bigSepL_mono` element) the outer Iris context is gone:
put the persistent facts you need in `P`. `BI.or_false` and `_root_.or_false` are ambiguous once
`TmpClaim` is imported: write `_root_.or_false`.

# Handoff (branch `wal-safe`, 2026-11-22, session 5 of etcd-grove-03's delegates): (D)1 done; (D)2-3 need a decision

**State** (`c771b6bf06`, on `025b1929a6`): no axiom, no `sorry`; the WAL Link and the tester Link build (3590 jobs; `RemoveAll`'s shared helpers moved to the defs module `RemoveAllTop`, tiers clean). Checked with `etc/lean-check.py -a` (the os
files, `RemoveAllSub`, `RemoveAllCover`, and the WAL files that used `SubCover`: `CreateDefs`, `CreateFree`,
`CreateArea`).

**(D)1 done** (`fe1fc1817f`, `2999344fbd`):
- `Spec/os/RemoveAll.lean`: **`os.RemoveAll.specSubS`**: `d/b` holding anything (nothing, a file, a directory
  with any subtree), the whole claim on `b`, the whole claims `cl` of the directories under it (`osClaimsW cl`,
  `SubCover cl`) and **`ClRanked cl`** (a rank growing along the claims' directory entries: no cycle; the
  recursion needs it to know a directory below `J` is not `J`). Post: `∃ h' cl'`, the claims back,
  `EntsSub h'.cur h.cur` (`b` as it was or gone), `ClsSub cl' cl` (same claims in order, each holding some of
  what it held); the error `nil` or `fmtErrorOk`, saying nothing of which. `ClReach`/`SubCover` moved here
  from the WAL's `CreateDefs` (namespace `EtcdGrove`, names unchanged).
- Proof `Proof/os/RemoveAllSub.lean`: `os.model.wp_removeAllFrom_sub n` by induction on the number of claims
  (the directory case is `RemoveAllFrom.lean`'s passes with each name removed by the induction hypothesis on
  the pool `os.rmPool`, the claims but the directory's own); `os.RemoveAll.wp_proofSubS`. Pure facts in
  `Proof/os/RemoveAllCover.lean` (defs tier: `ClsSub.*`, `SubCover.of_sub` for clients, `subCover_pool`,
  `TreeWf.rank`/`ClRanked.of_tree`: a well-formed tree's directories ranked by depth, for the boot).
- `os.model.wp_rmdirLoop_dirSt` takes a guard of any path `pg` of the root (`hkg`).

**(D)2-3: the plan as written is incomplete; a cheaper design needs a premise (decision for the coordinator).**
Retiring `BootFoNmTmp` needs `Create` to cope with *any* `nm.tmp`: a directory with subdirectories, a
`.touch` that is a directory, **and `nm.tmp` a file** (the third part of `BootFoNmTmp`; the plan only named
the `.touch` arm). After `specSubS`, `nm.tmp` may still be anything: `RemoveAll` returns `nil` on a spurious
`ENOENT` with no effect, and `Exist` may miss it (a `Stat` error). Two designs:
- **(G) as planned**: make `TouchDirAll`/`CreateDirAll` cope with any leftover. New: ext no-effect lemmas
  (`open(O_CREAT|O_WRONLY)` of a directory: `OpenEffect` has no case, an error with no effect; `open` of a
  path under a file: `lookup` none and no parent; each ~50 lines over `wp_callEndS`, as
  `RemoveAllExt.wp_osRmdirS_nonempty`), `os.WriteFile` error arms (both), `os.MkdirAll` on a file,
  `IsDirWriteable` error arms, `TouchDirAll.specFile`, `TouchDirAll.specDir` and `CreateDirAll.specTmp`
  over a subtree pool (with `ReadDir` of a directory holding directories), then `Create`, `walAreaRes`
  (`TmpOk` out, `tmpClTouch` accepting a directory), the boot (`bootTmps`/`bootFiles_split` without
  `BootFo`'s `nm.tmp` parts). Estimate 3-4 sessions.
- **(FNE, recommended)**: `Create`'s `nm.tmp` exact under `FsNoErrOn` of three paths. Checked against
  `NoIoErr`/`PathErrno` (`Premises.lean`) and the model (`TrustedCode/os.lean`): with `dir.tmp` and its
  parent covered (and fitting), `Exist(dir.tmp)` is exact (`Stat`'s `Open` and `Fstat` succeed), and
  `RemoveAll(dir.tmp)` returns `nil` only with `dir.tmp` gone: every `nil` exit is an `unlink`/`rmdir` of
  `dir.tmp` itself answering 0 or `ENOENT` (`PathErrno`: absent), the parent's `open` (covered: succeeds),
  or a read of `dir.tmp` answering `ENOENT` (only for a removed directory). The entries **below** `dir.tmp`
  need no coverage (their removal is `specSubS`'s weak recursion; a failure there surfaces as `ENOTEMPTY`
  at `dir.tmp`'s covered `rmdir`, an error). So `CreateDirAll` only ever sees an absent `dir.tmp`
  (`CreateDirAll.spec`, proved), `specTmp`/`TmpOk`/`tmpClTouch`/`bootTmps` can go, and the error returns
  give `walAreaRes` back from `specSubS`'s weak post. New: `os.RemoveAll.specSubSNE` (`specSubS` plus
  `FsNoErrOn (· ∈ [child d b, d])`, post `err = nil → h'.cur !! b = none`; NE variants of the top-level
  loops: unlink, rmdir, open of the directory and the parent, the read), `Stat`/`fileutil.Exist` NE
  variants (`true` iff present). Estimate 2 sessions, and it removes code.
  **The premise**: `wal.Create.spec`/`specFresh` (exported results of the WAL Link) and the tester's
  `tWalFsOk` (premise of `Boot`/`Main`) widen `FsNoErrOn (· = dir)` to
  `FsNoErrOn (fun p => p = dir ∨ p = dir ++ ".tmp" ∨ p = filepath.Dir dir)`. At the closed theorem it is
  discharged as `tWalFsOk` already is (`fsNoErrOn_of` with the semantics' `allIo`, every path), so the closed
  statement gains no premise. Needs the coordinator's yes (a premise on an exported statement).
Either way the boot supplies `ClRanked` of the `nm.tmp` claims from `TreeWf` (`ClRanked.of_tree`), and
`walAreaRes` carries `SubCover` and `ClRanked` of each `nm.tmp`'s tagged claims in place of `TmpOk`.

**Then**: retire `tester_crash`'s `hfo` (`BootFoNmTmp`) and `TCrashed`'s carried fact; `renameWALPost`'s
arm 2 if cheap; step 3 (the wiring onto `fsSQ_crash_adequacyShared`, plan two handoffs up); the hard stop
before the closed statement stands.

**Pitfalls (new).** `ihave H := lemma $$ [Hs]` puts the side goal first (`H` is not in it): write
`ihave H : P $$ [Hs]` then `· iapply lemma; iframe`. `ihave HΦ' : … $$ [HΦ]` consumes `HΦ` (no `iclear`).
A Lean-level induction (on the claims' count) is simpler than `iloeb` for a recursion whose depth a datum
bounds: the hypothesis is a plain triple for `wp_apply`.
