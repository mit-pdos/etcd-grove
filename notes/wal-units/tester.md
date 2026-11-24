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

# Handoff (branch `wal-safe`, 2026-11-22, session 6 of etcd-grove-03's delegates): (FNE) decided; its `os` half done

**Decision (coordinator, 2026-11-22): design (FNE), not (G).** `wal.Create.spec`/`specFresh` and the tester's
`tWalFsOk` widen `FsNoErrOn (· = dir)` to `dir`, `dir.tmp` and the area `r` (= `filepath.Dir dir`: `InArea r
dir nm` gives `dir = child r nm`; writing `r` avoids a pure `filepath.Dir` in the statement). Discharged at the
closed theorem by `allIo` (`fsNoErrOn_of`), as `tWalFsOk` is now: no new closed premise. Then `TmpOk`,
`CreateDirAll.specTmp`, `tmpClTouch`, `bootTmps` go, and `BootFoNmTmp`/`hfo` and `TCrashed`'s carried fact retire.

**Done this session (the `os` half; no axiom, no `sorry`, no trusted file touched):**
- `GooseLang/Ext/Fs/WpPostShared.lean`: **`wp_fs_postSh`**, `wp_ext_postS` for a shared-mode call: a spec proved
  over any semantics gets a pure fact `Ψ` of its result from the semantics' own step (where `NoIoErr` lives),
  given a fact `QP` of the state the caller's resources read through the claims' authority (`osSharedInv`,
  opened for an instant). No step lemma has to be re-proved to witness an errno.
- `GooseLang/Ext/Fs/NoErrRemoveSteps.lean`: `FsNoErrAt p := FsNoErrOn (· = p) ∧ PathFits p`; `unlink_noErrAt`
  (file: 0; directory: `EISDIR`), `rmdir_noErrAt` (empty: 0; non-empty: `ENOTEMPTY`), `openDir_noErrAt`
  (read-only open of a directory: 0 or `EINTR`).
- `Proof/os/RemoveAllNE.lean`: `wp_osUnlinkSW`, `wp_osUnlinkS_noneW`, `wp_osRmdirS_nonemptyW`, `wp_osRmdirSGW`,
  `wp_osOpenDirSW` (each the existing spec with its errno witnessed under `FsNoErrAt`).
- `Proof/os/RemoveAllDir.lean`: `os.rmAllOutP … P` (`rmAllOut` whose first arm, `b` still there, also says `P`);
  W variants `wp_unlinkLoop_dirStW`, `wp_rmdirLoop_dirStW`, `wp_openLoop_dirStW`, `wp_openLoop_spineW` (an open on
  a spine never answers `ENOENT`: no premise), the old names restated over them; `wp_unlinkLoop_nofile`'s post
  and `RemoveAllLeaf`'s `wp_unlinkLoop_leaf`/`wp_removeAllFrom_leaf` posts gain the witness in place.
- `Proof/os/RemoveAllParts.lean`: `wp_pathErrorPtrN`/`_errnoN`/`_rdN` (the error pointer non-null).
- **`os.RemoveAll.specSubS`'s post gains `err = interface.nil → FsNoErrAt (child d b) → FsNoErrAt d →
  h'.cur !! b = none`** (`Spec/os/RemoveAll.lean`, proved in `RemoveAllSub.lean`: `rmSubOut … G`, `rmSubOut_ofP`;
  every `nil` exit refuted or `b` gone; the directory read's `ENOENT` refuted with `wp_osDirReadNextGenS'`, the
  directory being on a spine).
- `GooseLang/Ext/Fs/FstatAny.lean`: `wp_osFstatAny`/`wp_osFstatAnyW` (no `OsMeta`; errno 0 under `FsNoErrIno`).
- `Proof/os/StatNE.lean`: **`os.Stat.wp_dirSW`, `os.Stat.wp_fileAnySW`**: an error only when `¬ FsNoErrAt path`
  (the file case needs no `OsMeta`, so `walAreaRes` need not hold a leftover `nm.tmp` file). With
  `fileutil.Exist.spec` (`b = decide (err = nil)`): `Exist(dir.tmp)` of something there answers `true`.
- Built: `Proof.os.RemoveAllSub`, `RemoveAll`, `RemoveAllAbsentN`, `StatNE` (and the WAL/tester Links, see the log).

**Next: the WAL half** (no further `os` work expected):
1. `CreateTmp.lean`: replace `tmpDirH` by a general `tmpAny jr b h := ∃ cl, osNames jr [b] 1 h ∗ osClaimsW cl ∗
   ⌜SubCover cl (h.cur !! b) ∧ ClRanked cl⌝` (`tmpDirH ⊢ ∃ h, tmpAny`: `cl := [(J, except [], hJ)]`, rank `J ↦ 0`,
   dropping the `.touch` file). `wp_existTmpNE`: cases `none` (`Stat.wp_absentS`), `file` (`wp_fileAnySW`),
   `dir` (borrow the spine as `wp_existTmp` does, `wp_dirSW`); post `x = false → FsNoErrAt (child r b) → h.cur !!
   b = none`. `wp_removeAllTmp` over `specSubS` (post `tmpAny` again, and `err = nil → … → none`).
2. `Create.lean` (`wal.Create.wp_proof`, ~line 540-760, the error arms at ~95, 174, 212, 253, 415, 618, 709, 1313,
   1352): `Exist(tmp)` false ⇒ absent ⇒ `CreateDirAll.spec` (proved, absent name) in place of `specTmp`;
   `RemoveAll` nil ⇒ absent ⇒ the same; error arms through `tmpAny` + `specSubS`. Premise: `FsNoErrOn (fun p => p = dir
   ∨ p = dir ++ ".tmp" ∨ p = r)`; `FsNoErrAt r` needs `PathFits r` from `PathFits dir` (a prefix: add the lemma in
   `PathFitsLemmas.lean` if none). Drop `wp_CDA`/`wp_RmDir` hypotheses (`etc/gen-link.py --walfs` then drops
   `CreateDirAll.specTmp` from the Link; delete `CreateDirAllTmp.lean` and, if unused, `TouchDirAll.specDir`).
3. `walAreaRes` (`CreateDefs.lean`): `TmpOk` conjunct → `∀ nm, walNameOk nm → ClRanked (clOf cl (tmpName nm))`;
   `areaCls` without `tmpClTouch`. Users: `CreateArea` (`area_takeTmp` gives `tmpAny`; `create_abortTmp` in
   `CreateAbort.lean`/`CreateUnmint.lean` takes it back: `SubCover.of_sub`, `ClRanked.of_sub`), `CreateFree`,
   `CreateAreaBack`, `CreateCleanup`, `openAtIndexLemmas`, `Boot0` (nothing at `nm.tmp`), `BootCrash*` (ClRanked
   from `TreeWf`: `ClRanked.of_tree`; `bootTmps`/`tmpClTouch`/`bootFiles_split`'s tmp part go), `Crash.lean`.
4. Tester: `tWalFsOk` widened (`RestartOk.lean`; `Boot`/`Main` specs); `tester_crash`'s `hfo`, `BootFoNmTmp`,
   `TCrashed`'s carried fact removed (`WalTester/.../Crash.lean`, `BootCrash.lean`). Regenerate both Links.
5. Ledger: `notes/specs-only/ledger.md` entry for `wal.Create.spec`'s widened premise and `CreateDirAll.specTmp`'s
   removal (not written yet: write it before editing the spec, per CLAUDE.md).
Then step 3 (the tester onto `fsSQ_crash_adequacyShared`) and the hard stop before the closed statement, as before.

**Pitfalls (new).** `rw (occs := .pos [n])` counts occurrences in the whole Iris entailment, context included:
a hypothesis whose type gains the pattern (here `HΦ'` mentioning `null`) shifts the index. An `iloeb` IH lists
the context in the order it had at the `iloeb`; a lemma that returns a resource (`wp_osDirReadNextGenS'`'s `P`)
moves it in the context, so the IH call's argument order changes. In a term, `⟨fun h => by cases h, x⟩` parses
`, x` into the tactic block: parenthesize the `fun`. Without `simp only [IsFsStep] at h`, `rcases` cannot split an
`IsFsStep "Open"`'s `let` body; with it, the main arm has ten components.

# Handoff (branch `wal-safe`, 2026-11-22, session 7 of etcd-grove-03's delegates): (FNE)'s WAL half done; step 3 done short of the closed theorem

**State** (`b94796513b` and this note): no axiom, no `sorry` added. Built green through the build slot: the WAL Link, the
tester Link and `InitLinked`, `storage.WalAreaFresh`, `etcdserver.RnNewStorageLinked`, `etcdstart.WalAreasInit`
(4479 jobs), then the new `Adequacy` module (3618 jobs). `etc/tier-check.py --check` ok.

**(FNE)'s WAL half** (`57d9a044f0`):
- `CreateCallees.lean`: `tmpCls e := ∃ ct, osClaimsW ct ∗ ⌜SubCover ct e ∧ ClRanked ct⌝`, `tmpAny j b h := osNames j [b] 1 h ∗
  tmpCls (h.cur !! b)`; `CreateDirAll.specTmp` deleted (with `CreateDirAllTmp.lean`, `TouchDirAllDir.lean` spec and proof).
- `CreateTmp.lean`: `wp_existTmpNE` (`false → FsNoErrAt (child d b) → absent`; over `wp_statDirW_err`/`wp_statFileW_err`,
  `Stat`'s W specs with the `FileInfo` dropped: `Exist.spec`'s `Q` takes only the error, a post mentioning `fi` makes the
  unifier time out), `wp_removeAllTmp` over `specSubS` (`nil → FsNoErrAt (child d b) → FsNoErrAt d → absent`).
- `Create.lean`: `hFt`/`hFr` from the widened premise (`pathFits_area`, `CreatePure.lean`); `CreateDirAll.spec` (proved) on
  the absent `nm.tmp`; every `tmpDirH` exit converted (`tmpDirH_any`, `CreateArea.lean`). Hypotheses `wp_RmSub`, `wp_CDA :
  CreateDirAll.spec` replace `wp_RmDir`, `specTmp`.
- `CreateDefs`/`CreateFree`/`CreateArea`: `areaCls` is the claims only; last conjunct `∀ nm, walNameOk nm → ClRanked (clOf cl
  (tmpName nm))`; `area_takeTmp`/`area_give` over `tmpCls`; `osClaimsW_eq`, `tmpCls_none`, `tmpDirH_any`.
- Boot: `BootFo` = the WAL directories' files-only part; `BootFoRest` = the pipeline names' part; `bootCls_ranked` (from
  `TreeWf`, `ClRanked.of_tree`); `bootFiles_split` drops the `nm.tmp` probes (affine); `bootTmps`, `bootCls_touch`,
  `bootCls_tmpOk` gone. Tester: `BootFoNmTmp` and `tester_crash`'s `hfo` gone; `TCrashed` still carries `BootFo`, now
  produced from `walInv_crash` alone (`bootFo_of hfoX hfoT`), so nothing is carried from outside.
- Not done (optional): `renameWALPost`'s dead arm 2. `Proof/os/MkdirAllDir.lean` (`os.MkdirAll.specDirS`) is now reached
  by no Link (it was `TouchDirAll.specDir`'s callee): leave or delete in a cleanup.

**Step 3** (`82c8eaa536`, `b94796513b`): `WalTester/Proof/.../etcd/wal/Adequacy.lean` (linking tier):
- the semantics `tExtsSem := fsExtsSemanticsWithS tSQ tQ` (`tSQ` = `etcdSQ`: no I/O, lock or map error on any file or path;
  `tQ := W1 walCodec`) with local instances `tFsSemOk`, `tHasFs`, `tSat`, `tSatL`; `tWalFsOk_of` (from `PathFits` only);
- `bootWal area orDir` (`initialize'`, then `Main`), `tFirst`, `tGenPre`;
- `tGen_wp`: one generation (osShared → `tBoot0`/`tBootCrash` → `TBoot_run`; WP: `Hinit_wp`, `Main.spec`; crash frame
  `tester_crash`);
- `TOpen` (the open specs) and `tMain_linked` (Link's `wp_Main` at `walRaftP`/`walRaftU`/`walRaftHsO`: `walPb_laws`,
  `walRaftP_marshalHs`, `walRaftHsO_own`);
- **`etcd_wal_crash_safety_bounded`** (hypotheses `Hinit_wp`, `Hopen`, stated at `tHeapAt hG lctx`).

**New blocker B-4 (decision needed):** the tester's initializer registers the WAL's prometheus metrics, so
`wp_initialize'` needs `prometheus.namesFree initNames`, handed out only by `goose_adequacy_start` (crash-free, a trust
boundary in `Proof/runtime/Start.lean`). The crash adequacy gives a generation `ownGoState ∅` only. Options: a crash variant
of the start axiom (every generation is a fresh process with an empty registry), or `Hinit_wp` kept as a stated premise
(as `seglog_crash_safety` and `bootCrashSafety` do).

**The proposed `etcd_wal_safe` statement**, with every premise, hypothesis and axiom: `/shared/tmp/coord-03/walsafe-log.md`,
"PROPOSED closed statement `etcd_wal_safe`". Hard stop: not stated in Lean.

**Pitfalls (new).** A Hoare-triple hypothesis whose post must unify with a callee spec's `Q err` (`Exist.spec`) cannot
mention the result's other components (`fi`): wrap the spec first. A closed theorem's per-`hG` hypotheses need the
program's Go local context (`tHeapAt hG lctx`, as bboltfs's `heapAt`), or `go.Semantics` is not found under `∀ [hG]`.
`iframe` against a goal whose resource differs only by a rewritable index (`tmpCls none` vs `tmpCls (h.cur !! b)`) times
out: `rw` first.

# Handoff (branch `wal-safe`, 2026-11-22, session 8 of etcd-grove-03's delegates): (i) two gaps closed; (a) needs a decision

**State** (`0e40aff935`, `28815a48a1`, this note): no axiom, no `sorry` added. Built green through the build slot: `Adequacy`,
`RnNewStorageLinked`, `WalAreaFresh`, `WalAreasInit` (4381 jobs); `etc/tier-check.py --check` ok.

**(i) The library gaps of `TOpen`, one by one.**
- `fmt.SprintfBroken.spec`: **proved** (`Proof/fmt/SprintfBroken.lean`, over Perennial's `SprintfOut.strV`, fmtmodel
  `79517dbdf`, already at the pin). Gone from `TOpen` and the Links.
- `filepathlite.IsAbs.spec`: **proved** (`Proof/internal/filepathlite/IsAbs.lean`) over its callee
  `stringslite.HasPrefix.spec` (`Spec/internal/stringslite/HasPrefix.lean`, Perennial's statement), which replaces it in
  `TOpen` (`hasPrefix`). Perennial change: branch `stringslite-hasprefix` (`d508df6ff`, off `lean` `04ed1c622`, worktree
  `/shared/perennial-stringslite-hasprefix`, NOT pushed): `HasPrefix` translated with its body (go1.26.3's source, as the
  committed `HasSuffix`; go1.27's moves `TrimSuffix`'s line comment), `internal.stringslite.HasPrefix.{spec,wp_proof}`,
  linked; builds. Once the pin reaches it: delete the local spec file, import Perennial's spec (the statement is the
  same, `EtcdGrove.stringslite.HasPrefix.spec` → `internal.stringslite.HasPrefix.spec`), regenerate the Links.
- `errors.{IsErrno, IsPathErrnoEof, IsPathErrnoNotExist, IsPathErrnoTerm}.spec` and `WalDecEnvSupply`: **blocked on
  Perennial**: all five need Perennial branch `errors-facts` (drafted 2026-11-14 off `ddc0f0acc`, pushed, pending the
  user's review, not landed): `58e04c5c0` (`newVar` keeps the `errorString`'s field, so `io.EOF`, `io.ErrUnexpectedEOF`,
  `walpb.ErrCRCMismatch`, `oserror`'s errors are provably distinct; `errors`' fact records `ErrUnsupported`, which
  `Errno.Is`'s `switch` loads) and, for `IsErrno`, `601b7fb5d` (`errors.Is.spec` at a comparable non-pointer target). Its
  third commit `7533cf64a` (`errors.As`) is #26's (upamanyus) territory: leave it out of any rebase. Here, after that:
  translate `syscall.Errno.Is` and `io/fs.(*PathError).Unwrap` (this repository's `Code/syscall.toml`, `Code/io/fs.toml`)
  and prove the four over `errors.Is.spec`'s two-error tree. Not started (a rebase of `errors-facts` onto `lean` and a
  full Perennial rebuild: errors is imported by almost everything).
- `fmt.ErrorfErrsNot.spec`, `fmt.ErrorfErrsTerm.spec`: **a spec decision**. Perennial's `Errorf` now wraps (`errorfErr`:
  a fresh `*wrapError`/`*wrapErrors`/`*errorString`), but (1) the arguments' facts `errIsNot e t`/`errIsTerm e` are opaque
  triples of `errors.Is(e, _)`, and `errors.Is` of the wrapper walks the child inside its own loop (`is`'s `for`, or a
  call of `is`, never of `Is`), so a triple of `Is(child, _)` cannot be used: the premises would have to be error trees
  (`errorWalkTree`) instead; (2) `errIsNot`'s `err ≠ t` in the no-`%w` case (`*errorString` result, `t` = `io.EOF` of the
  same type) needs freshness, and `errorfErr` gives only `l.[…] ↦□ s` (persistent, no disjointness from `t`'s pointer).
  So: restate `errIsNot`/`errIsTerm` (and the WAL decoder's 25 uses) over trees, and get freshness (an owned points-to or
  the `newVar` field of `t` with a distinct message) — ledger first; not done.
- `time.Time.Format.specBroken`: **a model or an axiom decision**. Perennial's `time` has no `Format` (names-only), and
  this repository's trust-boundary `time.Time.Format.spec` says nothing of the result. A proof needs `appendFormat`
  translated (with `Time`'s date arithmetic) or a Perennial model of `Format` for numeric layouts; otherwise a
  strengthened trust-boundary axiom, which needs the user. Hypothesis kept.
- `io.CopyFiles.spec`: **provable now, not started** (no Perennial change: `io.Copy`/`copyBuffer` have bodies at the pin
  `d648cfe22`; this repository's `os` translates `File.ReadFrom`/`WriteTo`, `genericReadFrom`/`genericWriteTo`, and
  `copy_file_range` is modelled). The proof is the "io.Copy log" path (`notes/wal-fsext-plan.md`): `copyBuffer`'s
  `WriterTo` assertion on the `*LockedFile` → `File.WriteTo` → `genericWriteTo` → `io.Copy` again → the `*os.File`
  destination's `ReadFrom` → `copy_file_range` rounds, then `genericReadFrom`'s 32 KiB loop; each needs a spec over
  `trFile`/the source's stream. One to two sessions. Touches no Perennial file (so no overlap with `stdlib-leaves`).

**(a) B-4: the crash variant of `goose_adequacy_start`, NOT added: unsound as asked.** The plan was: each generation's WP
(`goose_crash_adequacy_acc`'s `Hstart` and every crash frame's next generation) also receives `prometheus.namesFree Ns`.
But `prometheus.nameFree n : IProp GF` (`Registry.lean`) is not indexed by the generation, and a generation's crash frame
`∀ L', crashed -∗ … ={⊤}=∗ P L'` is a wand that can capture any resource of the generation (or `▷` of one, out of an
invariant). So a proof can keep generation 1's unused `nameFree n` in `P`, and generation 2 then holds it **and** the
fresh copy: two `MustRegister(n)` in generation 2 are provable, the second panics in Go. A concrete shape: a program that
on first boot writes a marker and registers nothing, and on a later boot (the marker present) registers `n` twice; the
proof gives generation 1's right to its crash frame. This is D19a's double-use hazard, across a crash. No axiom that
hands out the unindexed `nameFree` per generation avoids it (restricting the crash frame does not help: an invariant
allocated before the rights are given can carry them). Sound options, for the user:
1. **Index the rights by the generation**: `nameFree` (and `namesFree`, `startRights`) take the generation's
   `[CrashGS GF]` (an instance under every `[HeapGS]`, so most of the ~115 files using it are unchanged in source;
   `MustRegister.spec` consumes the current generation's right). Then the crash axiom gives `namesFree (hC := L'.crashGS)
   Ns` to each generation, and a leftover from generation `k` is a different predicate in generation `k+1` (the crash
   names are fresh per generation in Perennial's crash adequacy, as `ownGoState`'s are). Smallest sound change;
   rebuilds ~1150 modules (everything above `Registry.lean`), and touches the shared trust-boundary predicate.
2. **Receipts**: `MustRegister.spec`'s post gives a generation-indexed `registered n`, and the crash axiom turns
   `registered n ∗ crashed` of the dead generation back into `nameFree n`. Conservation holds per name, but it changes
   `MustRegister`'s axiom and the tester must thread the receipts from the initializer to its crash frame.
3. Keep `Hinit_wp` as a premise of the closed theorem (option (b), as `seglog_crash_safety`): rejected by the user, listed
   for completeness. `Hinit_wp` stays a hypothesis of `etcd_wal_crash_safety_bounded` until the decision.
No `notes/axiom-review/` entry was written (no axiom added); the analysis above is what it would start from.

**What `TOpen` holds now**: `decEnv` (`WalDecEnvSupply`), `cloneHs`/`unmarshalHs`/`resetHs` (under review, untouched),
`isErrno`, `isPathErrnoEof`, `isPathErrnoNotExist`, `isPathErrnoTerm`, `hasPrefix` (new leaf, was `isAbs`),
`errorfErrsNot`, `errorfErrsTerm`, `copyFiles`, `unmarshalWalRecordE` (under review, untouched), `formatBroken`.

**Pitfalls (new).** A proof file's section `variable [GoSemanticsFunctions]` (for a pure lemma) is copied by
`gen-link.py --walfs` into the Link's sections: put such instances in the lemma's own binders. Regenerating a Perennial
stdlib translation: run goose with the toolchain the committed output came from (go1.26.x for `internal/stringslite`;
`PATH=/root/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.26.3.linux-amd64/bin`, `GOTOOLCHAIN=local`), and build goose
into a private `GOBIN` (not `/root/go/bin`, which other sessions use). A Perennial worktree builds standalone with the
d648 worktree's `.lake/build` copied in and `.lake/packages/{iris,batteries,Qq}` symlinked to this worktree's.

# Handoff (branch `wal-safe`, 2026-11-22, session 9 of etcd-grove-03's delegates): the hard-state laws proved; `io.CopyFiles` begun

**State** (head after this note's commit): no axiom and no `sorry` added. Built green through the build slot:
the WAL `Link` and the tester's `Adequacy` (3622 jobs, after every change below), plus `Proof.io.CopyRound`.
`etc/tier-check.py --check`, `gen-init --check`, `gen-raft-tla --check` and `copy-part --check` pass.

**Gone from `TOpen`:** `cloneHs` and `unmarshalHs` (`3d9c18c0b6`). The new module is
`Proof/.../wal/RaftModel/LawsHsPb.lean`:
- `walRaftP_cloneHs` proves `WalPbIn.CloneHsLaw walRaftP` from the trusted `proto.ClonePb.spec` at `pbHsC`.
  `c' = c` holds because every hard state marshals. `hsOwnC_freeze` is the general-content form of
  `walRaftHsO_freeze`.
- The law is **narrowed to a non-nil source**, as the reviewer suggested (ledger 2026-11-22): `CloneHsLaw`
  takes `p ≠ null`, and `WalHsOwn` gains `notNull`. `ReadAll` reads it before freezing `state`, which is never nil.
- `walRaftHsO_unmarshal` proves `WalHsOwn.unmarshal` from `MustUnmarshalState`'s body and the trusted
  `proto.UnmarshalPb.spec` at `pbHsC`. **Deviation from the brief:** it does not go through
  `pbutil.MustUnmarshalMessagePb.spec`, because that spec module imports `etcdserver/apply` (about 390 more
  modules in the WAL's cone). It mirrors the entries' `wp_MustUnmarshalMessage_ent`. The trust is the same,
  since `MustUnmarshalMessagePb.wp_proof` is itself proved from `UnmarshalPb`.
- `walRaftHsO_own` now takes `proto.UnmarshalPb.spec` and the `reset` law. `Adequacy` passes
  `proto.ClonePb.wp_proof` and `proto.UnmarshalPb.wp_proof`, axioms the theorem already reached.

**`io.CopyFiles.spec`: still a hypothesis.** No Perennial change was needed. Four prerequisites are landed on
`wal-safe`:
1. `5ecf7c90c6`: `Code/os.toml` translates the promoted `fileWithoutWriteTo.Read`/`SyscallConn` and
   `fileWithoutReadFrom.Write`. Without their `MethodUnfold`s, `genericReadFrom`'s loop and `spliceToFile`'s
   `getPollFDAndNetwork(fileWithoutWriteTo{f})` could not step. `Code/os.lean` was regenerated
   (18 lines added; this touches the `Code.os` cone).
2. `b3cd28644c`: package facts. `os` records `checkWrapErr ↦□ false`, read by `(*File).wrapErr` of a non-nil,
   non-EOF error (`os.checkWrapErr_of_pkgInit`). `internal/poll` records `ErrFileClosing ↦□ e`, which
   `wrapErr` compares with (`internal.poll.errFileClosing_of_pkgInit`). These live in `etc/gen-init.py`'s
   SPECIAL, and every part's `Init` was regenerated.
3. `bb99dff6fc`/`0ac4a5fde7`: **spec fix (ledger 2026-11-22).** `m.size < 2^62` became `< 2^61`. A source in
   `[2^62 - 2^31, 2^62)` makes `model.copyFileRangeRound` panic, since `offMax ≤ soff + max` with
   `max = 0x7ffff000`. `Repair` supplies the new bound from `Fs.maxBytes`.
4. `a8387c413c`/`9c2bc0ad91`: proved lemmas:
   - `Proof/io/CopyDefs.lean`: `io.cpOk` (the destination's `OsMeta` shape), `cpOk_pwPost` (a pwrite at the
     end), `pwBytes_end_vals/len`, and `copyDst_intro/elim/mono/after`.
   - `Proof/io/CopyRound.lean`: **`os.wp_cfrRound`**. One round over a destination `io.copyDst … (· = vs)`
     at offset `|vs|` writes the source's next `k` bytes. It gives `k > 0` only with errno 0,
     `k = 0 ∧ errno 0` only at the source's end, and `soff + k ≤ |bs|`.

**In progress, outside the tree:** `/shared/tmp/coord-03/walsafe-wip/CopyPoll.lean` holds
`os.wp_pollCFR`, the `model.pollCopyFileRange` loop. It ends in `io.cpG` (the copy's state at some `j'`),
handled-with-nil only at the end. Proved so far:
- the outer Löb (`iloeb` after 7 `wp_pure`; the written value is generalized with
  `conv in (occs := 9)`, which is fragile);
- the EINTR inner Löb (`IH2`, after the first `wp_auto` into the round);
- the `k > 0` branch: `handleCopyFileRangeErr` stepped with `wp_func_call; wp_call` once its name is
  rewritten to `internal.poll.handleCopyFileRangeErr` and `[internal.poll.Assumptions]` is in scope, then `IH`.

Remaining there, the `k = 0` exit:
- errno 0: `handle` gives `(written ≠ 0, nil)`, and the source is at its end (`hk2`).
- errno ≠ 0: `handle` gives `(false, nil)` for ENOSYS/EXDEV/EINVAL/EIO/EOPNOTSUPP/EPERM, else `(true, Errno e)`.
- Then the `lr` test (`null`) and `os.wrapSyscallError` (translated: a type assertion to `syscall.Errno`, then
  `NewSyscallError`), which is nil exactly for a nil error.

**Then, in order** (≈ 1–2 sessions; `notes/wal-fsext-plan.md`, "io.Copy log", has the Go path):
1. `File.copyFileRange` on `fileWithoutWriteTo{f}`: `tryLimitedReader` (`*LimitedReader` fails, remain `2^63-1`),
   the two assertions, `checkValid`, then `wp_pollCFR`.
2. `spliceToFile`: `getPollFDAndNetwork` reaches the promoted `SyscallConn`, `File.SyscallConn`, `newRawConn`,
   then the assertion to the `{Network, PollFD}` interface, which fails. Result: `(0, false, nil)`.
3. `readFrom`.
4. `File.wrapErr`: nil/EOF are returned as is; otherwise the `ErrFileClosing` comparison, `checkWrapErr = false`,
   and a `&PathError`.
5. The fallback, `genericReadFrom`, which is `copyBuffer`'s 32 KiB loop. It reads with `os.File.Read.wp_eof` (the
   source's bytes from 0, any fraction) and writes with `os.File.Write.wp_long`/`wp_empty` (so the proof takes
   `os.File.WriteAt.specLong`). It needs a lemma turning `Write`'s success post (`pwPost`, `PwOut` with `xs = []`)
   into `io.copyDst_after`'s shape, and its error post (`pwPostE`/`PwOutA`) into `io.copyDst … (fun _ => True)`.
6. `File.ReadFrom`, `File.writeTo` (the `*File` destination's `SyscallConn`; `rawConn` is no `PollFD`, so not
   handled), `File.WriteTo`, `genericWriteTo`.
7. `io.Copy`/`copyBuffer` twice: the `*LockedFile` source's `WriterTo` (promoted, `ptr_WriteTo_unfold`), then
   `fileWithoutWriteTo`'s missing `WriterTo` and the `*File` destination's `ReaderFrom`.
8. `theorem io.CopyFiles.wp_proof (wp_WriteAt : os.File.WriteAt.specLong) : io.CopyFiles.spec` in
   `Proof/io/CopyFiles.lean`. Then regenerate the Links (`etc/gen-link.py --walfs`/`--wal-tester`, output
   redirected) and drop `copyFiles` from `TOpen`.

**`TOpen` now holds:** `decEnv`, `resetHs`, `isErrno`, `isPathErrnoEof`, `isPathErrnoNotExist`,
`isPathErrnoTerm`, `hasPrefix`, `errorfErrsNot`, `errorfErrsTerm`, `copyFiles`, `unmarshalWalRecordE`,
`formatBroken`. `Hinit_wp` is unchanged (B-4's decision).

**Pitfalls (new).**
- `etc/lean-check.py` needs `LAKE_OPTS=--packages=/shared/tmp/manifest-d64.json` once an imported file has
  changed. Otherwise `lake setup-file` fails with "manifest out of date".
- `wp_start` unrolls a model's first `rec:` iteration, which breaks a Löb setup. Instead, `iintro` the triple,
  `unfold` the model, `wp_pure` up to the loop, and generalize its arguments (see `CopyPoll.lean`).
- The `W64 (o + j)` casts elaborate as `W64 (↑o + ↑j)`. Use `push_cast` on the helper facts
  (`os.cfr_natZ`, `os.cfr_W64_addI`), not `rw` with `W64 ↑(o + j)`.
- `word` inside a proof whose context has many `sint.Z` facts gave a kernel "application type mismatch". The
  arithmetic goes in standalone lemmas (`os.cfr_sumZ`, …).

# Handoff (branch `wal-safe`, 2026-11-22, session 10 of etcd-grove-03's delegates): `io.CopyFiles.spec` proved

**State:** no axiom and no `sorry` added. `copyFiles` is gone from `TOpen` and from the WAL and tester Links'
hypotheses (`etc/gen-link.py --walfs`/`--wal-tester` regenerated: the WAL Link has `io.wp_CopyFiles`, from
`io.CopyFiles.wp_proof` and `os.File.wp_WriteAtLong`). `Hinit_wp` and the other `TOpen` fields are unchanged.

**The proof** (`Proof/io/`, all defs-tier lemmas but the last):
- `CopyPoll.lean`, `os.wp_pollCFR`: `model.pollCopyFileRange`'s loop, now finished (the no-progress exit:
  errno 0, `handleCopyFileRangeErr`'s six unhandled errnos, any other errno wrapped by `wrapSyscallError` into a
  `*SyscallError`). Its post also says the error is `nil` or a `*SyscallError`. The fragile
  `conv in (occs := 9)` is gone: the proof stops one `wp_pure` earlier, `wp_bind`s the loop's application and
  names its two arguments with the lemma `os.wp_genArgs2`.
- `CopyGeneric.lean`, `io.wp_copyGeneric`: `genericReadFrom`'s `io.Copy(fileWithoutReadFrom{bf},
  fileWithoutWriteTo{f})`, `copyBuffer`'s 32 KiB loop over `os.File.Read.wp_eof` and `os.File.Write.wp_long`.
  The copy's state over the `*File`s is `io.cpS` (at `j`), its end `io.cpFin` (the spec's post); `io.copyDst_open`
  and `io.copyDst_wrote` carry the destination through a write at its end (success and failure,
  `io.cpOk_pwPostE`).
- `CopyFrom.lean`, `os.wp_ReadFrom_cp`: `bf.ReadFrom(fileWithoutWriteTo{f})`: `checkValid`, the trusted
  `readFrom`/`copyFileRange` (`tryLimitedReader`, the type switch, `wp_pollCFR`), then either `wrapErr` (handled)
  or `spliceToFile` (`getPollFDAndNetwork`: the source's `rawConn` has no `PollFD`) and `io.wp_copyGeneric`.
- `CopyFiles.lean`, `io.CopyFiles.wp_proof (wp_WriteAt : os.File.WriteAt.specLong)`: the `*LockedFile`'s promoted
  `WriteTo`, `File.writeTo` (`bf`'s `rawConn`: no `sendfile`), `genericWriteTo`, `copyBuffer`'s `ReaderFrom`
  branch, `os.wp_ReadFrom_cp` at `j = 0` (the `O_TRUNC` destination is `io.copyDst (· = [])`, `io.trFile_copyDst`).

**A package fact strengthened** (`etc/gen-init.py`, `Proof/internal/poll/PkgInit.lean`; Init files of every part
and RaftTla's copies regenerated): `internal/poll`'s `ErrFileClosing` holds an `*errorString` (its translated
`errors.New`), not just some error. `wrapErr` compares the `*SyscallError` with it; with an unknown interface of
the same pointer type the comparison has no step (`GoOp GoEquals` on pointers needs two locations).

**Interface type assertions:** `go_type_set` (Perennial's `TypeSet.lean`) decides `go.typeSetContains` from the
method sets; `simp only [h, ↓reduceIte]` then lets `wp_auto` go on.

**Pitfalls (new).**
- `etc/lean-check.py` without `-a` can report errors of an earlier version of the file (and goals of the
  wrong state): check with `-a` before trusting an error or a goal.
- A `local macro` that names an Iris hypothesis must take it as an argument of category `pmTerm`
  (`iapply $h`): hygiene renames a literal `HΦ`.
- `⌜a' = a⌝ -∗ …` inside a Lean `∀` of a lemma statement elaborates as a `Prop` entailment; write
  `∀ a' : T, ∀ b' : T, ⌜…⌝ -∗ …` (one binder per `∀`, as `wa_wp_call1_gen`).
- `(by cases h, x)` inside an anonymous constructor: the tactic block swallows the comma; parenthesize.
- `iframe` does not look inside `"name" ∷ P`: `unfold named` first.

**Next:** the remaining `TOpen` fields and `Hinit_wp` wait on the user's decisions (sessions 8-9 above).

# Handoff (branch `wal-safe`, 2026-11-22, session 11 of etcd-grove-03's delegates): Reset, Format, the Errorf specs; `errors-facts-2`

The user approved four items; done in order (Reset), (4), (3), (2).

**(Reset) `WalHsOwn.reset` proved** (`bd7593e7a9`). `(*raftpb.HardState).Reset` is **trusted code** now:
`Code/go_etcd_io/raft/v3/raftpb.toml` lists `HardState.Reset`, and `TrustedCode/go_etcd_io/raft/v3/raftpb.lean`'s
`HardState.Reset.impl` stores the zero value (as `walpb`'s `Record.Reset.impl`; the message-state store left out,
the docstring says why; the model's `state` is zero where Go's is not, harmless since `hsOwnC` quantifies it).
`walRaftHsO_reset` (`RaftModel/LawsHs.lean`) proves the law; `walRaftHsO_own` no longer takes it; `resetHs` is out of
`TOpen`. `Code/go_etcd_io/raft/v3/raftpb.lean` regenerated (`ptr_Reset_unfold`): this touches the main raft cone (every
importer of raftpb), so a landing rebuilds raft, the server and the examples. The reviewer's report is kept as
`notes/axiom-review/hsown-reset.md` (with a follow-up section).

**(4) `time.Time.Format.specBroken` is a trust-boundary axiom** (`e2225cfac4`). What the WAL uses: one call site
(`cleanupWAL`, wal.go: `fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format("20060102.150405.999999"))`), and of the
result only `brokenName_nameOk` (no `/`, no NUL). The spec's post was weakened to exactly that (`timeStampOk s :=
47 ∉ s ∧ 0 ∉ s`, `cleanupLaw`'s premise follows; `timeStampChars` deleted; ledger 2026-11-22), and the axiom is

    axiom time.Time.Format.wp_proofBroken : time.Time.Format.specBroken (GF := GF) (hG := hG)
    -- ∀ t, {{ True }} t.Format("20060102.150405.999999") {{ (s : GoString), RET #s; ⌜timeStampOk s⌝ }}

in `Proof/time/Time__FormatBroken.lean`. Baselines edited **by hand** (`etc/tcb-baseline.txt`,
`etc/tcb-collections/wal-fsext.txt`): no `etc/tcb-report.py` run this session; rerun `--check` after the next full
build. The `axiom` skill (run by its author): **survives** (`notes/axiom-review/time-format-broken.md`, Go tests and
log beside it; `notes/audit.md` row added).

**(3) `fmt.ErrorfErrsNot`/`ErrorfErrsTerm` restated over error trees and proved** (`68e9aadaa7`). Ledger first
(2026-11-22). `Spec/errors/ErrTree.lean`: `errTreeNot e t` (an `errorIsTree S M t` holding `e`, no node `t`, no `Is`
answering true, `TreeTyped`), `errTreeTerm e` (such a tree at every pointer target); `Proof/errors/ErrTree.lean`:
`errIsNot_of_tree`/`errIsTerm_of_tree` (to the old triples, over Perennial's `errors.wp_Is_tree`), the leaf
`*errorString` (`errTreeNot_errorString`, `errTreeTerm_errorString`) and the `*fmt.wrapError` step
(`errTreeNot_wrapError`, `errTreeTerm_wrapError`: `Unwrap` returns the `err` field, no `Is`). Narrowed to the WAL's
calls: `ErrorfErrsNot` exactly one `%w` of an error argument (`fmt.wrapsErr`) and a target that is no
`*fmt.wrapError` (so `err ≠ t` by type, **no freshness needed**); `ErrorfErrsTerm` at most one (`fmt.wrapsAtMostOne`).
What freshness would be needed for the no-`%w` case of `Not`: Perennial's `fmt.errorfErr` gives only
`l.[errorString, "s"] ↦□ s` (persistent), nothing that separates `l` from the target's pointer; an owned (or
`↦{1}`-then-frozen) cell would. Both proofs: `Proof/fmt/ErrorfErrsNot.lean`, `Proof/fmt/ErrorfErrsTerm.lean`, over
`fmt.wp_Errorf` (the argument lemmas moved to `Proof/fmt/ErrorfArgs.lean`). Restated with them (callers updated):
`errors.IsPathErrnoTerm.spec` (now concludes `errTreeTerm`, still a hypothesis: item (2)), `fileutil.ReadDir.spec`/
`specAbsent` (error arm `errTreeTerm`), `walpb.Record.Validate.spec` (trees; the target's variable `X` dropped; a
target premise), `decEnv`'s `ErrCRCMismatch` conjunct (trees: **`WalDecEnvSupply`'s meaning changed**). `errIsNot`/
`errIsTerm` stay as they were (the trust boundary `proto.UnmarshalWalRecordE` states them; untouched). Principle
added to the spec skill (`PRINCIPLES.md`, "A premise about an argument is stated in the form the code consumes it").

**`TOpen` now holds:** `decEnv` (`WalDecEnvSupply`), `isErrno`, `isPathErrnoEof`, `isPathErrnoNotExist`,
`isPathErrnoTerm`, `hasPrefix`, `unmarshalWalRecordE`. Gone this session: `resetHs`, `formatBroken`, `errorfErrsNot`,
`errorfErrsTerm`. `Hinit_wp` untouched (B-4).

**(2) Perennial `errors-facts-2`** (worktree `/shared/perennial-errors-facts-2`, off Perennial `lean` `0e10295a1`, NOT
pushed): `94d5c61e5` (= `58e04c5c0`, `newVar` keeps the `errorString` field; `errors` records `ErrUnsupported`) and
`98a9ca318` (= `601b7fb5d`, `Is`/`is` at comparable targets; conflicts in `Base.lean`/`Results.lean` resolved by
dropping the `errors.As` commit's `AsFirst`/`wp_As_first`). The touched modules build (32 modules and 10 package
Links, 2107 jobs). The user pushes it; it then lands by Perennial's workflow (`etc/land.sh`), and the etcd-grove pin
moves to it (issue #9: one pin writer). A local copy on `d648cfe22` (`errors-facts-2-d648`, worktree
`/shared/perennial-errors-facts-2-d648`: `4866869ad`, `a40c07351`, the same two commits) exists only so that
`wal-safe` (still at pin `d648`) can be built against the change: manifest `/shared/tmp/manifest-ef2d.json`.

**`wal-safe-errors`** (worktree `/shared/etcd-grove-walsafe-errors`, off `wal-safe`; local only): see its own
commits and the section after this one (written there).
It is `wal-safe` (through `68e9aadaa7`) plus the adaptations the errors-facts commits need and the two translations
(`0016527b07`, merge, later commits: see `git log wal-safe..wal-safe-errors`): `newVar`'s extra conjunct fixed in
`etc/gen-init.py` (io/fs), `errOk_newVar`, `closeAll`; `Code/syscall.toml` translates `Errno.Is` (and `EACCES`, `EPERM`,
`EEXIST`, `ENOTEMPTY`, `ENOTSUP`, `EOPNOTSUPP`; imports `errors`, `internal/oserror`; the generated initializers follow),
`Code/io/fs.toml` `PathError.Unwrap`; `Proof/syscall/PkgInit.lean` imports the two packages' instances.
**Not done: the proofs** of `errors.{IsErrno, IsPathErrnoEof, IsPathErrnoNotExist, IsPathErrnoTerm}.spec` and
`WalDecEnvSupply`. Plan, all over Perennial's `errors.wp_Is` at the new statement (a client of the old pointer-target
form uses `errors.wp_Is_ptr`; `errIsNot_of_tree`/`errIsTerm_of_tree` in `Proof/errors/ErrTree.lean` call
`errors.wp_Is_tree`, unchanged by the branch):
1. `syscall.Errno.Is`'s spec: at a target `t`, the `switch` compares `t` with `oserror.ErrPermission`, `ErrExist`,
   `ErrNotExist` and `errors.ErrUnsupported` (four `newVar`s: `internal.oserror`'s facts and the branch's
   `errUnsupported_of_init`), and answers `e == ...` only on a match: `false` for `io.EOF`/`io.ErrUnexpectedEOF`
   (`newVar_ne`, different messages), `decide (e = ENOENT)` for `os.ErrNotExist`. An interface `==` of an `Errno`
   target with those pointer errors needs the comparison of different dynamic types (check `GoOp GoEquals` on
   interfaces).
2. The two-node tree of `os.errnoPathErr err e`: the `*PathError` (no `Is`; `Unwrap` returns `errnoErr e` from its
   `Err` cell `↦□`) and the `Errno` leaf (its `Is` by 1; no `Unwrap`). Then `IsPathErrnoTerm` (`errTreeTerm`: the tree at
   any pointer target, `TreeTyped` since the `Errno` is no pointer type), `IsPathErrnoEof` (`errTreeNot`-style: neither
   node is `eof`, the `Errno`'s `Is` false), `IsPathErrnoNotExist` (the walk's answer is the `Errno`'s).
3. `IsErrno` (target an `Errno`, a comparable non-pointer: `comparableErr_uintptr` of the branch).
4. `WalDecEnvSupply`: `decEnv` from the packages' facts: `eof ≠ ueof` and `ErrCRCMismatch ≠ io.EOF` by `newVar_ne`;
   `isEofOk`'s `errors.Is` answers by `errors.wp_Is_leaf`; the `ErrCRCMismatch` trees by `errTreeNot_errorString`/
   `errTreeTerm_errorString` (walpb's package fact must keep the `newVar` form, `walpb/PkgInit.lean`).
Then regenerate the Links (the four and `h_WalDecEnvSupply` gone) and drop the fields from `TOpen`.

**Pitfalls (new).**
- A Perennial worktree builds standalone: copy a nearby build (`/shared/perennial-d648cfe22/.lake/build`) and symlink
  `.lake/packages/{iris,batteries,Qq}` to `/shared/etcd-grove-walsafe/.lake/packages/`.
- A second etcd-grove worktree against another Perennial keeps `wal-safe`'s build intact: copy `.lake/build` (4.2 GB).
- `simp only [h]` (no `at`) rewrites the Iris context too; `simp ... at HIs` names a Lean hypothesis, not an Iris one.
- An Iris triple whose pre is only a points-to needs `(… : IProp GF)` to fix the BI.

# Handoff (branch `wal-safe-errors`, 2026-11-22, session 12 of etcd-grove-03's delegates): the four `errors` specs and `WalDecEnvSupply` proved

Against Perennial `errors-facts-2-d648` (manifest `/shared/tmp/manifest-ef2d.json`), as session 11 planned. No axiom, no
`sorry`, no Perennial change. `TOpen` now holds only `hasPrefix` and `unmarshalWalRecordE` (`Hinit_wp` untouched).

**Open check answered:** Perennial's `go_eq_interface` steps `==` of two interfaces of different dynamic types to `false`
without a step of their own, so `Errno.Is` compares an `Errno` (or any non-`*errorString`) target with the four pointer
errors for free; an `*errorString` target needs its value a pointer (`ErrnoIsTarget`).

**New modules.**
- `Proof/syscall/ErrnoIs.lean` (defs): `wp_Errno_Is`, the translated `Errno.Is` at any `ErrnoIsTarget`, answer
  `ErrnoIsPost` (`e == ENOENT` at internal/oserror's `ErrNotExist`, `false` at none of the four); `errnoIsVars` (the four
  errors and their message cells, distinct by `errors.errorString_ne`), from `isPkgInit syscall` (`errnoIsVars_of_init`;
  `oserror_isInit` is `internal.oserror.isInit_access` without oserror's `Assumptions`, which its section includes but
  never uses).
- `Proof/errors/PathErrnoTree.lean` (defs): `pathErrno_walkTree`, the two-error tree of `os.errnoPathErr` with exact
  relations (`peS`/`peI`/`peU`, the `Errno`'s answer any `Ie` that `ErrnoIsPost` implies); `errno_walkTree`;
  `peS_treeTyped`; `(*PathError).Unwrap` (`wp_pathError_Unwrap`).
- `Proof/errors/{IsErrno,IsPathErrnoTerm,IsPathErrnoEof,IsPathErrnoNotExist}.lean`: the four `wp_proof`s
  (`IsErrno` over `errors.wp_Is` with `comparableErr_uintptr`; `Term` the tree over-approximated; `Eof` over
  `wp_Is_tree`; `NotExist` over `wp_Is` and `isWalk_det` against the walk built by hand).
- `Proof/go_etcd_io/etcd/server/v3/storage/wal/DecEnvSupply.lean`: `wal_decEnvSupply : WalDecEnvSupply`, with `IoE` the
  `*PathError`s; passed by the tester's `Adequacy.lean` (the WAL Link keeps the premise `h_WalDecEnvSupply`, as the
  model's laws).

**Package facts strengthened** (`etc/gen-init.py`, all parts regenerated): `io/fs`'s and `os`'s `ErrNotExist` hold
internal/oserror's `ErrNotExist` (`os.errNotExist_oserror_of_pkgInit`); `walpb`'s `ErrCRCMismatch` keeps its message cell
(`"walpb: crc mismatch"`, so it differs from `io.EOF`).

**`errors-facts-2` adaptation** (broken on this branch before, outside the tester's cone): `errors.wp_New_errorString`'s
post now has the message cell, so the generated initializers name it apart (`⟨#Ec, #E⟩`, `etc/gen-init.py`), and raft's
hand-written `Init.lean` (four trees) likewise; `raft.v3.Init`, `fileutil.InitLinked`, `wal.InitLinked` build again.

**Build:** green (3752 jobs): WAL Link, `durable` and tester Links, tester `Adequacy`, `DecEnvSupply`, `os`/`io.fs`/`walpb`
Inits, `wal.InitLinked` (with `fileutil.InitLinked`, zap's), raft `Init`. The five new results rest on `propext`,
`Classical.choice`, `Quot.sound` only. The other generated initializers the cell split rewrote (bbolt, client, k8s, the
parts' copies, ...) are regenerated, not built. Links regenerated with `LAKE_OPTS=--packages=/shared/tmp/manifest-ef2d.json` (without
it `etc/gen-link.py` finds no Perennial in this worktree and drops ~50 results).

**Not done / noticed.** `etc/copy-part.py --check` reports `RaftNoAx/TrustedCode/go_etcd_io/raft/v3/raftpb.lean`
differing from the main tree's (session 11's `HardState.Reset` model, not copied; pre-existing). `tcb-report --check` not
run (no axiom added or removed).

**Pitfalls (new).**
- Do not run `etc/lean-check.py` in a worktree on a manifest override: its server's Lake ignores `LAKE_OPTS` for the file
  workers, clones the pinned Perennial into `.lake/packages/perennial` and rebuilds imports against it (it left
  `Proof.syscall.PkgInit` built against the wrong `errors`: a kernel error `@errors.isPkgInit_inst GF`). Check a file with
  `lake --packages=<manifest> env lean FILE` instead (imports built through the build slot).
- Lean's `repeat` follows only the first goal; after `wp_if_destruct` use `repeat'`.
- A theorem of a section with `[package_sem : X.Assumptions]` takes it even when unused (`internal.oserror.isInit_access`).
- `wp_start` unfolds the called function; to apply another spec to the call (`errors.wp_Is`), `iintro %Φ pre HΦ`.

# Handoff (branch `wal-safe-errors`, 2026-11-22, session 13 of etcd-grove-03's delegates): on `lean` at Perennial `9c3b81f30`; `hasPrefix` discharged

**State.** `wal-safe` (`0cfda4d071`: `Format`'s `Local` precondition, `time.Now.specLoc`) and `lean` `82950b71a3`
(Perennial pin `9c3b81f30`: perennial#677's errors facts, #685's `stringslite.HasPrefix`) merged. Builds against
`/shared/tmp/manifest-9c3b.json` (Perennial worktree `/shared/perennial-9c3b81f30`). `TOpen` holds only
`unmarshalWalRecordE` (`proto.UnmarshalWalRecordE.spec`, a trust boundary); `Hinit_wp` stays a hypothesis (the
registry work, B-4).

**The merge.**
- Package initializers: lean's form of `wp_New_errorString`'s post (`⟨#_, #E⟩`, the cell dropped) everywhere but
  `walpb`'s `ErrCRCMismatch` (its message cell, this branch's fact) and `internal/poll`'s `ErrFileClosing`
  (`ipersist` kept, the `*errorString` fact); `os`/`io.fs`'s `ErrNotExist` facts are this branch's. All regenerated
  by `etc/gen-init.py` (`PERENNIAL_DIR=/shared/perennial-9c3b81f30`).
- `renameWAL`: this branch's proof (the rename's error branch unreachable under the no-fs-error premise, so no
  `errors.AsType` callee and no `renameWALUnlock`); lean's `errors.AsTypeMatch` (#29) stays, unused by the WAL.
- `errors.IsPathErrnoNotExist.spec` moved on `lean` (kvnet) to `Spec/errors/IsPathErrnoNotExist.lean`; the proof
  imports it there (it imported the WAL's `ExistCallees`, which made KvNet's copy of `durable`'s Link reach the
  WAL's `fileutil`: `copy-part` refused).

**`hasPrefix`.** `filepathlite.IsAbs.wp_proof` takes Perennial's `internal.stringslite.HasPrefix.spec` (the same
statement, with `[internal.stringslite.Assumptions]`); the WAL Link passes Perennial's
`internal.stringslite.wp_HasPrefix`. `Spec/internal/stringslite/HasPrefix.lean` is gone; the tester's `Adequacy`
takes `[internal.stringslite.Assumptions]` (in `tMain_linked`'s section and `etcd_wal_crash_safety_bounded`).

**Side effect on kvnet (another session's part).** `durable`'s Link now links `tryRead` with the proof of
`errors.IsPathErrnoNotExist.spec`, so kvnet's regenerated Link's `wp_RunNode` has no `h_errors_IsPathErrnoNotExist`.
`ReplicaLinked.lean` no longer passes `h_err` (and takes `[errors.Assumptions]`); `kvReplica_wp`/`kvRep_gen` and
kvnet's top level keep the now unused hypothesis, for kvnet's owner to drop (its #677 closure).

**Second lean merge** (`2dce8dc601`: #31 `errors.IsCtxErr` proved, #32's `initFuncsOk` retirements incl. walpb's
protobuf packages): clean; every generator unchanged after it.

**Fixes the full build found** (outside the WAL cone): `SpecPlan/Spec/PkgInit/syscall.lean` regenerated
(`etc/gen-specs-pkginit.py`: syscall now imports errors and oserror, for `Errno.Is`); Net `wire/Pkg.lean`'s and
kvnet `TopPkg.lean`'s `poll_access` read the first two conjuncts of `internal/poll`'s fact, which has a third since
session 10 (`ErrFileClosing` an `*errorString`).

**Gates** (against manifest-9c3b): tier-check, gen-init/gen-link (every mode)/copy-part/gen-raft-tla/gen-specs-pkginit
`--check`, bounds-check, `goose.py --check` of `etcd`, `walfs`, `etcd-wal`, `durable` (with `--perennial
/shared/perennial-9c3b81f30`; `go` is `/usr/local/go/bin`, not on the agent's `PATH`).

**Next.** `etcd-grove#15`: land (the coordinator). Then: crc32 (`crc32-hooks2`, upamanyus) touches `DecDefs`,
`decoder__decodeRecord` and the WAL Link: merge, regenerate the Link. kvnet's owner can drop `h_err`. Left for the
closed theorem: `Hinit_wp` (B-4, the registry), `unmarshalWalRecordE` (trust boundary, the user's).

**Build and trust base.** Full `lake build` against manifest-9c3b green (24912 jobs). `etc/tcb-report.py --check`:
matches `etc/tcb-baseline.txt` (390 axioms, 0 sorries; unchanged: session 11 had already edited the baselines for
`time.Time.Format.wp_proofBroken` and the `HardState.Reset` model, and `HasPrefix` was a hypothesis, not an axiom).
Collections: all 54 match after `wal-tester.txt`'s update (`fmt.ErrorfStrs.wp_proof` no longer reached,
`time.Time.Format.wp_proofBroken` recorded).

# Session (branch `wal-open`, 2026-11-24, etcd-grove-03's delegate; #15): `Hinit_wp` discharged; `unmarshalWalRecordE` blocked

**`Hinit_wp` gone.** `etcd_wal_crash_safety_bounded` no longer takes the initializer's spec. Each generation
(`tGen_wp`) allocates its own registration rights for the WAL's three metric IDs (`prometheus.regKeys_alloc`,
`tRegQsOk`: the IDs as literals `tRegKeys`, decided by the kernel, the same values as the etcd examples' lists),
makes them the generation's `PromRegGS`, turns `ownGoState ∅` into `ownInitializing` (`tOwnInitializing_of_empty`)
and applies the generated `wp_initialize'` (`InitLinked.lean`) with the tester's package table
(`PkgTable.lean`, new: `etc/gen-init.py`'s `wt_inits` now generates it, `WT_PROGRAM`).

**A bug in the statement, fixed** (ledger 2026-11-24): `bootWal`'s bare `initialize'` was raft's (the file opens
`go_etcd_io.raft.v3`), so the program initialized raft only and `Hinit_wp` asked raft's initializer for the
tester's `isPkgInit`: unprovable. `bootWal` now calls the tester's initializer. The theorem gains
`[log.NewModel]` (raft's initializer calls `log.New`; the etcd examples' closed theorems take it too). For review
before landing.

**`unmarshalWalRecordE` not discharged** (stays the only field of `TOpen`): its failure post `errIsNot err t ∗
errIsTerm err` (the error is not `io.EOF`, `errors.Is` answers) does not follow from `proto.UnmarshalPb.spec`,
whose error post is only `err ≠ nil` (the spec's own header and `perennial-changes.md` 2026-11-14 say so: an
extension of the trust boundary, the user's decision). The success and `UFail` parts are
`proto.UnmarshalWalRecord.wp_proof`'s. No file added for it.

**Axioms** of `etcd_wal_crash_safety_bounded`: 18 before, 24 after (all already in the trust base, reached through
the initializer): `prometheus.NewGauge.wp_proof`, `prometheus.NewHistogram.wp_proof`, `strings.ToLower.wp_proof`,
`internal.runtime.sys.opaqueInitsOk`, `runtime.initFuncsOk`, `runtime.opaqueInitsOk`. None removed.

**Merged with lean `b0a063163c`** (Perennial `b3f2fc485`; 2026-11-24): `Adequacy.lean` taken from lean (fs-single-view:
`fsSQ_crash_adequacy`, `tGen` with `osShared`) and the changes above reapplied; generated files regenerated. With
fs-single-view on lean, the closed `etcd_wal_safe` wrapper is unblocked (not started).

# Session (branch `wal-safe-top`, 2026-11-24, etcd-grove-03's delegate): the top-level result `etcd_wal_safe`

**The statement** (`WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/TopLevelRobustness.lean`,
`etcd_wal_safe.spec`): `Robust [(bootWal e.area e.orDir, σ)] [] g (threads := 2 ^ 62 + 1) (bound := 2 ^ 62)`, the
tester alone on one machine that crashes and restarts, under the tester's semantics `tExtsSem` (no I/O, lock or
mapping error; no CRC collision kept by a crash), for every Go semantics and the packages' `Assumptions` (and
`log.NewModel`), given:
- `Hopen : ∀ hG : HeapGS .hasLC fsGF, TOpen (hG := tHeapAt hG lctx)`, the open specs as a named premise (today
  `proto.UnmarshalWalRecordE.spec`, #37 S3); when it is proved the premise goes, a strengthening;
- the bounded theorem's world premises: `FsInit` (`tExtsSem`'s `initLocal` is the default `True`, so `Robust`'s own
  initial-state premise does not give it, unlike kvnet's), the roots `e.R`, the area and oracle directory distinct
  roots, `e.orFile.Ok`, `tWalPathsOk`, the two `PathFits`, `tFirst`.
`Robust`'s `Fresh` gives the bounded theorem's `Hlctx`, `Hpkgs` and `σ.threads = 1`.

**The proof** (`WalTester/Proof/.../TopLevelRobustness.lean`): `Robust.of_single_crashing` over
`etcd_wal_crash_safety_bounded` at `GF := fsGF` (`tAbsPre : AbsDiskGpreS fsGF`, its universal camera), `N := 2 ^ 62`,
`T := n + 2` (`RealCrashThreadsBelow.of_single`: the thread bound follows from the step bound). The osfs pattern
(bboltfs's); kvnet's bridge `robust_of_netFsBoot` is for kvnet's net and fs extensions at the default fs semantics
and re-runs the adequacy, where the tester has its own closed execution theorem.

**Layout and tiers**: `TopLevelDefs.lean` (defs) holds what the statement names, moved unchanged out of
`Adequacy.lean` (linking): `tIo`, `tSQ`, `tQ`, `tFsSem`, `tExtsSem`, `tFsSemOk`, `tHasFs`, `tSat`, `tSatL`, `bootWal`,
`tFirst`, `TOpen`, `tHeapAt`; new `tAbsPre`. `Adequacy.lean` imports it.

**Trust base**: new collection `etc/tcb-collections/wal-safe.txt` (roots: the top-level file);
`wal-tester.txt` narrowed to the tester's Link (its pattern matched the whole directory, which now holds a second
root). `#print axioms etcd_wal_safe`: Lean's 3 and 20 of this repository's, all already in the trust base (those of
`etcd_wal_crash_safety_bounded`); no `sorry`, no axiom added.
