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

Base `origin/wal-int` (`89ef103d5b`). No axiom, no `sorry`, nothing trusted changed, no Go changed, no
existing statement changed.

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
- `TS/member__restart.lean`, `TP/member__restart.lean`: `member.restart.wp_proof` over `restartRead.spec`,
  `checkRestart.spec`, `storeOracle.spec`, `member.resume.spec`.

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
