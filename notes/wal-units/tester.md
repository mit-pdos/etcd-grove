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
