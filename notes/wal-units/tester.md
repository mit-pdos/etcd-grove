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
