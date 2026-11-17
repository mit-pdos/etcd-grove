# W4c U5 (tester), the member operations (branch `wal-c-ops`, 2026-11-14)

Base `origin/wal-int` (`87ead66a41`). No axiom, no `sorry`, nothing trusted or generated changed, no Go
changed. `TP/` = `LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`, `TS/` =
`LinuxFs/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`. Every module below passes `lake build`.

## Proved

- **`member.opEntries`** (`TS/member__opEntries.lean`): from `memSaveRes` and the raft-like fields, either nothing
  (`last ≥ 2^62`) or one to four entries at the term `t` saved (`memSavePost` at `(t, vo, cm')` and the entries),
  the entries `tEntWf` with term `t`, `terms` holding only `t` or old values (`tTermsFrom t M M'`). Premises:
  `tMemOk`, `tMemHs`, `t < 2^63`, room `tOrRoom o 184`. Over `rnd.choose/next`, `member.size/hs/save`.
- **`member.opResend`** (`TS/member__opResend.lean`): nothing, or one to three entries of the first candidate's
  history (`walFold` of `cands[0].h ++ since`) at consecutive indices from `last + 1` re-sent, the term raised to
  theirs, `tMemFields t M → tMemFields t' M'`. Premises: `tMemOk`, `tMemHs`, **`tCheckWf o`** (the entries' `tEntWf`
  comes from every candidate's history being well formed), room `tOrRoom o 152`. Over `copyOps`, `walFold`,
  `member.hs/save`.
- **`member.opRecvSnap`** (`TS/member__opRecvSnap.lean`), stated over the running member `memLive` (below):
  `{memLive o ∗ tOrRoom o 176} … {b; if b then ∃ o', memLive o' ∗ |enc o'| ≤ |enc o| + 176 else True}`. Over
  `rnd.choose/next`, `member.size/hs/save/sync` and **`member.saveSnap.spec`, stated here, not proved** (below).

## New non-spec modules

- **`TP/OrLen.lean`, the size lemma**: `tEncodeOracle` writes every number in 8 bytes, so its length depends on
  the oracle's shape only. `tEncodeOracle_saveO1` (a save of `k` entries costs `56 + 32k` bytes, any hard state),
  `_synced`, `_lastHS` (cost nothing), `tOrSmall_saveO1_iff` (the hard state's values do not matter),
  `tOrRoom o n` (room for `n` more bytes) and `tOrRoom_save` (room gives `save`'s two size premises for every
  hard state: what `opTerm`/`opCommit`'s `∀ h` premise needs, `MemberInv.tOrRoom_saveNil` from `tOrRoom o 56`),
  `tEncodeOracle_saveO_le`, `tOrRoom_saveO`; `tOrSmall_hist_lt` (an oracle within 1 GiB has every candidate
  history below `2^62`: `tCheckWf`'s bound), `tCheckWf_saveO`.
- **`TP/SnapPure.lean`**: `tSnapOp`, `tSnapO1`, `tSnapO` (`saveSnap` on the oracle: append, mark to the end),
  `tEncodeOracle_snapO1` (56 bytes), `tOrRoom_snap(O)`, `tCheckWf_synced`, `tCheckWf_snapO`.
- **`TP/MemberInv.lean`, the member's raft-like fields' invariant**: `tMemFields t M` = the term and every term
  `terms` records below `2^63` (`tEntWf`/`tOpWf` of what the operations save; `opOwnSnap`'s `terms[a]`). Nothing
  else is needed: every index computation is guarded by `last < maxIndex` or an explicit comparison, and `save`
  asks nothing of the entries' indices against the history. `tTermsFrom`, `tTermsOk_insert/_delete`,
  `tNextTerm_lt` (`opTerm` keeps it). `memSavePers` (memSaveRes's persistent half) and `memSaveRes_pers`;
  **`memOpPost o'`** (an operation's post at the oracle it leaves; `memSavePost = memOpPost (tSaveO …)`,
  `memSavePost_op`), **`memSaveRes_postOp`/`memSaveRes_post`** (a successful operation gives `memSaveRes` back
  at the new oracle, same candidate). **`memLive W e γ m qc o`**: the running member between operations
  (`memSaveRes`, the six raft-like fields with `tMemFields`, `r ↦ rv`, `walPurgeW` for `close`, `tMemOk`,
  `tMemHs`, `tCheckWf`), the form `step`'s spec should take.

## Statement changes

- **`member.save.spec`** (and `MemberRep`'s `memSaveRes`, `memSavePost`): the precondition gains `walLenLb w dir
  |d.H|`, the true arm `walLenLb w dir |d'.H|` (ledger 2026-11-14): `sync` takes the handle's written length
  of the current state, so nothing could call `sync` after a `save`. `WAL.Save.spec` gives it; the proof dropped
  it. `save`, `opTerm`, `opCommit` re-proved (their patterns gain one hypothesis). **Merge note** for
  `wal-c-tester`/`wal-c-tcrash`: `memSaveRes` has 17 conjuncts now (last `walLenLb … d.H.length`), `memSavePost`'s
  true arm ends with `walLenLb … d'.H.length`; whoever builds a `memSaveRes` at `restart`/`Boot` supplies the
  length of the open handle (`Open`+`ReadAll`, `Create`).

## New hypotheses

- **`member.saveSnap.spec`** (`TS/member__saveSnap.lean`), stated, no proof file: `{memSaveRes …} saveSnap(idx,
  term) {b; memOpPost (tSnapO o idx term) b}`, premises `tMemOk`, `tMemHs`, `idx, term < 2^63`, `tOrSmall (tSnapO1
  …)`. Its proof is blocked on **U1 mismatch 3** (the `ConfState` encoding, a user decision): skipped as asked.
  `opRecvSnap` takes it as a callee hypothesis, so `opRecvSnap` links only once it is proved.

## Not done

- **`saveSnap`, `opOwnSnap`**: skipped (U1 mismatch 3; `opOwnSnap` also U6, `purgeRound`).
- **`member.step`**: not stated. Its callees include `opOwnSnap` (blocked), `close` then `restart` (`restart`'s
  spec is `wal-c-tester`'s), and its size premise cannot be closed: `restart` replaces the oracle by
  `checkRestart`'s (`tAddCand` adds candidates with whole histories), whose length is not bounded by the old one
  plus a constant, so no `tOrRoom` survives a restart. That is **U1 mismatch 2** (the oracle's size against
  `durable.Write`'s 1 GiB; the tester's Go does not stop): a user decision. Once decided, the intended form is
  `{memLive o ∗ room} step {b; if b then ∃ o', memLive o' ∗ room' else True}`, each arm from the operation's spec
  (`opTerm`/`opCommit`/`opEntries`/`opResend` posts to `memLive` by `memSaveRes_post` and `tMemFields`;
  `opRecvSnap` already in that form).
- **For `restart`'s author: establishing `memLive` after a restart** needs `tMemFields (tResumeTerm c)
  (tResumeTerms c)`: the read hard state's term and the read entries' terms below `2^63`. The entries' terms
  follow from `tHistWf` (`tEntWf`), but **no fact bounds a hard state's term** (`tOpWf` constrains no hard state).
  Recommended: `tOpWf` of a save also bounds `hs.term' < 2^63` (then `save.spec` takes `h.term' < 2^63`, which every
  caller has from `tMemFields`), so the read's hard state, the WAL's last, is bounded. Not made (a change to
  `Defs.lean`, shared with the restart/crash branches). Also needed there: `walLenLb` and `walPurgeW` of the handle,
  `tCheckWf` of `checkRestart`'s oracle.

## Decisions for the user

None new. U1 mismatches 2 (the oracle's size; blocks `step`) and 3 (the `ConfState` encoding; blocks `saveSnap`,
hence `opRecvSnap`'s link and `opOwnSnap`) and U6 still stand.
