# mvccfull F1, Prove: the readers (2026-11-10)

Progress of the readers' part of mvccfull F1's Prove stage (`notes/mvccfull-proof-plan.md`), and of
the pure leaves, history and pending methods.

## Proved

- `Readers.lean`'s laws, all: `memberN_mask`, `memberInv_live` (and `ret_live_false`), the five bound
  accessors (`revLo_acc`, `cmpLo_acc`, `revHi_acc`, `nrevHi_acc`, `cmpHi_acc`: the incarnation's
  invariant opened under its later, the contents' `mvccState` put back without being stripped, so no
  persistence law is needed), `reader_au` (as mvccrand's, through `memberInv_live`), `rdStock_split`
  (`ReplicateLemmas`: fractional and additive resources over `List.replicate`).
  - `rdStock_split` gained two premises, `mvcc.api.persistent.law` (the handles `isInc`, copied into
    each reader's part, are persistent only through it) and `mvcc.api.mvccReaders_split.law` (the `n`
    reader tokens split): its statement was not provable without them. Its only users are mine
    (`startReaders`).
- `inBounds` (`AtomicLoad`: `Int64.Load` with the fraction inside the update, which `inBounds.spec`'s
  accessor needs; `notes/perennial-changes.md`).
- `runner.checkStoreRange`, `runner.readOne` (per member, `readOne_at`), `runner.startReaders`,
  `runner.stopReaders`; `ReadLemmas` (the result struct of a live read, `outcome_acc`; `check_ok`,
  `logOk_read`, `statesP_statesAt`, `end_read`).
  - `startReaders.wp_proof` takes the persistence and reader-split laws and `time.Sleep`'s spec
    (`etc/link-lean-first-mvccfull.txt`, `Link.lean` regenerated).
- The leaves (a helper agent): `checkRangeAt` (its `wp_proof` takes `errVars.law`), the history's
  `snapshot`/`appendRev`/`changesAt`/`addComp`, `pending.put`, `check`, `checkKV`, `copyState`,
  `inRange`, `itoa`, `noCluster.Version`, `MainConfig`, `choose`, `memberPath`, `buildPath`,
  `normalize`, `hashing`, `walkKeys`, `FilePaths`.

## Not proved

- **`pending.del`: its frozen spec is false.** The post's count and changes are `P.delKeys ks …`, a
  filter over `ks` (`matchKeys`), which counts a repeated key twice; the Go loop deletes it once (on
  its second visit the key is gone). With `ks = [k, k]`, `k` present and in range, Go returns 1, the
  spec 2. The spec needs `ks.Nodup` (or `ks.Pairwise go.GoStringLt`, which `runnerKeys` gives every
  caller). A defect of our spec, not of the Go code. Left `sorry`, for the user.

## Bounds

`etc/bounds-check.py`'s `stock` matches of the readers' epoch (`Readers`, `startReaders`) are listed
in `etc/bounds-allow.txt` as their owner's: the stock is the tester's configuration count, lent by
the writer and returned whole by the wait group. The three left in mvccfull are the streams'
(`epochTok`).

## Tooling

In this worktree, shared by four agents, `etc/lean-check.py` returned stale results and false
"0 errors" (no `sorry` warnings either) on files being edited; `lake env lean FILE` (15-60 s a file)
was used as the check instead.
