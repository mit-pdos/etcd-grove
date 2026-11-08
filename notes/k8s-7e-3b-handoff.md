# k8s 7e-3b handoff (2026-11-08, branch `k8s-7e`)

State for the next agent; read `notes/k8s-7e-3b-plan.md` first.

## Done

- (a) the object layer, accepted by 81: commits `fd01648df2`, `c6bb6a70c4` (splitKey as a byte loop,
  per 81; Go tests rerun, all pass).
- (b) started: `KModel.lean` builds on the new records (uncommitted at the time of writing, then
  committed with this file):
  - `Obj` 7 fields, `Input` 27, `Output` 15 in the decidable equalities;
  - `errOutL e k r` builds every no-object output (`Items' = slice.nil`); `objOutL` fills the
    namespace/node/app; `objOfL` (`objOf`); `tooLargeL` (`ETooLarge` = 6);
  - `mcreateL` splits the key (`splitKeyL`), takes node and app; `mdeleteL`/`mupdateL` reject on
    the node (`rejects has reject node`); `updatedL := updGo`; `mgetL` answers `tooLargeL` above
    the store's resource version; `isWriteL` lists the write kinds;
  - `sameObjL` compares the six fields.
- `KSteps`, `ItemList` build unchanged on it.

## Next, in order

1. (done) `MDefs.lean`'s `intoVal` injectivity on the new records.
2. (done) the `decOp`/`Output.Items` design point: option (B).
3. The function specs/proofs of the non-list model functions (`notFound`, `invalidObj`, `objOut`,
   `objOf` (new), `preOk`, `sameObj`, `mcreate` (now calls `splitKey`), `mdelete` (`validateFor(has,
   reject)`), `mupdate`, `mget` (`ETooLarge`), `mstep` (dispatches `KList`), `isWrite`).
4. The list functions of the plan's item 4, then `mlist` with the out-of-driver callees as
   hypotheses (81's decision 2).

## Resolved: option (B) (81, 2026-11-08), commit `90b6252aa5`

`Output.Items` is now `encodeItems(items)` (a string: per item `rvBytes(rv) ++ rvBytes(len e) ++ e`,
`e = encodeObj(item)`), so `Output` is a plain value and `decOp`/`ioOk` stay as they were. Lean:
`encItemsL`, `encItemsL_inj` (`Codec.lean`, on `itemOk` objects: fitting fields, no annotation,
encoding below `2^63`). 7f's codec changes are folded in (`codec.Decode` with no target;
`Obj.Annotated`, never encoded: `DObj.toObj` sets it `false`, `decodeD` yields `false`). `MDefs`
builds. Go: the package passes; `TestPartitionScale` with `K8SETCD3_SCALE`: Ok in 34s, heap 1.4 GiB,
7.9s in Step/Equal, at most 10 configurations (the commit before, same test: 75s, 8.6 GiB, 50s,
96 configurations; runs are random, so this shows no blow-up, not a speedup).

## The design point as it was (for the record)

`Output.Items` is a `[]Obj` slice, so `Output` is no longer a plain value: `decOp`
(`MDefs.lean`) is a pure function of porcupine's `OpV`, and sees only the slice's pointer, while
the model must compare the items. 81 accepted "the I/O fact carries the items' read-only
points-to"; but a points-to in `ioOk` does not let the pure `decOp` read the contents. Options:
- (A) Ghost: a persistent ghost map from slices to their contents, `ioOk` ties `y.Items ↦*□ its`
  to it, `decOp` reads the map's (pure) agreement through a parameter of `k8setcd3S`. Lean-only, but
  the parameter must be fixed before the run (allocation order), which is awkward.
- (B) Go: `Output` keeps the list as a value (e.g. `Items string`, the items' length-prefixed
  encoding through the driver's codec, built by `listOut`; the model builds the same bytes). Output
  stays plain, `decOp`/`ioOk` unchanged; only the state's `rep` must own the history chain.
  Costs a Go change (driver, tests, re-translation) and an encoding lemma (injective on fitting
  objects, from `decodeD_encode`).
- (C) Keep `Items []Obj` and let the model compare outputs ignoring `Items'` but carry the list in
  a separate ghost: unsound for lists (the items would be unchecked).

Recommendation: (B).
