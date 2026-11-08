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

1. `MDefs.lean`: the `intoVal` injectivity lemmas need the new fields (`Obj`: Namespace, Node, App;
   `Input`: Node, App, HasReject, ListKey, Recursive, Match, Field, SelNS/SelName/SelNode/SelApp,
   Limit; `Output`: Namespace, Node, App, Items, ListRV, Continue, HasRemaining, Remaining). Mechanical.
2. **The open design point below** (`decOp` and `Output.Items`), before `k8setcd3S` changes.
3. The function specs/proofs of the non-list model functions (`notFound`, `invalidObj`, `objOut`,
   `objOf` (new), `preOk`, `sameObj`, `mcreate` (now calls `splitKey`), `mdelete` (`validateFor(has,
   reject)`), `mupdate`, `mget` (`ETooLarge`), `mstep` (dispatches `KList`), `isWrite`).
4. The list functions of the plan's item 4, then `mlist` with the out-of-driver callees as
   hypotheses (81's decision 2).

## Open design point (for 81)

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
