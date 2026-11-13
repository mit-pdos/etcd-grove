# mvccfull F1 Prove: the streams (2026-11-10)

Stage F1, Prove (`notes/mvccfull-proof-plan.md`). One agent with three forks (A: leaves; B: the
epochs; C: `act`, `cancel`), worktree `worktree-mvcc-full-tester`.

## Proved (no `sorry` of their own)

- `Streams.lean`'s laws: `recv_facts` (over `excl.law`, new hypothesis); `maxK_attained` dropped
  (`StreamLemmas.maxK_attained'`).
- `stream.receive` (takes `excl.law`: link line and `Link.lean` regenerated), `stream.watch`,
  `stream.cancel`, `stream.act`, `stream.pick`, `stream.expect`, `watcher.matches`, `pick.wp_proofW`,
  `runner.endEpoch`.
- `runner.startEpoch`: proved over `EpochLemmas.inc_watchable` (`sorry`, below).
- Lemma modules: `RecvLemmas` (the watch guarantee's clauses as the tester's expected changes, the
  floating window, `covered_none`, `float_anchor`), `WatchLemmas` (`register_au'`, `regOk'_register`,
  `cmpLo_acc_lt`), `RegLemmas` (cancel's mark and update), `EpochLemmas` (stream allocation,
  `Close`, the closed stream's `Watch`/`Cancel`), `LeafLemmas`.

## Changes to the stream vocabulary (`Streams.lean`, internal; no Spec statement changed)

1. `streamInv`: `⌜regOk' S W C⌝ ∨ ⌜S.closed = true⌝ ∗ ∃ rs, wsRecv σs.ws rs`. `endEpoch`'s
   `Cancel(0)` on the closed stream commits `S.cancel 0`, which may make an unmarked watcher not live;
   the stopped receiver's `wsRecv` is deposited instead. The receiver refutes the branch by
   `excl.law`, the registrar by its half of the closed flag at `false`.
2. `regOk'` gains a third conjunct: every id of the cancel record is registered (so a fresh id is in
   no cancel; `watch` needs it).
3. `smuBody`'s registry half is `regLock`: the auth half with every entry's fragment, persistent once
   marked (`cancel` marks with `ghost_map_update` under `s.mu` and keeps a persistent copy as the
   witness its `Cancel`'s commit needs after the unlock).

## Blocker left: `inc_watchable` (`EpochLemmas.lean`, `sorry`)

`startEpoch`'s `m.kv.NewWatchStream()` needs `NewWatchStream`'s contract, which only `isWatchableKV`
has, and `shapes.law` gives it only of `*watchableStore`. `isInc` records `isMvcc kv ι.kv` (sealed:
possibly a plain store). Proposed fix (`Members.lean`, shared; the writer's `inc_alloc` must provide
it, from `mvcc.api.New.spec`'s post `RET #(interface.mkOk PW #ws)`): `isInc` gains
`⌜∃ s : Loc, kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #s⌝`. Not additive, so
not done here.

## Other

- Bounds gate: the epoch stocks (`runner__{start,end}Epoch`, `WriterShares`) are the tester's own
  (`etc/bounds-allow.txt`); `etc/bounds-check.py --check` ok.
- Cross-package unfolds: mvcc's `filtersImpl`, `filterSpec`, `evIs`, `kvPtrFixed` (the API's
  vocabulary of `Watch`'s filters and events; `watch` proves its filter closures' `filterSpec`,
  `receive` reads the events as mvccrand's did).
- Stub hypothesis `wp_pick : pick.spec` inside `stream.*` proofs resolves to `stream.pick.spec`
  (namespace); `act` and `watch` now name `EtcdGrove.mvccfull.pick.spec`.
- Tooling: `etc/lean-check.py`'s server is shared by the worktree's agents and reported "0 errors"
  on files with errors; `LEAN_NUM_THREADS=6 lake env lean FILE` was reliable. Long proofs need
  `set_option maxHeartbeats` (the limit is per declaration).
