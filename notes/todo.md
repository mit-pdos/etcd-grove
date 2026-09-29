# Deferred work

Things that should be done at some point but are not blocking anything now:
workarounds that ought to be replaced by a proper fix, generalisations that
wait for a second user, known gaps outside the current scope. One entry per
item: what, where, why it was deferred, and what the fix is. Delete an entry
when it is done (and say so in `journal.md`); unlike the journal this file
is kept current.

Not for defects that *block* a proof — those go in [../bugs/](../bugs/README.md).
Not for the next step of the work in flight — that is `STATUS.md`.

## Framework (`new/golang/`)

- **The `done` override skips contradictions on `WP` goals** (added
  2026-09-29). `proofmode.v:330` sends a goal that is or contains a `WP`
  to `wp_done_wp_goal` (`fast_done`/`trivial` only), so a branch dead by a
  contradictory hypothesis needs `by exfalso` (gotchas.md; 13 sites fixed
  2026-09-29). The override exists because ssreflect's `//` runs `done` on
  the main `WP` goal too (`rewrite lemma //`, 154 uses in
  `election_proof/`), which failed at 7-38 s per use with the program
  visible. Considered and left as-is for now: (a) hide the body and run the
  full `wp_done_core` there (stdpp semantics back, ~1 s per failing `//`
  per the 2026-09-17 table, unmeasured on today's tree); (b) drop the
  override and write `rewrite …; last …` instead of `//` (a missed site
  is a silent slowdown, not an error). Revisit if the trap bites again.

## Raft proof

- **Remove `nstate.log`** (added 2026-09-29). No spec mentions it. It
  only makes `wp_raft_load_raftLog` (returns `#s.(nstate.log)`) and the
  log accessors `own_raft_phys_log_at`/`_same` (hand out
  `own_raftLog s.(nstate.log) …`) agree on the pointer. It was added
  2026-09-22 so a caller holding the log *on loan* could tell after a call
  that it still held the struct's log, and loans are gone. Fix: have the
  log accessor hand out the field points-to `r.[raft.raft.t, "raftLog"] ↦ l`
  with `own_raftLog l s.(nstate.logst)` and a wand back, as
  `own_raft_phys_tracker` does for `trk`. Then delete `wp_raft_load_raftLog`
  and the `Hlogp` conjunct, and rework its 31 uses in 14 files: accessor
  first, then the load by `wp_auto`, then the wand. Also
  `proof_raft__loadState.v:56`, and `nstate.mk … l …` in `proof_newRaft.v`.
  Deferred because it is physical state and harmless.

- **`nextUnstableEnts` returns an uncapped slice** (noted 2026-09-29).
  `log_unstable.go:101` returns `u.entries[inProgress:]` without a
  capacity limit, unlike `unstable.slice`. An application that appends to
  it could write into `u.entries`' slack, which raft may later append into
  too. Existing elements are never overwritten, so `own_unstable`'s
  read-only entries are unaffected, but a spec of `Ready` can hand the
  application only the elements read-only, never the slack. Not on the
  election path; matters when `Ready`/`Advance` are specified.
