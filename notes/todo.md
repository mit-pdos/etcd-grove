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

- **`wp__new_cap` quantifies over an unused `V`** (added 2026-09-29).
  `new/golang/theory/slice.v:905` states it inside `Section wps` after
  `Context [V] `[!ZeroVal V] `[!TypedPointsto V]`, although the lemma
  never mentions `V`. Inside the section that is harmless (the one use,
  `wp_slice_append`, has `V` fixed); outside it the lemma takes an extra
  type and two instances that nothing determines, and `wp_apply` leaves them
  as shelved goals ("Expected a single focused goal but 3 goals are
  focused" on the next tactic). Workaround:
  `wp_apply (wp__new_cap (V:=V))` in
  `new/proof/go_etcd_io/raft/election_proof/slice_persistent.v`. Fix: move
  the lemma above that `Context` (it needs only `sem_fn`/`pre_sem`), then
  drop the `(V:=V)`. Deferred because touching `slice.v` rebuilds all of
  `new/`.

- **`wp_slice_append_persistent` belongs in `slice.v`** (added 2026-09-29).
  `append` onto a destination whose elements are held `↦*□`, with the
  capacity slack owned. It lives in
  `new/proof/go_etcd_io/raft/election_proof/slice_persistent.v` because
  its one user is the raft log (`truncateAndAppend`). Move it next to
  `wp_slice_append` when a second user appears, or together with the
  `wp__new_cap` fix above (same rebuild).

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
