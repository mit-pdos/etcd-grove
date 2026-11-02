# `store.Restore` in either mode (2026-11-02, M2's item 15)

`store.Restore` (and `watchableStore.Restore`, which collects its pre under the watchable store's
lock) installs a snapshot's backend. Its spec excluded compaction mode: `cm = false` for both
backends, the store never compacted (`crevFrozen`), the whole `Key` bucket of the restored log, no
compaction record. A three-member cluster with compaction on needs a lagging follower to install
a snapshot while compaction runs.

## The first version (the Draft `store.Restore.specM`)

The mode survives the install (`d'.cm = d.cm` in place of the two `cm = false`); everything that
differs by the mode is a predicate indexed by it, `True` or the old resource off:

- what `Restore` takes of the store's right, `restoreRightM s γ c` (off, the closer and
  `crevFrozen` at `c = -1`; on, the compaction right at the store's revision `c`);
- the image at its compaction records `r`, `restoreImageM d' γb' L' r` (off, the whole bucket and no
  record; on, the job's cut of `L'` at `r.crev` with the records' write right), with `c ≤ r.crev`;
- the backend's contract and clean read at the records, the new job's budgets, the unset hook lent
  when the records resume a compaction;
- the post: `storeCloserM … r.crev` (the right at the restored revision), the old job's budgets,
  the old readers less the job's;
- a pure premise `restoreBoundM d' L'` (on, the restored log's changes below the receipts' bound).

## Changes before approval

1. **The receipt a persistent premise** (B2 by sealed logs, the user's decision: no premise of
   `NewServer`, every installed log is some member's sealed log): the pure bound became
   `restoreRcptM d' L'` (on, `⧖ (logCh L')`), which the proof keeps in the restored writer's handle.
2. **The writer's relation thin** (the user's Q1: `bucketViewL`, mvcc-internal, over a backend
   axiom that would open the view wide): no change to the text, a change to what the proof rests on.
3. **Amendment 1: the compaction permit of both records** (`crevPermAt γ r.finRev ∗
   crevPermAt γ r.crev`): C3's permit law landed after the draft and keeps, in `s.mu`'s resource, a
   permit of the compaction revision, which every writer of it carries. `restore()` writes it twice
   (to the finished record, then, resuming, `compactLockfree` to the scheduled one), so the spec
   takes the permit of both. Off, both are `-1`, permitted by `crevPermAt_none`.

## The approved spec

`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__Restore.lean` (the Draft with changes 1 and 3,
`isPkgInit` first), and the same for `watchableStore__Restore.lean`. The old text stays only for
callers that have not moved (`watchableStore.Restore.specOff`, with `specOff_of_spec`).

## The caller's spec: `applySnapshot.specSnap` (stage B2, 2026-11-02)

The server's snapshot install, which took `d.cm = false`, was switched to the same mode-indexed
form: the image's records `r` with `keyImageM d.cm L r D` (off: today's `keyImage`, `r` empty),
the receipt `restoreRcptM d L` and the permits `crevPermAt E.γ r.finRev ∗ crevPermAt E.γ r.crev`
as premises (the user's "Add as premises": like `hkI`, facts the caller holds about the image), the
closer by the mode (`srvKVCloserW`), and a post with `d'.cm = d.cm`, `x'.crev = r.crev`. Against
candidate 1's text, three changes the user approved after the fact ("go ahead"):

1. **An existing name, not a new parameter**: the store's compaction revision is the apply thread's
   `x.crev` (already tied to the store by `srvEnvOk`), not a fresh `c`.
2. **The landed vocabulary over the draft's**: `srvKVCloserW` (landed meanwhile) for the draft's
   `srvKVCloserM s E c`.
3. **A mode-conditional premise**: `hcc : d.cm = true → x.crev ≤ r.crev`, not `x.crev ≤ r.crev`:
   off it follows from the mode-off resources (`x.crev = -1`, `r` empty), so the condition only
   weakens what callers must show.

## What it shows

- One spec for both modes, its mode-dependent pieces as predicates indexed by the mode whose off
  value is the old resource (and an off law for each), keeps one proof obligation and one statement;
  the callers that stay off get the old text by a lemma, not a second spec.
- When a law about a field lands (the permit), every writer of the field carries its premise,
  restores included: check each write a function makes, not only the obvious one.
- A caller's spec switched after its callee keeps the same shape (mode-indexed pieces, facts about
  the input as premises), names state by what already ties it (`x.crev`, not a new `c`), and states a
  premise only in the mode that needs it.
